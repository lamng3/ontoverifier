"""Run Lean. This is the only place a claim can become accepted.

Lean's kernel checks each theorem, and `#print axioms` must show nothing beyond the
three standard ones: in particular no `sorryAx`, and no `Lean.ofReduceBool`, which
would mean trusting compiled code. Without Lean every finding stays `not_run`.

Theorems are checked once. A theorem's text says everything it rests on, so the same
text under the same toolchain needs no second run, and a new version of an ontology
only pays for what actually changed.
"""

import hashlib
import json
import os
import re
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(os.environ.get("ONTOVERIFIER_ROOT", Path(__file__).resolve().parents[2]))
ELAN = Path.home() / ".elan" / "bin"
WORKERS = max(1, min(6, (os.cpu_count() or 2) - 2))
CACHE = Path(os.environ.get("ONTOVERIFIER_CACHE",
                            Path.home() / ".cache" / "ontoverifier" / "kernel.json"))


@dataclass
class Checked:
    kernel: str  # accepted, rejected, or not_run
    detail: str = ""
    cached: bool = False


def _env():
    return {**os.environ, "PATH": f"{ELAN}{os.pathsep}{os.environ.get('PATH', '')}"}


def available():
    return shutil.which("lean", path=_env()["PATH"]) is not None


def _toolchain():
    source = ROOT / "OntoVerifier" / "Model.lean"
    model = source.read_bytes() if source.exists() else b""
    toolchain = (ROOT / "lean-toolchain").read_bytes() if (ROOT / "lean-toolchain").exists() else b""
    return hashlib.sha256(model + toolchain).hexdigest()


def _ensure_built():
    built = ROOT / ".lake" / "build" / "lib" / "lean" / "OntoVerifier" / "Model.olean"
    source = ROOT / "OntoVerifier" / "Model.lean"
    if not built.exists() or built.stat().st_mtime < source.stat().st_mtime:
        subprocess.run(["lake", "build"], cwd=ROOT, env=_env(), capture_output=True, timeout=900)


class Cache:
    def __init__(self, path=CACHE):
        self.path = Path(path) if path else None
        self.known = set()
        if self.path and self.path.exists():
            try:
                self.known = set(json.loads(self.path.read_text()))
            except ValueError:
                self.known = set()

    def save(self):
        if self.path:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.write_text(json.dumps(sorted(self.known)))


class Batch:
    """Theorems that share a prelude, checked in one run of Lean."""

    def __init__(self, path, prelude="", cache=None):
        self.path = Path(path)
        self.prelude = prelude
        self.cache = cache
        self.theorems = {}

    def add(self, name, text):
        self.theorems[name] = text

    def _key(self, text):
        return hashlib.sha256(f"{_toolchain()}\0{self.prelude}\0{text}".encode()).hexdigest()

    def run(self, timeout=1800):
        """Write every theorem to the batch's file, and check the ones not seen before."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(self.prelude + "\n" + "\n".join(self.theorems.values()))
        if not self.theorems:
            return {}
        if not available():
            return {n: Checked("not_run", "lean is not installed") for n in self.theorems}
        results, pending = {}, {}
        for name, text in self.theorems.items():
            if self.cache and self._key(text) in self.cache.known:
                results[name] = Checked("accepted", "seen before", cached=True)
            else:
                pending[name] = text
        if pending:
            results.update(self._check_all(pending, timeout))
        if self.cache:
            for name, text in pending.items():
                if results[name].kernel == "accepted":
                    self.cache.known.add(self._key(text))
            self.cache.save()
        return results

    def _check_all(self, pending, timeout):
        """Share the theorems out among several runs of Lean."""
        _ensure_built()
        names = list(pending)
        parts = [names[i::WORKERS] for i in range(WORKERS) if names[i::WORKERS]]
        with ThreadPoolExecutor(len(parts)) as pool:
            runs = pool.map(lambda part: self._check(
                {n: pending[n] for n in part[1]}, timeout, part[0]), enumerate(parts))
        return {name: checked for found in runs for name, checked in found.items()}

    def _check(self, pending, timeout, part=0):
        lines = self.prelude.count("\n") + 1
        starts, body = [], [self.prelude]
        for name, text in pending.items():
            starts.append((lines + 1, name))
            block = f"{text}\n#print axioms {name}\n"
            body.append(block)
            lines += block.count("\n") + 1
        probe = self.path.with_suffix(f".check{part}.lean")
        probe.write_text("\n".join(body))
        try:
            run = subprocess.run(["lake", "env", "lean", "--json", str(probe.resolve())], cwd=ROOT,
                                 env=_env(), capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return {n: Checked("rejected", "lean timed out") for n in pending}
        finally:
            probe.unlink(missing_ok=True)
        errors, axioms = {}, {}
        for line in run.stdout.splitlines():
            try:
                message = json.loads(line)
            except ValueError:
                continue
            text = message.get("data", "")
            if message.get("severity") == "error":
                errors.setdefault(_owner(starts, message["pos"]["line"]), text)
            match = re.match(r"'([^']+)' (depends on axioms: \[(.*?)\]|does not depend on any axioms)",
                             text, flags=re.S)
            if match:
                used = {a.strip() for a in (match.group(3) or "").split(",") if a.strip()}
                axioms[match.group(1)] = used
        results = {}
        for name in pending:
            if name in errors or None in errors:
                results[name] = Checked("rejected", (errors.get(name) or errors[None])[:2000])
            elif name not in axioms:
                results[name] = Checked("rejected", (run.stderr or "no audit from lean")[:2000])
            elif axioms[name] - ALLOWED:
                results[name] = Checked("rejected", f"rests on {sorted(axioms[name] - ALLOWED)}")
            else:
                results[name] = Checked("accepted", f"axioms: {sorted(axioms[name]) or 'none'}")
        return results


def _owner(starts, line):
    owner = None
    for start, name in starts:
        if start <= line:
            owner = name
        else:
            break
    return owner
