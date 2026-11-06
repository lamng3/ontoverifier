"""Do an ontology's words agree with its axioms?

A class often says what it means twice: in English, in a definition, and in logic, in
its axioms. Nothing keeps the two together. Here a model reads the definition and writes
the claims it makes, and the Verifier judges each claim against the axioms:

    agrees       the axioms prove the claim
    contradicts  with the claim added, the class could have no instance
    says more    a model of the axioms where the claim fails: the definition says
                 something the axioms do not

What this does not do is verify the English. The kernel checks the logic of a claim, and
nothing checks that the claim is what the definition meant, so each finding shows both,
for a person to read. A wrong translation looks exactly like a real disagreement.

The model never writes Lean. It picks terms by handle from a short list and a claim from
a fixed set of shapes, and the Lean is written from that here. A Lean file can run code
when it compiles, so model output must never reach the compiler as text.
"""

import hashlib
import json
import random
import re
import shlex
import subprocess
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path

from ontoverifier.axioms import Axiom
from ontoverifier.search import Budget, Search
from ontoverifier.verifier import Verifier

SYSTEM = (
    "You read one definition from an ontology and write down what it states about every "
    "instance of the class, using only the given terms. Return only JSON."
)
_TEMPLATE = """Class: T0 = {subject}
Definition: {definition}

Classes you may use:
{classes}

Properties you may use:
{properties}

Each claim has one of these shapes:
{{"kind": "sub", "super": "T1"}}                    every T0 is a T1
{{"kind": "some", "prop": "P1", "filler": "T2"}}    every T0 has a P1 that is a T2
{{"kind": "all", "prop": "P1", "filler": "T2"}}     every P1 of a T0 is a T2
{{"kind": "disjoint", "other": "T2"}}               nothing is both a T0 and a T2

Rules:
- Write only what the definition states about every instance. Leave out what is merely
  typical, what is an example, and what you know from elsewhere.
- "sub" needs the definition to say a T0 IS a T1. A term that is only mentioned is not a
  superclass: "a patch of ground above a plain" does not make it a plain.
- A term must mean what the definition means, not just share a word with it. If the only
  listed term is narrower, broader or merely related, leave the claim out.
- When unsure, leave the claim out. Few correct claims are better than many doubtful ones.
- Claims may be empty. Do not repeat the class as its own superclass.

Return {{"claims": [...]}}."""
_STOP = set("that this with from which have been were their there other such into than "
            "class refers used when where while also some each more most both only very "
            "being between within".split())
VERDICTS = {"entailed": "agrees", "contradiction": "contradicts", "refuted": "says more",
            "unknown": "unknown"}


class Ollama:
    def __init__(self, model, host="http://localhost:11434", timeout=600):
        self.name, self.host, self.timeout = f"ollama:{model}", host, timeout
        self.model = model

    def complete(self, system, prompt):
        body = {"model": self.model, "stream": False, "format": "json",
                "options": {"temperature": 0},
                "messages": [{"role": "system", "content": system},
                             {"role": "user", "content": prompt}]}
        request = urllib.request.Request(f"{self.host}/api/chat", json.dumps(body).encode(),
                                         {"Content-Type": "application/json"})
        with urllib.request.urlopen(request, timeout=self.timeout) as response:
            return json.loads(response.read())["message"]["content"]


class Command:
    """Any program that reads a prompt on stdin and writes the answer on stdout."""

    def __init__(self, command, timeout=600):
        self.name, self.argv, self.timeout = f"command:{command}", shlex.split(command), timeout

    def complete(self, system, prompt):
        run = subprocess.run(self.argv, input=f"{system}\n\n{prompt}", capture_output=True,
                             text=True, timeout=self.timeout)
        if run.returncode:
            raise RuntimeError(run.stderr[:500])
        return run.stdout


class Cached:
    """Replay earlier answers, so a rerun asks nothing and sees the same claims."""

    def __init__(self, model, path):
        self.model, self.path = model, Path(path)
        self.name = model.name
        self.answers = json.loads(self.path.read_text()) if self.path.exists() else {}

    def complete(self, system, prompt):
        key = hashlib.sha256(f"{self.model.name}\0{system}\0{prompt}".encode()).hexdigest()
        if key not in self.answers:
            self.answers[key] = self.model.complete(system, prompt)
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.write_text(json.dumps(self.answers, indent=0))
        return self.answers[key]


def model_for(spec):
    kind, _, value = spec.partition(":")
    if kind == "ollama":
        return Ollama(value)
    if kind == "command":
        return Command(value)
    raise ValueError(f"unknown model {spec!r}: use ollama:<name> or command:<program>")


@dataclass
class Reading:
    """One definition, what the model read in it, and how each claim was judged."""

    subject: str
    label: str
    definition: str
    claims: list = field(default_factory=list)
    invalid: list = field(default_factory=list)
    error: str = ""


def _tokens(text):
    return {t for t in re.findall(r"[a-z][a-z-]{3,}", text.lower()) if t not in _STOP}


def readable(theory, prop):
    """Can a reader, or a model, tell what this property means from its label?"""
    return not re.fullmatch(r"[A-Z]+[ _]\d+", theory.label(prop))


def candidates(theory, subject, definition, classes=30, properties=30):
    """Classes that share words with the definition, and the properties that can be read.

    A relation often shares no word with the text that states it ("made mostly of" and
    "composed primarily of"), so properties are ranked by shared words but not cut by them.
    """
    words = _tokens(definition)

    def closest(terms, limit):
        scored = []
        for term in terms:
            if term == subject:
                continue
            label = theory.label(term)
            overlap = len(words & _tokens(label))
            if overlap:
                scored.append((-overlap, len(label), label, term))
        return [t for *_, t in sorted(scored)[:limit]]

    named = [p for p in sorted(theory.properties) if readable(theory, p)]
    chosen = closest(named, properties)
    chosen += [p for p in named if p not in chosen][:properties - len(chosen)]
    return closest(sorted(theory.classes), classes), chosen


def prompt_for(theory, subject, definition):
    classes, properties = candidates(theory, subject, definition)
    handles = {"T0": subject}
    handles.update({f"T{i + 1}": c for i, c in enumerate(classes)})
    handles.update({f"P{i + 1}": p for i, p in enumerate(properties)})
    listed = lambda prefix: "\n".join(  # noqa: E731
        f"{h} = {theory.label(t)}" for h, t in handles.items()
        if h.startswith(prefix) and h != "T0") or "(none)"
    text = _TEMPLATE.format(subject=theory.label(subject), definition=definition,
                            classes=listed("T"), properties=listed("P"))
    return text, handles


def parse_claims(answer, handles, subject):
    """Claims from a model's answer. Anything off the fixed shapes is set aside, not guessed."""
    match = re.search(r"\{.*\}", answer or "", flags=re.S)
    try:
        items = json.loads(match.group(0))["claims"] if match else None
    except (ValueError, KeyError, TypeError):
        items = None
    if not isinstance(items, list):
        return [], [str(answer)[:200]]
    claims, invalid = [], []

    def term(item, key, prefix):
        handle = item.get(key)
        return handles[handle] if handle in handles and str(handle).startswith(prefix) else None

    for item in items:
        if not isinstance(item, dict):
            invalid.append(str(item)[:200])
            continue
        kind = item.get("kind")
        axiom = None
        if kind == "sub" and (sup := term(item, "super", "T")) and sup != subject:
            axiom = Axiom("sub", (subject, sup))
        elif kind == "disjoint" and (other := term(item, "other", "T")) and other != subject:
            axiom = Axiom("disjoint", (subject, other))
        elif kind in ("some", "all"):
            prop, filler = term(item, "prop", "P"), term(item, "filler", "T")
            if prop and filler:
                axiom = Axiom(kind, (subject, prop, filler))
        if axiom is None:
            invalid.append(json.dumps(item)[:200])
        elif axiom not in claims:
            claims.append(axiom)
    return claims, invalid


def near_disjoint(theory):
    """Classes with a definition whose superclasses reach a disjointness axiom."""
    search = Search(theory)
    sides = {x for a in theory.index["disjoint"] for x in a.args}
    found = []
    for subject in sorted(theory.definitions):
        try:
            outcome = search.class_(subject)
        except Budget:
            continue
        if not outcome.clash and outcome.cls("x0") & sides:
            found.append(subject)
    return found


def read_definitions(theory, model, out="out", certify=True, limit=None, seed=0, only=None,
                     progress=None):
    """Judge what the definitions claim. `limit` takes a seeded sample of them."""
    verifier = Verifier(theory, out, certify)
    subjects = sorted(theory.definitions if only is None else only)
    if limit is not None and limit < len(subjects):
        subjects = sorted(random.Random(seed).sample(subjects, limit))
    readings = []
    for i, subject in enumerate(subjects):
        definition = theory.definitions[subject]
        reading = Reading(subject, theory.label(subject), definition)
        prompt, handles = prompt_for(theory, subject, definition)
        try:
            reading.claims, reading.invalid = parse_claims(
                model.complete(SYSTEM, prompt), handles, subject)
        except Exception as exc:  # a model that fails on one definition should not end the run
            reading.error = f"{type(exc).__name__}: {exc}"
        reading.findings = [verifier.judge(c, "definition") for c in reading.claims]
        readings.append(reading)
        if progress:
            progress(i + 1, len(subjects), reading)
    verifier.finish()
    return summarize(theory, model, readings), readings


def summarize(theory, model, readings):
    counts = {}
    items = []
    for reading in readings:
        judged = []
        for claim, finding in zip(reading.claims, reading.findings):
            word = VERDICTS.get(finding.verdict, finding.verdict)
            if finding.vacuous:
                word = "vacuous"
            if finding.kernel == "rejected":
                word = "rejected by the kernel"
            counts[word] = counts.get(word, 0) + 1
            judged.append({
                "claim": claim.text(theory.label),
                "lean": finding.statement,
                "verdict": word,
                "kernel": finding.kernel,
                "because": finding.because,
                "fragment": finding.fragment,
                "detail": finding.detail if finding.kernel == "rejected" else "",
            })
        items.append({"class": reading.subject, "label": reading.label,
                      "definition": reading.definition, "claims": judged,
                      "invalid": reading.invalid, "error": reading.error})
    return {
        "source": theory.source,
        "model": model.name,
        "definitions": len(readings),
        "with_claims": sum(bool(r.claims) for r in readings),
        "invalid_claims": sum(len(r.invalid) for r in readings),
        "errors": sum(bool(r.error) for r in readings),
        "verdicts": counts,
        "readings": items,
    }


def markdown(summary):
    """The findings for a person to read, disagreements first."""
    lines = [f"# Definitions against axioms: {summary['source']}", "",
             f"Model: `{summary['model']}`. {summary['definitions']} definitions, "
             f"{summary['with_claims']} with claims. Verdicts: {summary['verdicts']}.", ""]
    for word in ("contradicts", "rejected by the kernel", "says more", "vacuous", "agrees", "unknown"):
        found = [(r, c) for r in summary["readings"] for c in r["claims"] if c["verdict"] == word]
        if not found:
            continue
        lines += [f"## {word} ({len(found)})", ""]
        for reading, claim in found:
            lines += [f"- **{reading['label']}**: {reading['definition']}",
                      f"  - claim: `{claim['claim']}` (kernel: {claim['kernel']})"]
            if claim["because"]:
                lines.append("  - because: " + "; ".join(f"`{b}`" for b in claim["because"]))
        lines.append("")
    return "\n".join(lines)
