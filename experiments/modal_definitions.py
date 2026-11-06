"""Check the ENVO definition runs on Modal, so that kernel work does not hold your laptop.

The model's answers are read first, on your machine, with --no-kernel:

    sh experiments/definitions.sh

This replays those answers and sends everything through Lean's kernel, which is where the
time goes. The container never calls a model: an answer that is missing shows up as an error
in the run's summary. Results are written back under results/envo-definitions/.

    modal run experiments/modal_definitions.py --only sonnet
"""

from pathlib import Path

import modal

ROOT = Path(__file__).resolve().parent.parent
ENVO = ROOT.parent / "agentic-ontologist/data/BioDiv/envo-sweet/envo.owl"
MODEL = ('command:claude -p --model claude-sonnet-5-5 --tools "" --no-session-persistence '
         '--setting-sources ""')
RUNS = {
    "sonnet": ["--limit", "60", "--seed", "1"],
    "sonnet-near-disjoint": ["--near-disjoint", "--limit", "80", "--seed", "1"],
}
KEEP = ("comments.json", "comments.md", "proofs.lean", "models.lean")
ELAN = ("curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh "
        "| sh -s -- -y --default-toolchain leanprover/lean4:v4.35.0")

image = (
    modal.Image.debian_slim(python_version="3.11")
    .apt_install("curl", "git")
    .uv_pip_install("rdflib>=7")
    .run_commands(ELAN)
    .env({"PATH": "/root/.elan/bin:/usr/local/bin:/usr/bin:/bin",
          "PYTHONPATH": "/app/src", "ONTOVERIFIER_ROOT": "/app",
          "ONTOVERIFIER_CACHE": "/results/kernel.json", "ONTOVERIFIER_WORKERS": "8"})
    .add_local_dir(ROOT / "OntoVerifier", "/app/OntoVerifier", copy=True)
    .add_local_file(ROOT / "OntoVerifier.lean", "/app/OntoVerifier.lean", copy=True)
    .add_local_file(ROOT / "lakefile.toml", "/app/lakefile.toml", copy=True)
    .add_local_file(ROOT / "lake-manifest.json", "/app/lake-manifest.json", copy=True)
    .add_local_file(ROOT / "lean-toolchain", "/app/lean-toolchain", copy=True)
    .run_commands("cd /app && lake build")
    .add_local_dir(ROOT / "src", "/app/src")
    .add_local_file(ENVO, "/data/envo.owl")
)
results = modal.Volume.from_name("ontoverifier-results", create_if_missing=True)
app = modal.App("ontoverifier-definitions")


@app.function(image=image, cpu=8, memory=16384, timeout=4 * 60 * 60,
              volumes={"/results": results})
def check(name, flags, answers):
    import subprocess
    import sys
    import time

    out = Path("/results") / name
    out.mkdir(parents=True, exist_ok=True)
    (out / "answers.json").write_text(answers)
    start = time.time()
    run = subprocess.run([sys.executable, "-m", "ontoverifier.cli", "comments", "/data/envo.owl",
                          "--model", MODEL, *flags, "--out", str(out)],
                         capture_output=True, text=True)
    results.commit()
    found = {f: (out / f).read_text() for f in KEEP if (out / f).exists()}
    return {"files": found, "code": run.returncode, "stdout": run.stdout[-1000:],
            "stderr": run.stderr[-1500:], "seconds": round(time.time() - start, 1)}


@app.local_entrypoint()
def main(only: str = ""):
    names = [only] if only else list(RUNS)
    for name in names:
        where = ROOT / "results/envo-definitions" / name
        answer = check.remote(name, RUNS[name], (where / "answers.json").read_text())
        for file, text in answer["files"].items():
            (where / file).write_text(text)
        print(name, "exit", answer["code"], "seconds", answer["seconds"])
        print(answer["stdout"])
        if answer["code"]:
            print(answer["stderr"])
