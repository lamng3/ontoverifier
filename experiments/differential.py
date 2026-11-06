"""Does the reasoner agree with hermitpy, and does Lean accept what it writes?

Random ontologies in the fragment both handle. Two independent reasoners should agree on
which classes can have instances. Where they differ, one of them has a bug.

    PYTHONPATH=src:../hermitpy/src python experiments/differential.py [ontologies] [seed]
"""

import json
import random
import sys
import tempfile
import time
from pathlib import Path

from hermitpy import Reasoner
from rdflib import BNode, Graph, Namespace, OWL, RDF, RDFS

from ontoverifier import Verifier
from ontoverifier.axioms import from_graph

EX = Namespace("http://example.org/r#")


def random_ontology(rng, classes=8, properties=3):
    g = Graph()
    cs = [EX[f"C{i}"] for i in range(classes)]
    ps = [EX[f"p{i}"] for i in range(properties)]
    for c in cs:
        g.add((c, RDF.type, OWL.Class))
    for p in ps:
        g.add((p, RDF.type, OWL.ObjectProperty))
    for _ in range(rng.randint(3, 10)):
        g.add((rng.choice(cs), RDFS.subClassOf, rng.choice(cs)))
    for _ in range(rng.randint(1, 4)):
        a, b = rng.sample(cs, 2)
        g.add((a, OWL.disjointWith, b))
    for _ in range(rng.randint(0, 4)):
        r = BNode()
        kind = rng.choice([OWL.someValuesFrom, OWL.allValuesFrom])
        g.add((r, RDF.type, OWL.Restriction))
        g.add((r, OWL.onProperty, rng.choice(ps)))
        g.add((r, kind, rng.choice(cs)))
        g.add((rng.choice(cs), RDFS.subClassOf, r))
    for _ in range(rng.randint(0, 2)):
        g.add((rng.choice(ps), rng.choice([RDFS.domain, RDFS.range]), rng.choice(cs)))
    if rng.random() < 0.3:
        one, other = rng.sample(ps, 2)
        g.add((one, OWL.inverseOf, other))
    if rng.random() < 0.3:
        g.add((rng.choice(ps), RDF.type, OWL.TransitiveProperty))
    if rng.random() < 0.2:
        g.add((rng.choice(ps), RDF.type, OWL.SymmetricProperty))
    return g, cs


def hermit_unsat(g, cs):
    out = set()
    for c in cs:
        probe = Graph()
        probe += g
        probe.add((EX.probe, RDF.type, c))
        if not Reasoner(probe).is_consistent():
            out.add(str(c))
    return out


def main(count=200, seed=0):
    rng = random.Random(seed)
    tally = dict(ontologies=0, classes=0, agree=0, we_only=0, hermit_only=0, hermit_failed=0,
                 unsat_proofs=0, witnesses=0, unknown=0, accepted=0, rejected=0)
    disagreements = []
    start = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        for i in range(count):
            g, cs = random_ontology(rng)
            theory = from_graph(g, source=f"random {seed}/{i}")
            v = Verifier(theory, Path(tmp) / str(i), certify=True, cache=False)
            ours = set(v.unsatisfiable_classes())
            try:
                theirs = hermit_unsat(g, cs)
            except Exception as exc:
                tally["hermit_failed"] += 1
                disagreements.append({"ontology": i, "hermit_error": str(exc)[:200]})
                continue
            tally["ontologies"] += 1
            tally["classes"] += len(cs)
            tally["agree"] += len(cs) - len(ours ^ theirs)
            tally["we_only"] += len(ours - theirs)
            tally["hermit_only"] += len(theirs - ours)
            if ours != theirs:
                disagreements.append({
                    "ontology": i, "we_only": sorted(ours - theirs),
                    "hermit_only": sorted(theirs - ours),
                    "axioms": [a.text() for a in theory.axioms]})
            report = v.check(witnesses=len(cs))
            for f in report["findings"]:
                if f["kind"] == "unsatisfiable":
                    tally["unsat_proofs"] += 1
                if f["kind"] == "witness":
                    tally["witnesses" if f["verdict"] == "satisfied" else "unknown"] += 1
                if f["name"]:
                    tally["accepted" if f["kernel"] == "accepted" else "rejected"] += 1
                    if f["kernel"] != "accepted":
                        disagreements.append({"ontology": i, "rejected": f["name"],
                                              "detail": f["detail"][:400]})
    tally["seconds"] = round(time.time() - start, 1)
    tally["seed"] = seed
    out = Path("results/differential.json")
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps({"tally": tally, "disagreements": disagreements}, indent=1))
    print(json.dumps(tally, indent=1))
    for item in disagreements[:6]:
        print(json.dumps(item)[:600])


if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:]))
