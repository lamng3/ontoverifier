"""One object for reasoning and proof.

`certify=False` is a plain reasoner: fast, and its answers come from the search.
`certify=True` is the same reasoner, with each answer sent through Lean's kernel. The
two give the same verdicts; only what stands behind them differs, and `kernel` on a
finding says which it is.

Verdicts on a claim, under the open-world reading:

    entailed       the axioms prove it, whatever else is added later
    contradiction  the axioms plus the claim leave its subject with no instance
    refuted        a model of the axioms where it fails: the axioms do not say it
    unknown        the search could not settle it

`entailed` and `contradiction` survive axioms the translator skipped. `refuted` is for
the translated fragment, and `Finding.fragment` says when axioms were skipped.
"""

import hashlib
from dataclasses import asdict, dataclass, field
from pathlib import Path

from rdflib.plugins.sparql import prepareQuery

from ontoverifier import emit, lean, models
from ontoverifier.axioms import Axiom, local
from ontoverifier.search import MAX_NODES, Budget, Search

CLAIMS = ("sub", "some", "all", "disjoint")
CONSISTENCY_LIMIT = 3000  # axioms plus facts: the checker is linear in each, so this is its product


@dataclass
class Finding:
    kind: str
    subject: str
    verdict: str
    claim: str = ""
    statement: str = ""
    because: list = field(default_factory=list)
    used: list = field(default_factory=list)
    kernel: str = "not_run"
    cached: bool = False
    detail: str = ""
    name: str = ""
    fragment: bool = False
    vacuous: bool = False

    def as_dict(self):
        out = asdict(self)
        out.pop("used")
        return out


class Verifier:
    def __init__(self, theory, out="out", certify=True, max_nodes=MAX_NODES, cache=True):
        self.theory = theory
        self.out = Path(out)
        self.certify = certify
        self.max_nodes = max_nodes
        self.search = Search(theory, max_nodes)
        self.cache = lean.Cache() if cache else None
        self._outcomes = {}
        self._theorems = None
        self.findings = []
        self.proofs = lean.Batch(self.out / "proofs.lean", cache=self.cache)
        self._abox = False

    # The reasoner.

    def outcome(self, name):
        """The search from one instance of a class, or None if out of budget."""
        if name not in self._outcomes:
            try:
                self._outcomes[name] = self.search.class_(name)
            except Budget:
                self._outcomes[name] = None
        return self._outcomes[name]

    def unsatisfiable_classes(self):
        return sorted(c for c in self.theory.classes
                      if (o := self.outcome(c)) is not None and o.clash)

    def out_of_budget(self):
        return sorted(c for c in self.theory.classes if self.outcome(c) is None)

    def hierarchy(self):
        """Every satisfiable class with its named superclasses, itself excluded."""
        found = {}
        for c in sorted(self.theory.classes):
            outcome = self.outcome(c)
            if outcome is not None and not outcome.clash:
                found[c] = {d for d in outcome.cls("x0") if d != c}
        return found

    def direct_subclasses(self):
        """(sub, super) pairs with nothing strictly between them. Equivalents go both ways."""
        tree = self.hierarchy()
        pairs = set()
        for c, supers in tree.items():
            for d in supers:
                between = any(e not in (c, d) and d in tree.get(e, ()) and c not in tree.get(e, ())
                              for e in supers)
                if not between:
                    pairs.add((c, d))
        return pairs

    def data_clashes(self):
        if self._abox is False:
            has_data = self.theory.index["type"] or self.theory.index["rel"]
            self._abox = self.search.abox() if has_data else None
        return self._abox

    def is_consistent(self):
        """True, False, or None when the search ran out of budget before finding a clash."""
        outcome = self.data_clashes()
        if outcome is None:
            return True
        if outcome.clashes:
            return False
        return None if outcome.exhausted else True

    # The verifier: findings, each of which can go through the kernel.

    @staticmethod
    def _name(stem, *key):
        """A name that depends only on what is claimed, so it is the same in every version."""
        return f"{stem}_{hashlib.sha256(chr(0).join(key).encode()).hexdigest()[:12]}"

    def _record(self, finding, text=None, batch=None):
        if text is not None:
            (batch or self.proofs).add(finding.name, text)
        self.findings.append(finding)
        return finding

    def prove_unsatisfiable(self, names=None):
        """Write a proof for these classes, which must be unsatisfiable; by default, all that are."""
        for name in self.unsatisfiable_classes() if names is None else names:
            outcome = self.outcome(name)
            label = self._name("unsat", name)
            proof = emit.Proof(outcome)
            self._record(Finding(
                "unsatisfiable", name, "entailed", claim=f"{local(name)} ⊑ ⊥",
                because=[a.text() for a in proof.axioms], used=list(proof.axioms),
                name=label), emit.unsat_class(outcome, name, label))

    def prove_data(self):
        outcome = self.data_clashes()
        if outcome is None:
            return
        for clash in outcome.clashes:
            label = self._name("data", clash[0].text(), *map(str, clash[1:]))
            held, outcome.clash = outcome.clash, clash
            proof = emit.Proof(outcome)
            outcome.clash = held
            self._record(Finding(
                "data clash", clash[1][1], "entailed", claim=f"{local(clash[1][1])} clashes",
                because=[a.text() for a in proof.axioms], used=list(proof.axioms),
                name=label), emit.inconsistent(outcome, clash, label))
        if outcome.clashes or outcome.exhausted:
            return
        facts = len(self.theory.index["type"]) + len(self.theory.index["rel"])
        if self.theory.translated + facts <= CONSISTENCY_LIMIT:
            self._certify_consistent(outcome)

    def _certify_consistent(self, outcome):
        named = {n: i for i, n in enumerate(sorted(self.theory.individuals))}
        table = models.Theorems(self.theory.axioms, named)
        candidate = models.build(outcome, self.theory, named)
        if not all(models.holds(candidate, a) for a in self.theory.axioms):
            return
        batch = lean.Batch(self.out / "consistent.lean", table.prelude(), self.cache)
        label = self._name("consistent", self.theory.source)
        finding = Finding("consistent", self.theory.source, "satisfied", name=label,
                          fragment=bool(self.theory.skipped))
        batch.add(label, table.consistent(label, candidate))
        self._record(finding)
        self._apply(batch)

    def witness_classes(self, limit=None):
        """A checked model for each satisfiable class, up to `limit`."""
        names = [c for c in sorted(self.theory.classes)
                 if (o := self.outcome(c)) is not None and not o.clash]
        for name in names[:limit]:
            outcome = self.outcome(name)
            candidate = models.build(outcome, self.theory)
            if not all(models.holds(candidate, a) for a in self.theory.terminology):
                self.findings.append(Finding("witness", name, "unknown",
                                             detail="the candidate failed the first look"))
                continue
            label = self._name("sat", name)
            self._record(Finding(
                "witness", name, "satisfied", name=label, fragment=bool(self.theory.skipped)),
                self.table().satisfiable(label, candidate, name, candidate.element["x0"]),
                self.models_batch())

    def judge(self, claim, kind="claim"):
        """Does the claim follow, contradict, or go beyond the terminology?"""
        if claim.kind not in CLAIMS:
            raise ValueError(f"cannot judge a {claim.kind} claim")
        subject = claim.args[0]
        text = claim.text()
        statement = emit.sentence(claim, emit.Names())
        base = dict(kind=kind, subject=subject, claim=text, statement=statement)
        seeds = _seeds(claim)
        try:
            outcome = self.search.run(seeds)
        except Budget:
            return self._record(Finding(**base, verdict="unknown", detail="out of budget"))
        before = self.outcome(subject)
        vacuous = before is not None and bool(before.clash)
        if _reached(claim, outcome, seeds):
            label = self._name("holds", claim.kind, *claim.args)
            proof, written = emit.holds(claim, outcome, seeds, label)
            return self._record(Finding(
                **base, verdict="entailed", name=label, vacuous=vacuous,
                because=[a.text() for a in proof.axioms], used=list(proof.axioms)), written)
        found = self._contradiction(claim, base)
        if found:
            return found
        candidate = models.build(outcome, self.theory)
        fits = all(models.holds(candidate, a) for a in self.theory.terminology)
        if not fits or models.holds(candidate, claim):
            return self._record(Finding(**base, verdict="unknown",
                                        detail="no model that refutes it was found"))
        label = self._name("refute", claim.kind, *claim.args)
        return self._record(Finding(
            **base, verdict="refuted", name=label, fragment=bool(self.theory.skipped)),
            self.table().refutes(label, candidate, claim), self.models_batch())

    def _contradiction(self, claim, base):
        extended = Search(self.theory.extended(claim), self.max_nodes)
        for name in _subjects(claim):
            before = self.outcome(name)
            if before is not None and before.clash:
                continue
            try:
                outcome = extended.class_(name)
            except Budget:
                continue
            if outcome.clash:
                label = self._name("contradiction", claim.kind, *claim.args, name)
                proof = emit.Proof(outcome)
                return self._record(Finding(
                    **base, verdict="contradiction", name=label,
                    because=[a.text() for a in proof.axioms], used=list(proof.axioms)),
                    emit.contradiction(outcome, name, label))
        return None

    def query(self, sparql):
        """Can a query of one basic graph pattern have answers on any graph?"""
        variables, seeds = _bgp(sparql)
        base = dict(kind="query", subject=" ".join(variables) if seeds else "", claim=sparql.strip())
        if seeds is None:
            return self._record(Finding(**base, verdict="unknown", detail=variables))
        outcome = self.search.run(seeds)
        if not outcome.clash:
            return self._record(Finding(**base, verdict="no_clash",
                                        detail="the search found no reason it must be empty"))
        label = self._name("empty", sparql)
        proof = emit.Proof(outcome)
        return self._record(Finding(
            **base, verdict="entailed", name=label, because=[a.text() for a in proof.axioms],
            used=list(proof.axioms)), emit.empty_query(outcome, variables, label))

    # Certificates.

    def table(self):
        if self._theorems is None:
            self._theorems = models.Theorems(self.theory.terminology)
        return self._theorems

    def models_batch(self):
        if not hasattr(self, "_models"):
            self._models = lean.Batch(self.out / "models.lean", "", self.cache)
        return self._models

    def _apply(self, batch):
        if not self.certify or not batch.theorems:
            return
        results = batch.run()
        for finding in self.findings:
            if finding.name in results:
                checked = results[finding.name]
                finding.kernel, finding.detail, finding.cached = (
                    checked.kernel, checked.detail, checked.cached)

    def finish(self):
        """Send everything written so far through the kernel."""
        self._apply(self.proofs)
        if hasattr(self, "_models"):
            self._models.prelude = self.table().prelude()
            self._apply(self._models)
        return self.findings

    def check(self, witnesses=None):
        """Everything about the ontology: classes, data, and witnesses when they are cheap."""
        self.prove_unsatisfiable()
        self.prove_data()
        if witnesses is None:
            witnesses = len(self.theory.classes) if self.theory.translated <= 300 else 0
        if witnesses:
            self.witness_classes(witnesses)
        self.finish()
        return self.report()

    def report(self):
        counts = {}
        for finding in self.findings:
            key = (finding.kind, finding.verdict, finding.kernel)
            counts[key] = counts.get(key, 0) + 1
        return {
            "source": self.theory.source,
            "axioms": self.theory.translated,
            "not_translated": dict(self.theory.skipped),
            "coverage": round(self.theory.coverage(), 4),
            "classes": len(self.theory.classes),
            "consistent": self.is_consistent(),
            "unsatisfiable": len(self.unsatisfiable_classes()),
            "out_of_budget": len(self.out_of_budget()),
            "counts": [{"kind": k, "verdict": v, "kernel": n, "count": c}
                       for (k, v, n), c in sorted(counts.items())],
            "findings": [f.as_dict() for f in self.findings],
        }


def _seeds(claim):
    a = claim.args
    if claim.kind == "all":
        return [("cls", "x0", a[0]), ("rel", a[1], "x0", "y0")]
    if claim.kind == "disjoint":
        return [("cls", "x0", a[0]), ("cls", "x0", a[1])]
    return [("cls", "x0", a[0])]


def _subjects(claim):
    if claim.kind == "disjoint":
        return claim.args[:2]
    return claim.args[:1]


def _reached(claim, outcome, seeds):
    if outcome.clash:
        return True
    a = claim.args
    if claim.kind == "sub":
        return ("cls", "x0", a[1]) in outcome.steps
    if claim.kind == "all":
        return ("cls", "y0", a[2]) in outcome.steps
    if claim.kind == "some":
        return any(p == a[1] and ("cls", o, a[2]) in outcome.steps
                   for p, o in outcome.out_edges.get("x0", ()))
    return False


def _bgp(sparql):
    """(variables, seed facts) for a query of one basic graph pattern, else (reason, None)."""
    node = prepareQuery(sparql).algebra.p
    while node.name in ("Project", "Distinct", "Reduced", "Slice", "OrderBy"):
        node = node.p
    if node.name != "BGP":
        return f"has {node.name}, and only basic graph patterns are translated", None
    names, seeds = {}, []

    def term(value):
        if type(value).__name__ == "Variable":
            return names.setdefault(f"?{value}", f"?{value}")
        return str(value)

    for s, p, o in node.triples:
        if type(p).__name__ == "Variable" or type(o).__name__ == "Literal":
            return "has a variable predicate or a literal", None
        if str(p).endswith("#type"):
            if type(o).__name__ == "Variable":
                return "has a variable class", None
            seeds.append(("cls", term(s), str(o)))
        else:
            seeds.append(("rel", str(p), term(s), term(o)))
    return list(names), seeds


__all__ = ["Axiom", "CLAIMS", "Finding", "Verifier"]
