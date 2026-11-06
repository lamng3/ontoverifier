"""What a new version of an ontology changes in meaning, not just in text.

Two versions can differ by one line and disagree about thousands of subclass facts, or
differ a lot and mean the same. `compare` reads both and reports:

    new unsatisfiable classes   a class that could exist and now cannot, with a proof
                                and the added axioms that proof rests on
    new data clashes            assertions that were fine and now contradict the axioms
    lost subsumptions           what used to follow and no longer does: a proof for the
                                old version and a refuting model for the new one
    gained subsumptions         what now follows that did not, with a proof

The first two are errors and block the version. Lost subsumptions are a breaking change
for whoever relied on them, which is a decision, so they block only under `strict`.

Proofs rest on named axioms, so a proof carries over to every later version that still
has them. The kernel cache makes that concrete: only new theorems are ever checked.
"""

from dataclasses import dataclass, field
from pathlib import Path

from ontoverifier.axioms import Axiom
from ontoverifier.verifier import Verifier


@dataclass
class Change:
    old: str
    new: str
    added: list = field(default_factory=list)
    removed: list = field(default_factory=list)
    new_unsatisfiable: list = field(default_factory=list)
    resolved_unsatisfiable: list = field(default_factory=list)
    new_clashes: list = field(default_factory=list)
    lost: list = field(default_factory=list)
    gained: list = field(default_factory=list)
    lost_total: int = 0
    gained_total: int = 0
    out_of_budget: int = 0
    kernel: dict = field(default_factory=dict)

    def blocked(self, strict=False):
        return bool(self.new_unsatisfiable or self.new_clashes or (strict and self.lost_total))

    def rejected(self):
        return self.kernel.get("rejected", 0)

    def as_dict(self, strict=False):
        return {
            "old": self.old,
            "new": self.new,
            "blocked": self.blocked(strict),
            "axioms_added": len(self.added),
            "axioms_removed": len(self.removed),
            "new_unsatisfiable": self.new_unsatisfiable,
            "resolved_unsatisfiable": self.resolved_unsatisfiable,
            "new_clashes": self.new_clashes,
            "lost_total": self.lost_total,
            "gained_total": self.gained_total,
            "lost": self.lost,
            "gained": self.gained,
            "out_of_budget": self.out_of_budget,
            "kernel": self.kernel,
        }


def compare(old, new, out="out", certify=True, limit=50, cache=True):
    """Compare two Theories. `limit` caps the lost and gained facts that get certificates."""
    out = Path(out)
    before = Verifier(old, out / "old", certify, cache=cache)
    after = Verifier(new, out / "new", certify, cache=cache)
    old_axioms, new_axioms = set(old.axioms), set(new.axioms)
    added = new_axioms - old_axioms
    change = Change(old.source, new.source,
                    added=sorted(added, key=_order), removed=sorted(old_axioms - new_axioms, key=_order))

    was = set(before.unsatisfiable_classes())
    now = set(after.unsatisfiable_classes())
    change.resolved_unsatisfiable = sorted(was - now)
    after.prove_unsatisfiable()
    fresh = {f.subject: f for f in after.findings if f.kind == "unsatisfiable" and f.subject not in was}

    old_clashes = before.data_clashes()
    known = {_clash_key(c) for c in old_clashes.clashes} if old_clashes else set()
    after.prove_data()
    clashes = [f for f in after.findings if f.kind == "data clash"]
    new_outcome = after.data_clashes()
    keys = [_clash_key(c) for c in new_outcome.clashes] if new_outcome else []
    fresh_clashes = [f for f, key in zip(clashes, keys) if key not in known]

    old_tree, new_tree = before.hierarchy(), after.hierarchy()
    lost, gained = [], []
    for c in sorted(old_tree):
        if c not in new_tree:
            continue
        for d in sorted(old_tree[c] - new_tree[c]):
            if d in new.classes:
                lost.append((c, d))
        for d in sorted(new_tree[c] - old_tree[c]):
            gained.append((c, d))
    change.lost_total, change.gained_total = len(lost), len(gained)
    change.out_of_budget = len(after.out_of_budget())

    lost_pairs = []
    for c, d in lost[:limit]:
        claim = Axiom("sub", (c, d))
        lost_pairs.append((before.judge(claim, "lost: proof in old"),
                           after.judge(claim, "lost: refuted in new")))
    gained_findings = [after.judge(Axiom("sub", pair), "gained") for pair in gained[:limit]]

    before.finish()
    after.finish()

    for name in sorted(fresh):
        finding = fresh[name]
        change.new_unsatisfiable.append(_explained(finding, added))
    change.new_clashes = [_explained(f, added) for f in fresh_clashes]
    change.lost = [{"claim": b.claim, "old": _brief(a), "new": _brief(b)} for a, b in lost_pairs]
    change.gained = [_brief(f) for f in gained_findings]

    counts = {}
    for finding in (*before.findings, *after.findings):
        if finding.name:
            key = "cached" if finding.cached else finding.kernel
            counts[key] = counts.get(key, 0) + 1
    change.kernel = counts
    return change


def history(theories, out="out", certify=True, limit=50):
    """Each version against the one before it."""
    return [compare(one, other, Path(out) / f"step{i + 1}", certify, limit)
            for i, (one, other) in enumerate(zip(theories, theories[1:]))]


def _explained(finding, added):
    return {
        "subject": finding.subject,
        "claim": finding.claim,
        "kernel": finding.kernel,
        "because": finding.because,
        "added_axioms_used": [a.text() for a in finding.used if a in added],
    }


def _brief(finding):
    return {"verdict": finding.verdict, "kernel": finding.kernel, "claim": finding.claim,
            "because": finding.because}


def _clash_key(clash):
    return (clash[0], clash[1:])


def _order(axiom):
    return (axiom.kind, axiom.args)
