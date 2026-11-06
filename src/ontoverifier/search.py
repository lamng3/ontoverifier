"""The prover's search. It is not trusted, and nothing here needs to be correct.

A tableau with blocking over the fragment in `axioms`. It remembers how each fact
was derived, which gives two things to hand to Lean:

- a clash, from which `emit` writes a step-by-step proof using only the axioms
  the clash depends on;
- no clash, from which `models` reads off a finite model for Lean's `check`.

Blocking looks at every earlier node, not only at ancestors. That can miss a clash
when inverse properties push facts back along an edge, and a missed clash can only
produce a model that fails its check, which is reported as unknown. If this code has
a bug, Lean rejects what it wrote and the claim is never made.
"""

from dataclasses import dataclass, field

from ontoverifier.axioms import Axiom

MAX_NODES = 2000


class Budget(RuntimeError):
    """The search ran out of nodes before it settled the question."""


@dataclass(frozen=True)
class Step:
    """A derived fact: `axiom` applied to `premises`, at the nodes in `at`."""

    fact: tuple
    axiom: object
    premises: tuple = ()
    at: tuple = ()


@dataclass
class Outcome:
    clash: object = None  # the first clash: (axiom, fact, fact), or (axiom, fact)
    clashes: list = field(default_factory=list)
    steps: dict = field(default_factory=dict)
    labels: dict = field(default_factory=dict)
    out_edges: dict = field(default_factory=dict)
    in_edges: dict = field(default_factory=dict)
    pending: list = field(default_factory=list)
    nodes: list = field(default_factory=list)
    parent: dict = field(default_factory=dict)
    blocked: dict = field(default_factory=dict)
    seeds: list = field(default_factory=list)
    known: set = field(default_factory=set)
    exhausted: bool = False  # the budget ran out, so finding no clash settles nothing

    def add(self, step):
        """Record a derived fact. False if it was already known."""
        fact = step.fact
        if fact in self.steps:
            return False
        self.steps[fact] = step
        self.pending.append(fact)
        if fact[0] == "cls":
            self.labels.setdefault(fact[1], set()).add(fact[2])
        else:
            self.out_edges.setdefault(fact[2], set()).add((fact[1], fact[3]))
            self.in_edges.setdefault(fact[3], set()).add((fact[1], fact[2]))
        for node in _nodes(fact):
            if node not in self.known:
                self.known.add(node)
                self.nodes.append(node)
        return True

    def cls(self, node):
        return self.labels.get(node, set())

    def edges(self):
        return {(f[1], f[2], f[3]) for f in self.steps if f[0] == "rel"}

    def slice(self, clash=None):
        """Every step a clash depends on, premises first."""
        order, seen = [], set()

        def visit(fact):
            if fact in seen:
                return
            seen.add(fact)
            step = self.steps[fact]
            for premise in step.premises:
                visit(premise)
            order.append(step)

        for fact in (clash or self.clash)[1:]:
            visit(fact)
        return order


class Search:
    def __init__(self, theory, max_nodes=MAX_NODES):
        self.theory = theory
        self.max_nodes = max_nodes
        by = theory.index
        self.subs = _group(by["sub"], 0)
        self.nothing = {a.args[0]: a for a in by["nothing"]}
        self.disjoint = {}
        for a in by["disjoint"]:
            self.disjoint.setdefault(a.args[0], []).append((a.args[1], a))
            self.disjoint.setdefault(a.args[1], []).append((a.args[0], a))
        self.domains = _group(by["domain"], 0)
        self.ranges = _group(by["range"], 0)
        self.subprops = _group(by["subprop"], 0)
        self.inverses = _group(by["inverse"], 0)
        self.symmetric = {a.args[0]: a for a in by["symmetric"]}
        self.transitive = {a.args[0]: a for a in by["transitive"]}
        self.somes = _group(by["some"], 0)
        self.alls = _group(by["all"], 0)

    def run(self, seeds, every_clash=False):
        """Saturate from seed facts: ("cls", node, class) and ("rel", prop, x, y)."""
        out = Outcome(seeds=list(seeds))
        for fact in seeds:
            out.add(Step(fact, None))
        fresh = [0]
        while True:
            self._saturate(out, every_clash)
            if out.clash and not every_clash:
                return out
            try:
                if not self._expand(out, fresh):
                    return out
            except Budget:
                if not every_clash:
                    raise
                out.exhausted = True  # the clashes found so far still stand
                return out

    def abox(self):
        seeds = []
        for axiom in self.theory.index["type"]:
            seeds.append(("cls", axiom.args[0], axiom.args[1]))
        for axiom in self.theory.index["rel"]:
            seeds.append(("rel", axiom.args[1], axiom.args[0], axiom.args[2]))
        return self.run(seeds, every_clash=True)

    def class_(self, name):
        return self.run([("cls", "x0", name)])

    # The rules.

    def _saturate(self, out, every_clash=False):
        while out.pending:
            fact = out.pending.pop()
            for step in list(self._consequences(fact, out)):
                out.add(step)
            self._clash(fact, out)
            if out.clash and not every_clash:
                return

    def _consequences(self, fact, out):
        if fact[0] == "cls":
            _, x, c = fact
            for a in self.subs.get(c, ()):
                yield Step(("cls", x, a.args[1]), a, (fact,), (x,))
            for a in self.alls.get(c, ()):
                prop, target = a.args[1], a.args[2]
                for (p, o) in sorted(out.out_edges.get(x, ())):
                    if p == prop:
                        yield Step(("cls", o, target), a, (fact, ("rel", p, x, o)), (x, o))
            return
        _, p, x, y = fact
        for a in self.domains.get(p, ()):
            yield Step(("cls", x, a.args[1]), a, (fact,), (x, y))
        for a in self.ranges.get(p, ()):
            yield Step(("cls", y, a.args[1]), a, (fact,), (x, y))
        for a in self.subprops.get(p, ()):
            yield Step(("rel", a.args[1], x, y), a, (fact,), (x, y))
        for a in self.inverses.get(p, ()):
            yield Step(("rel", a.args[1], y, x), a, (fact,), (x, y))
        if p in self.symmetric:
            yield Step(("rel", p, y, x), self.symmetric[p], (fact,), (x, y))
        if p in self.transitive:
            for (q, o) in sorted(out.out_edges.get(y, ())):
                if q == p:
                    yield Step(("rel", p, x, o), self.transitive[p], (fact, ("rel", p, y, o)),
                               (x, y, o))
            for (q, s) in sorted(out.in_edges.get(x, ())):
                if q == p:
                    yield Step(("rel", p, s, y), self.transitive[p], (("rel", p, s, x), fact),
                               (s, x, y))
        for c in sorted(out.cls(x)):
            for a in self.alls.get(c, ()):
                if a.args[1] == p:
                    yield Step(("cls", y, a.args[2]), a, (("cls", x, c), fact), (x, y))

    def _clash(self, fact, out):
        if fact[0] != "cls":
            return
        _, x, c = fact
        found = []
        if c in self.nothing:
            found.append((self.nothing[c], fact))
        for other, axiom in self.disjoint.get(c, ()):
            if other == c:
                found.append((axiom, fact, fact))
            elif ("cls", x, other) in out.steps:
                partner = ("cls", x, other)
                first, second = (fact, partner) if axiom.args[0] == c else (partner, fact)
                found.append((axiom, first, second))
        for clash in found:
            if clash not in out.clashes:
                out.clashes.append(clash)
        if found and out.clash is None:
            out.clash = found[0]

    def _expand(self, out, fresh):
        """Add one witness for an unmet ∃. True if anything was added."""
        out.blocked.clear()
        having = {}  # class -> the active nodes with it, to find a blocker without a scan
        for node in out.nodes:
            label = out.cls(node)
            if node in out.parent and label:
                rarest = min(label, key=lambda c: len(having.get(c, ())))
                blocker = next((a for a in having.get(rarest, ()) if label <= out.cls(a)), None)
                if blocker is not None:
                    out.blocked[node] = blocker
                    continue
            for c in label:
                having.setdefault(c, []).append(node)
            for c in sorted(label):
                for a in self.somes.get(c, ()):
                    _, prop, target = a.args
                    met = any(p == prop and ("cls", o, target) in out.steps
                              for (p, o) in out.out_edges.get(node, ()))
                    if met:
                        continue
                    if len(out.parent) >= self.max_nodes:
                        raise Budget(f"more than {self.max_nodes} generated nodes")
                    fresh[0] += 1
                    witness = f"n{fresh[0]}"
                    out.parent[witness] = node
                    premise = ("cls", node, c)
                    out.add(Step(("rel", prop, node, witness), a, (premise,), (node, witness)))
                    out.add(Step(("cls", witness, target), a, (premise,), (node, witness)))
                    return True
        return False


def _group(axioms, index):
    grouped = {}
    for axiom in axioms:
        grouped.setdefault(axiom.args[index], []).append(axiom)
    return grouped


def _nodes(fact):
    return (fact[1],) if fact[0] == "cls" else (fact[2], fact[3])


__all__ = ["Axiom", "Budget", "Outcome", "Search", "Step"]
