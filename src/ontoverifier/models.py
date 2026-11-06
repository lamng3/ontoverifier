"""Finite models, written as data for the checker proved correct in OntoVerifier/Model.lean.

The search reads off a candidate. `holds` tries it here first, so that a bad candidate
is reported as unknown without troubling Lean. Lean then runs its own `check`, and that
is the only verdict that counts: nothing in this file is trusted.
"""

from dataclasses import dataclass, field

CHUNK = 400


@dataclass
class Model:
    """Elements are integers. `element` maps the search's nodes to them."""

    classes: set = field(default_factory=set)  # (class IRI, element)
    edges: set = field(default_factory=set)  # (property IRI, from, to)
    element: dict = field(default_factory=dict)


def build(outcome, theory, named=None):
    """The candidate from a finished search. `named` fixes the elements of individuals."""
    named = named or {}
    start = max(named.values(), default=-1) + 1
    model = Model(element=dict(named))
    for node in outcome.nodes:
        if node in outcome.blocked or node in model.element:
            continue
        model.element[node] = start
        start += 1
    for node, element in model.element.items():
        if node in outcome.blocked:
            continue
        for c in outcome.cls(node):
            model.classes.add((c, element))
    for p, s, o in outcome.edges():
        if s not in outcome.blocked:
            model.edges.add((p, model.element[s], model.element[outcome.blocked.get(o, o)]))
    _close(model, theory)
    return model


def _close(model, theory):
    """Add what property axioms require of the edges that blocking redirected."""
    index = theory.index
    changed = True
    while changed:
        before = len(model.edges)
        for a in index["subprop"]:
            model.edges |= {(a.args[1], s, o) for p, s, o in model.edges if p == a.args[0]}
        for a in index["inverse"]:
            model.edges |= {(a.args[1], o, s) for p, s, o in model.edges if p == a.args[0]}
        for a in index["symmetric"]:
            model.edges |= {(p, o, s) for p, s, o in model.edges if p == a.args[0]}
        for a in index["transitive"]:
            pairs = [(s, o) for p, s, o in model.edges if p == a.args[0]]
            by_source = {}
            for s, o in pairs:
                by_source.setdefault(s, []).append(o)
            model.edges |= {(a.args[0], s, z) for s, o in pairs for z in by_source.get(o, ())}
        changed = len(model.edges) != before


def holds(model, axiom, individual=None):
    """The axiom on the model. Mirrors `check` in Lean, for a cheap first look."""
    cls, edges = model.classes, model.edges
    a = axiom.args
    kind = axiom.kind
    if kind == "sub":
        return all((a[1], x) in cls for c, x in cls if c == a[0])
    if kind == "disjoint":
        return not any((a[1], x) in cls for c, x in cls if c == a[0])
    if kind == "nothing":
        return not any(c == a[0] for c, _ in cls)
    if kind == "domain":
        return all((a[1], s) in cls for p, s, _ in edges if p == a[0])
    if kind == "range":
        return all((a[1], o) in cls for p, _, o in edges if p == a[0])
    if kind == "subprop":
        return all((a[1], s, o) in edges for p, s, o in edges if p == a[0])
    if kind == "inverse":
        return all((a[1], o, s) in edges for p, s, o in edges if p == a[0])
    if kind == "symmetric":
        return all((p, o, s) in edges for p, s, o in edges if p == a[0])
    if kind == "transitive":
        pairs = [(s, o) for p, s, o in edges if p == a[0]]
        return all((a[0], s, z) in edges for s, o in pairs for y, z in pairs if y == o)
    if kind == "some":
        return all(any(p == a[1] and s == x and (a[2], o) in cls for p, s, o in edges)
                   for c, x in cls if c == a[0])
    if kind == "all":
        return all((a[2], o) in cls for c, x in cls if c == a[0]
                   for p, s, o in edges if p == a[1] and s == x)
    if kind == "type":
        return (a[1], model.element[a[0]]) in cls
    if kind == "rel":
        return (a[1], model.element[a[0]], model.element[a[2]]) in edges
    raise ValueError(kind)


class Theorems:
    """A Lean file for one theory: its axioms as data, then models checked against them."""

    def __init__(self, axioms, named=None):
        self.axioms = axioms
        self.named = named or {}
        self.ids = {}
        for axiom in axioms:
            self._term_ids(axiom)

    def number(self, kind, iri):
        return self.ids.setdefault((kind, iri), len(self.ids))

    def _term_ids(self, axiom):
        return _render(axiom, self)

    def prelude(self):
        lines = ["import OntoVerifier.Model", "open OntoVerifier", ""]
        lines.append("/-! Identifiers:")
        for (kind, iri), number in sorted(self.ids.items(), key=lambda x: x[1]):
            lines.append(f"  {number} = {kind} {iri.replace('-/', '- /')}")
        lines.append("-/")
        chunks = [self.axioms[i:i + CHUNK] for i in range(0, len(self.axioms), CHUNK)] or [[]]
        for i, chunk in enumerate(chunks):
            body = ", ".join(_render(a, self) for a in chunk)
            lines.append(f"def T{i} : List Axiom := [{body}]")
        lines.append("def T : List Axiom := " + " ++ ".join(f"T{i}" for i in range(len(chunks))))
        return "\n".join(lines) + "\n"

    def model(self, model):
        cls = ", ".join(f"({self.number('term', c)}, {x})" for c, x in sorted(model.classes))
        rel = ", ".join(f"({self.number('term', p)}, {s}, {o})"
                        for p, s, o in sorted(model.edges))
        return f"⟨[{cls}], [{rel}]⟩"

    def mask(self, model):
        """One bit for each class and property the model uses. The kernel checks it covers them."""
        bits = 0
        for c, _ in model.classes:
            bits |= 1 << self.number("term", c)
        for p, _, _ in model.edges:
            bits |= 1 << self.number("term", p)
        return hex(bits)

    def refutes(self, label, model, claim):
        """The theory does not entail the claim."""
        return (f"def m_{label} : FinModel := {self.model(model)}\n"
                f"theorem {label} : ¬ Entails T ({_render(claim, self)}) :=\n"
                f"  refutes m_{label} {self.mask(model)} (by decide +kernel) (by decide +kernel)\n")

    def satisfiable(self, label, model, name, element=0):
        return (f"def m_{label} : FinModel := {self.model(model)}\n"
                f"theorem {label} : ∃ (U : Type) (I : Interp U), Models I T ∧ "
                f"∃ y, I.cls {self.number('term', name)} y :=\n"
                f"  satisfiable m_{label} {self.mask(model)} {element} "
                f"(by decide +kernel) (by decide +kernel)\n")

    def consistent(self, label, model):
        return (f"def m_{label} : FinModel := {self.model(model)}\n"
                f"theorem {label} : ∃ (U : Type) (I : Interp U), Models I T :=\n"
                f"  consistent m_{label} {self.mask(model)} (by decide +kernel)\n")


def _render(axiom, table):
    a = axiom.args
    if axiom.kind == "type":
        return f".type {table.named[a[0]]} {table.number('term', a[1])}"
    if axiom.kind == "rel":
        return f".rel {table.named[a[0]]} {table.number('term', a[1])} {table.named[a[2]]}"
    args = " ".join(str(table.number("term", x)) for x in a)
    return f".{axiom.kind} {args}"
