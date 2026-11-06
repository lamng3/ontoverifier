"""Write what the search found as Lean proofs. Each theorem stands alone.

A theorem takes as hypotheses only the axioms its proof uses. Adding axioms keeps a
proof valid, so a proof from this slice is a proof from the whole ontology, and an
ontology of thousands of classes costs no more than the handful a proof touches. It
also means a proof stays valid for every later version that still has those axioms.

Hypotheses keep the ontology inconsistent-safe: nothing here is a Lean `axiom`, so a
bad ontology can never make Lean itself prove False. It can only make these
theorems' hypotheses unsatisfiable, which is what `theorem ... : False` then says.
"""

import re

from ontoverifier.axioms import local

_IDENT = re.compile(r"[^A-Za-z0-9_]")


class Names:
    """Lean identifiers for IRIs, readable and distinct."""

    def __init__(self):
        self.taken = {}
        self.used = set()

    def __call__(self, prefix, iri):
        key = (prefix, iri)
        if key not in self.taken:
            base = f"{prefix}_{_IDENT.sub('_', local(iri))}"
            name, n = base, 1
            while name in self.used:
                n += 1
                name = f"{base}_{n}"
            self.used.add(name)
            self.taken[key] = name
        return self.taken[key]


def sentence(axiom, names):
    """The axiom as a Lean proposition. `OntoVerifier.Axiom.holds` reads the same way."""
    a, c, p = axiom.args, lambda n: names("c", n), lambda n: names("p", n)
    return {
        "sub": lambda: f"∀ x, {c(a[0])} x → {c(a[1])} x",
        "disjoint": lambda: f"∀ x, {c(a[0])} x → {c(a[1])} x → False",
        "nothing": lambda: f"∀ x, {c(a[0])} x → False",
        "domain": lambda: f"∀ x y, {p(a[0])} x y → {c(a[1])} x",
        "range": lambda: f"∀ x y, {p(a[0])} x y → {c(a[1])} y",
        "subprop": lambda: f"∀ x y, {p(a[0])} x y → {p(a[1])} x y",
        "inverse": lambda: f"∀ x y, {p(a[0])} x y → {p(a[1])} y x",
        "symmetric": lambda: f"∀ x y, {p(a[0])} x y → {p(a[0])} y x",
        "transitive": lambda: f"∀ x y z, {p(a[0])} x y → {p(a[0])} y z → {p(a[0])} x z",
        "some": lambda: f"∀ x, {c(a[0])} x → ∃ y, {p(a[1])} x y ∧ {c(a[2])} y",
        "all": lambda: f"∀ x y, {c(a[0])} x → {p(a[1])} x y → {c(a[2])} y",
    }[axiom.kind]()


class Proof:
    """One theorem: the slice's axioms, then one `have` for each step of the derivation."""

    def __init__(self, outcome, facts=None):
        """`facts` are what the proof must reach; by default, the two sides of the clash."""
        self.outcome = outcome
        self.names = Names()
        self.clash = None if facts is not None else outcome.clash
        self.steps = outcome.slice((None, *facts) if facts is not None else None)
        self.axioms = []
        for step in self.steps:
            if step.axiom is not None and step.axiom not in self.axioms:
                self.axioms.append(step.axiom)
        if self.clash and self.clash[0] not in self.axioms:
            self.axioms.append(self.clash[0])
        self.hypothesis = {a: f"h{i}" for i, a in enumerate(self.axioms)}

    def term(self, node, free):
        """A node in the proof: a bound variable, a skolem from `obtain`, or a constant."""
        return free.get(node) or self.names("i", node)

    def fact(self, fact, free):
        if fact[0] == "cls":
            return f"{self.names('c', fact[2])} {self.term(fact[1], free)}"
        return f"{self.names('p', fact[1])} {self.term(fact[2], free)} {self.term(fact[3], free)}"

    def body(self, free, have):
        """The tactic steps: `have` names each fact it proves."""
        lines = []
        for step in self.steps:
            axiom = step.axiom
            if axiom is None or step.fact in have:
                continue
            h = self.hypothesis[axiom]
            if axiom.kind == "some":
                x, w = step.at
                n = len(have)
                free[w] = f"w{n}"
                have[("rel", axiom.args[1], x, w)] = f"f{n}r"
                have[("cls", w, axiom.args[2])] = f"f{n}c"
                lines.append(f"  obtain ⟨w{n}, f{n}r, f{n}c⟩ := "
                             f"{h} {self.term(x, free)} {have[step.premises[0]]}")
                continue
            n = len(have)
            args = " ".join(self.term(node, free) for node in step.at)
            premises = " ".join(have[p] for p in step.premises)
            lines.append(f"  have f{n} : {self.fact(step.fact, free)} := {h} {args} {premises}")
            have[step.fact] = f"f{n}"
        return lines

    def write(self, label, statement, intro, have, free, finish=None, mentions=(),
              assume_seeds=False, constants=()):
        names = self.names
        classes, props = set(), set()
        for axiom in (*self.axioms, *mentions):
            _symbols(axiom, classes, props)
        seeds = [s.fact for s in self.steps if s.axiom is None and s.fact not in have]
        for fact in seeds:
            if fact[0] == "cls":
                classes.add(fact[2])
            else:
                props.add(fact[1])
        individuals = set(constants)
        if assume_seeds:
            for fact in seeds:
                individuals.update(_nodes(fact))
        lines = [f"theorem {label} {{U : Type}}"]
        if classes:
            lines.append("    (" + " ".join(sorted(names("c", c) for c in classes)) + " : U → Prop)")
        if props:
            lines.append("    (" + " ".join(sorted(names("p", p) for p in props))
                         + " : U → U → Prop)")
        if individuals:
            lines.append("    (" + " ".join(sorted(names("i", i) for i in individuals)) + " : U)")
        for axiom in self.axioms:
            lines.append(f"    ({self.hypothesis[axiom]} : {sentence(axiom, names)})"
                         f" -- {axiom.text()}")
        if assume_seeds:
            for i, fact in enumerate(seeds):
                lines.append(f"    (s{i} : {self.fact(fact, free)})")
                have[fact] = f"s{i}"
        lines.append(f"    : {statement} := by")
        lines += intro
        lines += self.body(free, have)
        lines.append(finish(have, free) if finish else self.refute(have, free))
        return "\n".join(lines) + "\n"

    def refute(self, have, free):
        axiom, facts = self.clash[0], self.clash[1:]
        at = self.term(facts[0][1], free)
        args = " ".join(have[f] for f in facts)
        return f"  exact False.elim ({self.hypothesis[axiom]} {at} {args})"


def unsat_class(outcome, name, label):
    """`∀ x, ¬ C x`, from a clash reached from x0 : C."""
    proof = Proof(outcome)
    return proof.write(label, f"∀ x, ¬ {proof.names('c', name)} x", ["  intro x0 s0"],
                       {("cls", "x0", name): "s0"}, {"x0": "x0"},
                       mentions=[_mention(name)])


def inconsistent(outcome, clash, label):
    """`False`, from a clash among the assertions about named individuals."""
    held, outcome.clash = outcome.clash, clash
    proof = Proof(outcome)
    outcome.clash = held
    proof.clash = clash
    return proof.write(label, "False", [], {}, {}, assume_seeds=True)


def empty_query(outcome, variables, label):
    """`¬ ∃ vars, patterns`, from a clash among a query's patterns."""
    proof = Proof(outcome)
    free = {v: f"v{i}" for i, v in enumerate(variables)}
    have = {s: f"s{i}" for i, s in enumerate(outcome.seeds)}
    binders = " ".join(free.values())
    atoms = " ∧ ".join(proof.fact(s, free) for s in outcome.seeds)
    statement = f"¬ ∃ {binders}, {atoms}" if binders else f"¬ ({atoms})"
    pattern = ", ".join([*free.values(), *have.values()])
    constants = {n for s in outcome.seeds for n in _nodes(s) if n not in free}
    mentions = [_mention_fact(s) for s in outcome.seeds]
    return proof.write(label, statement, [f"  intro ⟨{pattern}⟩"], have, free,
                       mentions=mentions, constants=constants)


def holds(claim, outcome, seeds, label):
    """The claim itself, reached from the seeds that assume its left-hand side."""
    x = seeds[0][1]
    if outcome.clash:
        proof = Proof(outcome)
        finish = None
    elif claim.kind == "some":
        w = _successor(outcome, x, claim.args[1], claim.args[2])
        rel, cls = ("rel", claim.args[1], x, w), ("cls", w, claim.args[2])
        proof = Proof(outcome, (rel, cls))

        def finish(have, free):
            return f"  exact ⟨{proof.term(w, free)}, {have[rel]}, {have[cls]}⟩"
    else:
        target = ("cls", "y0" if claim.kind == "all" else x, claim.args[-1])
        proof = Proof(outcome, (target,))

        def finish(have, free):
            return f"  exact {have[target]}"
    free = {"x0": "x0", "y0": "y0"}
    have = {s: f"s{i}" for i, s in enumerate(seeds)}
    binders = "x0 y0" if claim.kind == "all" else "x0"
    intro = [f"  intro {binders} {' '.join(have.values())}"]
    return proof, proof.write(label, sentence(claim, proof.names), intro, have, free,
                              finish=finish, mentions=[claim])


def contradiction(outcome, name, label):
    """With the claim among the axioms, the class can have no instance."""
    return unsat_class(outcome, name, label)


def _successor(outcome, x, prop, target):
    for p, o in sorted(outcome.out_edges.get(x, ())):
        if p == prop and ("cls", o, target) in outcome.steps:
            return o
    raise LookupError(f"no {prop} successor of {x} in {target}")


def _nodes(fact):
    return (fact[1],) if fact[0] == "cls" else (fact[2], fact[3])


def _mention(name):
    from ontoverifier.axioms import Axiom
    return Axiom("nothing", (name,))


def _mention_fact(fact):
    from ontoverifier.axioms import Axiom
    if fact[0] == "cls":
        return Axiom("nothing", (fact[2],))
    return Axiom("symmetric", (fact[1],))


def _symbols(axiom, classes, props):
    a = axiom.args
    kind = axiom.kind
    if kind in ("sub", "disjoint"):
        classes.update(a)
    elif kind == "nothing":
        classes.add(a[0])
    elif kind in ("domain", "range"):
        props.add(a[0])
        classes.add(a[1])
    elif kind in ("subprop", "inverse"):
        props.update(a)
    elif kind in ("symmetric", "transitive"):
        props.add(a[0])
    elif kind in ("some", "all"):
        classes.update((a[0], a[2]))
        props.add(a[1])
