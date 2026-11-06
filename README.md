<div align="center">

# OntoVerifier

**A reasoner for changing ontologies, with answers checked by Lean's kernel**

[![Python](https://img.shields.io/badge/python-3.11%2B-3b82f6)](pyproject.toml)
[![Lean](https://img.shields.io/badge/lean-4.35-8b5cf6)](lean-toolchain)
[![License](https://img.shields.io/badge/license-BSD--3--Clause-green.svg)](LICENSE)

Lam Nguyen

[Quick start](#quick-start) ·
[Gate a new version](#gate-a-new-version) ·
[Definitions against axioms](#definitions-against-axioms) ·
[Results](#results) ·
[How it works](#how-it-works)

</div>

OntoVerifier finds what is wrong with an ontology and what a new version changes in meaning. It reasons over OWL, and can back each answer with a Lean proof or a finite model that Lean's kernel checks, so a bug in the reasoner can't become a wrong claim.

## Quick start

Install [Lean](https://github.com/leanprover/elan), then OntoVerifier:

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

git clone https://github.com/lamng3/ontoverifier.git && cd ontoverifier
pip install -e .
lake build

ontoverifier check examples/university.ttl
```

```text
24 axioms translated, 100% of what was read
9 classes, 2 unsatisfiable, 0 out of budget
data: NO
data clash (entailed): 1, kernel accepted
unsatisfiable (entailed): 2, kernel accepted
witness (satisfied): 7, kernel accepted
```

Add `--no-kernel` to use it as a plain reasoner, without Lean.

Or from Python:

```python
from ontoverifier import Axiom, Verifier, load

v = Verifier(load("examples/university.ttl"))    # certify=False is a plain reasoner
ns = "http://example.org/uni#"

print(v.unsatisfiable_classes())

finding = v.judge(Axiom("sub", (ns + "Lecturer", ns + "Person")))
v.finish()                                       # send what was written through the kernel
print(finding.verdict, finding.kernel, finding.because)
```

```text
['http://example.org/uni#Advisor', 'http://example.org/uni#TeachingAssistant']
entailed accepted ['Lecturer ⊑ Staff', 'Staff ⊑ Person']
```

OntoVerifier reads any RDF format (`.owl`, `.ttl`, `.rdf`, …).

## Gate a new version

`gate` compares what two versions mean, names the added axioms behind each problem, and exits with 1 if the new version should not ship:

```bash
ontoverifier gate --old examples/versions/v1.ttl --new examples/versions/v2.ttl
```

```text
BLOCKED
  axioms: +1 -0
  new unsatisfiable classes: 2
  new data clashes: 1
  subsumptions: 0 lost, 0 gained
  theorems: {'accepted': 3}
    Dog ⊑ ⊥ [accepted]
      from the change: ['Mammal ⊑ Plant']
    Mammal ⊑ ⊥ [accepted]
      from the change: ['Mammal ⊑ Plant']
```

| Reported | Evidence | Blocks? |
|:--|:--|:--|
| New unsatisfiable classes | A proof, and the added axioms it rests on | Yes |
| New data clashes | A proof | Yes |
| Lost subsumptions | A proof for the old version, a refuting model for the new one | With `--strict` |
| Gained subsumptions | A proof | No |

`gate` only blocks on what is new, so a problem carried over from the last version does not block again. `check` reports everything. `history v1.ttl v2.ttl v3.ttl` runs each version against the one before it, and a theorem seen before is not checked again, so a new version only pays for what changed.

## Definitions against axioms

A class often says what it means twice, in English and in logic. `comments` has a model read each definition and write the claims it makes, then judges them against the axioms. No API key needed, only [Ollama](https://ollama.com):

```bash
ollama pull llama3.1
ontoverifier comments examples/definitions.ttl --model ollama:llama3.1
```

| Definition | Claim | Result |
|:--|:--|:--|
| A lake is a body of water. | lake ⊑ water | agrees |
| Basalt is a kind of water found in volcanoes. | basalt ⊑ water | contradicts |
| A pond is a small body of water that is fed by a stream. | pond ⊑ ∃fed by.stream | says more |

**This does not verify the English.** The kernel checks the logic of a claim, and nothing checks that the claim is what the definition meant, so a wrong translation looks exactly like a real disagreement. Each finding shows both, for a person to read. The accuracy of these translations on real ontologies has not been measured yet.

## Results

Measured on 2026-11-06. Runs are in [`results/`](results/) or can be rerun from [`experiments/`](experiments/).

| Test | Result |
|:--|:--|
| Random ontologies against [`hermitpy`](https://github.com/lamng3/hermitpy) | Agreed on 3,992 of 3,992 classes across 499 ontologies; `hermitpy` hit its node limit on 1 more |
| Lean's kernel on those answers | 3,992 accepted, 0 rejected |
| ENVO + SWEET + the OAEI reference alignment | Blocked: 6 new unsatisfiable classes, all accepted by the kernel, traced to 2 of the 842 added axioms |
| A bad single edit to SWEET | Blocked in about 5 seconds, with the 1 responsible axiom named |
| The next version, with the bad edit unchanged | Its proof came from the cache, with no new kernel run |

The ENVO merge reads alignment correspondences as strict equivalences, so a clash there may be the alignment's fault.

## How it works

An ontology means the set of all its models, and a Lean theorem quantified over all interpretations says the same thing. A search that is not trusted does the work and writes down what it found.

When something must be true, it writes a proof that takes only the axioms it uses:

```lean
theorem advisor {U : Type}
    (c_Advisor c_Course c_Person : U → Prop)
    (p_teaches : U → U → Prop)
    (h0 : ∀ x, c_Advisor x → ∃ y, p_teaches x y ∧ c_Person y) -- Advisor ⊑ ∃teaches.Person
    (h1 : ∀ x y, p_teaches x y → c_Course y)                  -- ⊤ ⊑ ∀teaches.Course
    (h2 : ∀ x, c_Course x → c_Person x → False)               -- Course ⊓ Person ⊑ ⊥
    : ∀ x, ¬ c_Advisor x := by
  intro x0 s0
  obtain ⟨w1, f1r, f1c⟩ := h0 x0 s0
  have f3 : c_Course w1 := h1 x0 w1 f1r
  exact False.elim (h2 w1 f3 f1c)
```

When something need not be true, it writes a finite model as data. The kernel runs `check` from [`Model.lean`](OntoVerifier/Model.lean), which is proved to mean what the axioms mean:

```lean
theorem check_iff (m : FinModel) (a : Axiom) : check m a = true ↔ a.holds m.interp
```

| Verdict | Meaning | If axioms were skipped |
|:--|:--|:--|
| entailed | The axioms prove it. | Still holds |
| contradiction | With the claim added, the class could have no instance. | Still holds |
| refuted | A model of the axioms where the claim fails. | Holds for the translated fragment only |
| satisfied | A model where the class has an instance. | Holds for the translated fragment only |
| unknown | The search could not settle it. | |

On a finding, `kernel` is `accepted`, `rejected` or `not_run`, and only `accepted` means Lean checked it.

**What is translated:** `subClassOf`, `equivalentClass`, `disjointWith`, `complementOf` of a named class, `AllDisjointClasses`, `domain`, `range`, `subPropertyOf`, `inverseOf`, symmetric and transitive properties, `someValuesFrom` and `allValuesFrom` on named classes, intersections as superclasses, and class and object-property assertions. Everything else, such as cardinality, `unionOf` and literals, is counted and reported.

**What is trusted:** the kernel checks a proof, not the translation. `axioms.py`, `emit.sentence` and `Axiom.holds` say what an ontology means, and each hypothesis carries its description-logic reading so a person can audit it. The search and the model's reading of a definition are not trusted, and a model's output never reaches the Lean compiler as text.

[`Planner.lean`](OntoVerifier/Planner.lean) also proves when a SPARQL selection may cross a join, the condition behind a fix to join reordering in [Hermes](https://github.com/lamng3/hermes). It proves this for a model of SPARQL, not for Hermes's Python.

## License

[BSD 3-Clause](LICENSE)
