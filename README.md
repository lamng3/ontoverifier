# OntoVerifier

A reasoner for OWL ontologies whose answers can each be checked by Lean's kernel, built for ontologies that change.

- **Reason:** which classes can have instances, what the hierarchy is, whether the data fits.
- **Prove:** each answer can come with a Lean proof or a finite model.
- **Gate a new version:** what changed in meaning, which added axioms caused it, and whether to block it.
- **Compare words with axioms:** do a class's definition and its axioms say the same thing?

## Quick start

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
pip install -e ".[dev]"
lake build
```

```bash
ontoverifier check examples/university.ttl             # reason and prove
ontoverifier check examples/university.ttl --no-kernel # reason only
ontoverifier gate --old v1.ttl --new v2.ttl            # exit 1 if v2 breaks something
ontoverifier history v1.ttl v2.ttl v3.ttl              # each version against the last
ontoverifier entails onto.ttl --claim sub http://ex.org/A http://ex.org/B
ontoverifier query onto.ttl --sparql q.rq              # must this query be empty?
ontoverifier comments onto.ttl --model ollama:llama3.1 # definitions against axioms
```

```python
from ontoverifier import Axiom, Verifier, load

v = Verifier(load("onto.ttl"), certify=True)   # certify=False is a plain reasoner
print(v.unsatisfiable_classes(), v.direct_subclasses())
finding = v.judge(Axiom("sub", ("http://ex.org/A", "http://ex.org/B")))
v.finish()                                     # send what was written through the kernel
print(finding.verdict, finding.kernel, finding.because)
```

## How it works

OWL is first-order logic, and an ontology means the set of all its models. A Lean theorem quantified over all interpretations says the same thing, so the open-world assumption needs no special handling.

A search that is not trusted does the work, and writes down what it found in one of two forms.

**A proof, when something must be true.** It is written out step by step, with only the axioms it uses as hypotheses:

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

**A finite model, when something need not be true.** It is written as data, and the kernel runs `check` from [`OntoVerifier/Model.lean`](OntoVerifier/Model.lean), which is proved correct:

```lean
theorem check_iff (m : FinModel) (a : Axiom) : check m a = true ↔ a.holds m.interp
```

Four choices follow:

- **Axioms are hypotheses, never Lean `axiom`s.** An inconsistent ontology can't make Lean itself unsound.
- **A proof takes only the axioms it uses.** Adding axioms keeps a proof valid, so it also holds for the whole ontology and for every later version that still has those axioms.
- **Search bugs can't become claims.** Lean rejects anything wrong, and `#print axioms` must show only Lean's three standard axioms. That rules out `sorry` and trusting compiled code.
- **Lean only sees text this program wrote.** A Lean file can run code when it compiles, so model output never reaches the compiler.

## Verdicts

| Verdict | Lean statement | Meaning | If axioms were skipped |
|:--|:--|:--|:--|
| entailed | the claim itself | The axioms prove it. | Still holds |
| contradiction | the claim as a hypothesis, then `∀ x, ¬ C x` | With the claim added, `C` could have no instance. | Still holds |
| refuted | `¬ Entails T claim` | A model of the axioms where the claim fails. | Holds for the translated fragment only |
| satisfied | `∃ U I, Models I T ∧ …` | A model where the class has an instance. | Holds for the translated fragment only |
| unknown | none | The search could not settle it. | |

`kernel` on a finding is `accepted`, `rejected`, or `not_run`. Only `accepted` means Lean checked it.

## Versions

`ontoverifier gate` compares what two versions mean:

| Reported | Evidence | Blocks? |
|:--|:--|:--|
| New unsatisfiable classes | A proof, and the added axioms it rests on | Yes |
| New data clashes | A proof | Yes |
| Lost subsumptions | A proof for the old version, a refuting model for the new one | With `--strict` |
| Gained subsumptions | A proof | No |

Each theorem is checked once. The same text under the same toolchain is never checked again, so a new version only pays for what changed.

## Definitions against axioms

A class often says what it means twice: in English and in logic. `ontoverifier comments` has a model read each definition and write the claims it makes, then judges them:

| Result | Meaning |
|:--|:--|
| agrees | The axioms prove the claim. |
| contradicts | With the claim added, the class could have no instance. |
| says more | A model of the axioms where the claim fails, so the definition states something the axioms don't. |

**This does not verify the English.** The kernel checks the logic of a claim, and nothing checks that the claim is what the definition meant. A wrong translation looks exactly like a real disagreement, so every finding shows both for a person to read. The model picks terms by handle from a short list and a claim from four fixed shapes.

## Results

Measured on 2026-11-06. Each run is in [`results/`](results/) or can be rerun from [`experiments/`](experiments/).

| Test | Result |
|:--|:--|
| Random ontologies against `hermitpy` | Agreed on 3,992 of 3,992 classes across 499 ontologies; `hermitpy` hit its node limit on 1 more |
| Lean's kernel on those answers | 3,992 accepted, 0 rejected |
| ENVO + SWEET + the OAEI reference alignment | Blocked: 6 new unsatisfiable classes, all accepted by the kernel, traced to 2 of the 842 added axioms |
| A bad single edit to SWEET | Blocked in about 5 seconds, with the 1 responsible axiom named |
| The next version, with the bad edit unchanged | The proof came from the cache, with no new kernel run |

The ENVO merge treats alignment correspondences as strict equivalences, so a clash there may be the alignment's fault. The gate only blocks on what is new, so a problem carried over from the previous version does not block again; use `check` for the whole ontology.

Definitions against axioms has run on ENVO, but its output has not been reviewed yet, so there is no result to report.

## Fragment

Translated: `subClassOf`, `equivalentClass`, `disjointWith`, `complementOf` of a named class, `AllDisjointClasses`, `domain`, `range`, `subPropertyOf`, `inverseOf`, symmetric and transitive properties, `someValuesFrom` and `allValuesFrom` on named classes, intersections as superclasses, and class and object-property assertions.

Counted and reported, but not translated: cardinality, `hasValue`, `unionOf`, complex fillers, `sameAs`, `differentFrom`, functional properties and literals. Queries are limited to basic graph patterns.

The fragment has no disjunction, so the search does not branch. Classes that run past the search's budget are reported as out of budget.

## What is trusted

The kernel checks the proof, not the translation. These are trusted:

- `src/ontoverifier/axioms.py` and `emit.sentence`, which say what an ontology means. Each hypothesis carries its description-logic reading so a person can audit it.
- `Axiom.holds` in `OntoVerifier/Model.lean`, which defines the meaning of the fragment.
- Lean's kernel.

Search, proof writing, models and the model's reading of a definition are not trusted.

## Planner proofs

[`OntoVerifier/Planner.lean`](OntoVerifier/Planner.lean) models SPARQL solutions with unbound variables and proves when a selection may cross a join, with a counterexample showing the condition can't be dropped. This is the condition behind a fix to the [Hermes](https://github.com/lamng3/hermes) join reordering. It proves things about the model, not about Hermes's Python.
