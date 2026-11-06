"""The Verifier, through Lean's kernel when Lean is there. Every claim must survive it."""

import json
from pathlib import Path

import pytest

from ontoverifier import Axiom, Search, Verifier, emit, lean, load, models

EXAMPLE = Path(__file__).parent.parent / "examples" / "university.ttl"
NS = "http://example.org/uni#"
needs_lean = pytest.mark.skipif(not lean.available(), reason="lean is not installed")


@pytest.fixture(scope="module")
def theory():
    return load(EXAMPLE)


def verifier(theory, tmp_path, certify=True):
    return Verifier(theory, tmp_path, certify, cache=False)


def sub(a, b):
    return Axiom("sub", (NS + a, NS + b))


# The search.


def test_a_subclass_chain_into_disjoint_classes_clashes(theory):
    assert Search(theory).class_(NS + "TeachingAssistant").clash


def test_a_clash_can_sit_behind_a_restriction_and_a_range(theory):
    outcome = Search(theory).class_(NS + "Advisor")
    kinds = {step.axiom.kind for step in outcome.slice() if step.axiom}
    assert {"some", "range"} <= kinds


@pytest.mark.parametrize("name", ["Person", "Student", "Lecturer", "Instructor", "Seminar"])
def test_satisfiable_classes_do_not_clash(theory, name):
    assert not Search(theory).class_(NS + name).clash


def test_data_clash_is_found_through_domains(theory):
    assert {c[1][1] for c in Search(theory).abox().clashes} == {NS + "bob"}


def test_a_proof_uses_only_the_axioms_it_needs(theory):
    outcome = Search(theory).class_(NS + "TeachingAssistant")
    assert len(emit.Proof(outcome).axioms) < theory.translated / 3
    text = emit.unsat_class(outcome, NS + "TeachingAssistant", "t")
    assert "c_Course" not in text and "sorry" not in text


def test_a_witness_needs_a_second_element_for_an_existential(theory):
    outcome = Search(theory).class_(NS + "Instructor")
    model = models.build(outcome, theory)
    assert len({x for _, x in model.classes}) == 2
    assert all(models.holds(model, a) for a in theory.terminology)


def test_the_same_ontology_writes_the_same_proofs(theory, tmp_path):
    def written():
        one = load(EXAMPLE)
        outcome = Search(one).class_(NS + "Advisor")
        return emit.unsat_class(outcome, NS + "Advisor", "t")

    assert written() == written()


# The reasoner, without Lean.


def test_the_reasoner_needs_no_kernel(theory, tmp_path):
    v = verifier(theory, tmp_path, certify=False)
    assert v.unsatisfiable_classes() == [NS + "Advisor", NS + "TeachingAssistant"]
    assert not v.is_consistent()
    assert (NS + "Staff") in v.hierarchy()[NS + "Lecturer"]
    assert (NS + "Lecturer", NS + "Staff") in v.direct_subclasses()
    assert (NS + "Lecturer", NS + "Person") not in v.direct_subclasses()


def test_nothing_is_accepted_without_the_kernel(theory, tmp_path):
    report = verifier(theory, tmp_path, certify=False).check()
    named = [f for f in report["findings"] if f["name"]]
    assert named and {f["kernel"] for f in named} == {"not_run"}


# Claims.


@pytest.mark.parametrize("claim,verdict", [
    (sub("Lecturer", "Person"), "entailed"),
    (Axiom("disjoint", (NS + "Lecturer", NS + "Student")), "entailed"),
    (Axiom("some", (NS + "Instructor", NS + "teaches", NS + "Course")), "entailed"),
    (Axiom("all", (NS + "Staff", NS + "teaches", NS + "Course")), "entailed"),
    (sub("Person", "Student"), "refuted"),
    (Axiom("disjoint", (NS + "Person", NS + "Student")), "contradiction"),
    (sub("Student", "Staff"), "contradiction"),
    (Axiom("some", (NS + "Person", NS + "teaches", NS + "Course")), "refuted"),
    (Axiom("all", (NS + "Person", NS + "enrolledIn", NS + "Seminar")), "refuted"),
])
def test_a_claim_is_judged(theory, tmp_path, claim, verdict):
    finding = verifier(theory, tmp_path, certify=False).judge(claim)
    assert finding.verdict == verdict


@needs_lean
def test_the_kernel_accepts_every_claim(theory, tmp_path):
    v = verifier(theory, tmp_path)
    claims = [
        sub("Lecturer", "Person"), Axiom("disjoint", (NS + "Lecturer", NS + "Student")),
        Axiom("some", (NS + "Instructor", NS + "teaches", NS + "Course")),
        Axiom("all", (NS + "Staff", NS + "teaches", NS + "Course")),
        sub("Person", "Student"), sub("Student", "Staff"),
        Axiom("disjoint", (NS + "Person", NS + "Student")),
        sub("TeachingAssistant", "Course"),  # vacuous: the class cannot exist
    ]
    findings = [v.judge(c) for c in claims]
    v.finish()
    assert {f.kernel for f in findings} == {"accepted"}, [(f.claim, f.detail) for f in findings]
    assert findings[-1].vacuous


@needs_lean
def test_the_kernel_accepts_a_whole_check(theory, tmp_path):
    report = verifier(theory, tmp_path).check()
    named = [f for f in report["findings"] if f["name"]]
    assert {f["kernel"] for f in named} == {"accepted"}, named
    kinds = {f["kind"] for f in named}
    assert {"unsatisfiable", "data clash", "witness"} <= kinds


@needs_lean
def test_a_consistent_ontology_with_data_gets_a_model(tmp_path):
    path = tmp_path / "ok.ttl"
    path.write_text(EXAMPLE.read_text().replace(":bob :teaches :logic ; :enrolledIn :logic .", ""))
    v = verifier(load(path), tmp_path / "out")
    v.prove_data()
    v.finish()
    assert [f.kernel for f in v.findings if f.kind == "consistent"] == ["accepted"]


@needs_lean
def test_the_kernel_rejects_a_false_proof(tmp_path):
    batch = lean.Batch(tmp_path / "bad.lean")
    batch.add("bad", "theorem bad (A B : Nat → Prop) (h : ∀ x, A x → B x) : ∀ x, B x → A x := by\n"
                     "  intro x hb\n  exact h x hb\n")
    assert batch.run()["bad"].kernel == "rejected"


@needs_lean
def test_the_kernel_rejects_a_sorry(tmp_path):
    batch = lean.Batch(tmp_path / "bad.lean")
    batch.add("bad", "theorem bad : 1 = 2 := by sorry\n")
    assert batch.run()["bad"].kernel == "rejected"


@needs_lean
def test_the_kernel_rejects_a_model_that_does_not_fit(theory, tmp_path):
    table = models.Theorems(theory.terminology)
    wrong = models.Model(classes={(NS + "Lecturer", 0)})  # Lecturer ⊑ Staff fails here
    batch = lean.Batch(tmp_path / "bad.lean", "", None)
    batch.add("bad", table.refutes("bad", wrong, sub("Person", "Student")))
    batch.prelude = table.prelude()
    assert batch.run()["bad"].kernel == "rejected"


@needs_lean
def test_one_bad_theorem_does_not_condemn_the_rest(tmp_path):
    batch = lean.Batch(tmp_path / "mixed.lean")
    batch.add("good1", "theorem good1 : 1 + 1 = 2 := rfl\n")
    batch.add("bad", "theorem bad : 1 + 1 = 3 := rfl\n")
    batch.add("good2", "theorem good2 : 2 + 2 = 4 := rfl\n")
    results = batch.run()
    assert {n: r.kernel for n, r in results.items()} == {
        "good1": "accepted", "bad": "rejected", "good2": "accepted"}


@needs_lean
def test_a_theorem_seen_before_is_not_checked_again(tmp_path):
    cache = lean.Cache(tmp_path / "cache.json")
    first = lean.Batch(tmp_path / "a.lean", cache=cache)
    first.add("t", "theorem t : 1 + 1 = 2 := rfl\n")
    assert not first.run()["t"].cached
    second = lean.Batch(tmp_path / "b.lean", cache=lean.Cache(tmp_path / "cache.json"))
    second.add("t", "theorem t : 1 + 1 = 2 := rfl\n")
    assert second.run()["t"].cached


# Queries.


def test_a_query_with_optional_is_refused(theory, tmp_path):
    finding = verifier(theory, tmp_path, False).query(
        f"SELECT ?x WHERE {{ ?x a <{NS}Course> OPTIONAL {{ ?x <{NS}teaches> ?y }} }}")
    assert finding.verdict == "unknown" and "LeftJoin" in finding.detail


@needs_lean
def test_a_query_that_can_have_no_answers_is_proved_empty(theory, tmp_path):
    v = verifier(theory, tmp_path)
    finding = v.query(f"SELECT ?x ?y WHERE {{ ?x a <{NS}Course> . ?x <{NS}teaches> ?y }}")
    v.finish()
    assert finding.verdict == "entailed" and finding.kernel == "accepted", finding.detail


def test_a_query_that_could_have_answers_is_not_called_empty(theory, tmp_path):
    finding = verifier(theory, tmp_path, False).query(
        f"SELECT ?x ?y WHERE {{ ?x a <{NS}Staff> . ?x <{NS}teaches> ?y }}")
    assert finding.verdict == "no_clash"


def test_results_are_json(theory, tmp_path):
    json.dumps(verifier(theory, tmp_path, False).check())


def test_many_individuals_do_not_use_up_the_budget(tmp_path):
    from ontoverifier.axioms import Theory
    theory = Theory()
    theory.classes = {NS + "A"}
    for i in range(50):
        theory.add("type", f"{NS}i{i}", NS + "A")
    v = Verifier(theory, tmp_path, certify=False, max_nodes=10, cache=False)
    assert v.is_consistent() is True


def test_running_out_of_budget_on_data_is_not_called_consistent(tmp_path):
    from ontoverifier.axioms import Theory
    theory = Theory()
    theory.classes = {NS + "A", NS + "B"}
    theory.add("some", NS + "A", NS + "p", NS + "B")
    theory.add("some", NS + "B", NS + "q", NS + "A")
    theory.add("all", NS + "B", NS + "q", NS + "C")
    theory.add("some", NS + "C", NS + "r", NS + "D")
    theory.add("type", NS + "i", NS + "A")
    v = Verifier(theory, tmp_path, certify=False, max_nodes=1, cache=False)
    assert v.is_consistent() is None


@needs_lean
def test_the_kernel_rejects_a_mask_that_hides_part_of_the_model(theory, tmp_path):
    """Here the mask would hide the fact that Lecturer ⊑ Staff fails, if it were believed."""
    table = models.Theorems(theory.terminology)
    wrong = models.Model(classes={(NS + "Lecturer", 0)})
    claim = sub("Person", "Student")
    written = table.refutes("bad", wrong, claim)
    lying = written.replace(table.mask(wrong), "0x0")
    assert lying != written
    batch = lean.Batch(tmp_path / "bad.lean", "", None)
    batch.add("bad", lying)
    batch.prelude = table.prelude()
    assert batch.run()["bad"].kernel == "rejected"


@needs_lean
def test_a_timeout_is_not_called_a_rejection(tmp_path):
    batch = lean.Batch(tmp_path / "slow.lean")
    batch.add("t", "theorem t : 1 + 1 = 2 := rfl\n")
    assert batch.run(timeout=0.001)["t"].kernel == "not_run"
