"""Definitions against axioms. The model is scripted here; the judging is real."""

import re
from pathlib import Path

import pytest

from ontoverifier import Axiom, language, lean, load

EXAMPLE = Path(__file__).parent.parent / "examples" / "definitions.ttl"
NS = "http://example.org/lang#"
needs_lean = pytest.mark.skipif(not lean.available(), reason="lean is not installed")


class Scripted:
    """Answers with the handle of the term the script names."""

    name = "scripted"

    def __init__(self, script):
        self.script = script

    def complete(self, system, prompt):
        lines = {m.group(2): m.group(1)
                 for m in re.finditer(r"^([TP]\d+) = (.*)$", prompt, flags=re.M)}
        for needle, answer in self.script.items():
            if needle in prompt.split("Definition:")[1].splitlines()[0]:
                return answer(lines)
        return '{"claims": []}'


SCRIPT = {
    "body of water.": lambda t: f'{{"claims": [{{"kind": "sub", "super": "{t["water"]}"}}]}}',
    "kind of water": lambda t: f'{{"claims": [{{"kind": "sub", "super": "{t["water"]}"}}]}}',
    "fed by": lambda t: f'{{"claims": [{{"kind": "some", "prop": "{t["fed by"]}", '
                        f'"filler": "{t["stream"]}"}}]}}',
}


@pytest.fixture(scope="module")
def theory():
    return load(EXAMPLE)


def verdicts(summary):
    return {r["label"]: [c["verdict"] for c in r["claims"]] for r in summary["readings"]}


def test_candidates_come_from_the_words_of_the_definition(theory):
    classes, _ = language.candidates(theory, NS + "Lake", "A lake is a body of water.")
    assert NS + "Water" in classes and NS + "Lake" not in classes


def test_the_three_verdicts(theory, tmp_path):
    summary, _ = language.read_definitions(theory, Scripted(SCRIPT), tmp_path, certify=False)
    found = verdicts(summary)
    assert found["lake"] == ["agrees"]
    assert found["basalt"] == ["contradicts"]
    assert found["pond"] == ["says more"]


@needs_lean
def test_the_kernel_backs_the_three_verdicts(theory, tmp_path):
    summary, _ = language.read_definitions(theory, Scripted(SCRIPT), tmp_path, certify=True)
    found = verdicts(summary)
    assert found["lake"] == ["agrees"]
    assert found["basalt"] == ["contradicts"]
    assert found["pond"] == ["says more"]
    claims = [c for r in summary["readings"] for c in r["claims"]]
    assert {c["kernel"] for c in claims} == {"accepted"}, claims


@pytest.mark.parametrize("answer", [
    "not json at all",
    '{"claims": "none"}',
    '{"claims": [{"kind": "sub", "super": "T99"}]}',
    '{"claims": [{"kind": "sub", "super": "<http://evil>"}]}',
    '{"claims": [{"kind": "theorem", "lean": "#eval IO.Process.spawn"}]}',
    '{"claims": [{"kind": "sub", "super": "P1"}]}',
    '{"claims": [{"kind": "sub", "super": "T0"}]}',
])
def test_an_answer_off_the_fixed_shapes_is_set_aside(answer):
    claims, invalid = language.parse_claims(answer, {"T0": "s", "T1": "a", "P1": "p"}, "s")
    assert not claims and invalid


def test_a_good_answer_is_read():
    claims, invalid = language.parse_claims(
        'Sure! {"claims": [{"kind": "sub", "super": "T1"}, '
        '{"kind": "some", "prop": "P1", "filler": "T1"}]}',
        {"T0": "s", "T1": "a", "P1": "p"}, "s")
    assert claims == [Axiom("sub", ("s", "a")), Axiom("some", ("s", "p", "a"))] and not invalid


def test_nothing_the_model_writes_reaches_lean_as_text(theory, tmp_path):
    evil = 'import Lean #eval IO.Process.spawn'
    script = {"body of water.": lambda t: (
        f'{{"claims": [{{"kind": "sub", "super": "{t["water"]}", "note": "{evil}"}}]}}')}
    language.read_definitions(theory, Scripted(script), tmp_path, certify=False)
    written = "".join(p.read_text() for p in tmp_path.glob("*.lean"))
    assert "IO.Process" not in written


def test_a_failing_model_does_not_end_the_run(theory, tmp_path):
    class Broken:
        name = "broken"

        def complete(self, system, prompt):
            raise RuntimeError("down")

    summary, _ = language.read_definitions(theory, Broken(), tmp_path, certify=False)
    assert summary["errors"] == summary["definitions"] > 0


def test_answers_are_replayed(tmp_path):
    class Once:
        name = "once"
        calls = 0

        def complete(self, system, prompt):
            Once.calls += 1
            return "{}"

    cached = language.Cached(Once(), tmp_path / "answers.json")
    cached.complete("s", "p")
    language.Cached(Once(), tmp_path / "answers.json").complete("s", "p")
    assert Once.calls == 1


def test_a_property_nobody_can_read_is_not_offered(tmp_path):
    path = tmp_path / "t.ttl"
    path.write_text("""
@prefix : <http://purl.obolibrary.org/obo/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
:BFO_0000050 a owl:ObjectProperty .
:ZZZ_0000001 a owl:ObjectProperty .
:A a owl:Class .
""")
    theory = load(path)
    _, properties = language.candidates(theory, ":A", "anything")
    assert [theory.label(p) for p in properties] == ["part of"]
