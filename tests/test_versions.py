"""What a new version changes in meaning."""

import pytest

from ontoverifier import lean, load, versions

needs_lean = pytest.mark.skipif(not lean.available(), reason="lean is not installed")
HEAD = """
@prefix : <http://example.org/v#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
"""
V1 = HEAD + """
:Animal a owl:Class .
:Plant a owl:Class ; owl:disjointWith :Animal .
:Dog a owl:Class ; rdfs:subClassOf :Mammal .
:Mammal a owl:Class ; rdfs:subClassOf :Animal .
:Oak a owl:Class ; rdfs:subClassOf :Plant .
:rex a :Dog .
"""


def theory(tmp_path, name, text):
    path = tmp_path / f"{name}.ttl"
    path.write_text(text)
    return load(path)


def compare(tmp_path, text, **kwargs):
    return versions.compare(theory(tmp_path, "v1", V1), theory(tmp_path, "v2", text),
                            tmp_path / "out", cache=False, **kwargs)


def test_no_change_is_no_change(tmp_path):
    change = compare(tmp_path, V1, certify=False)
    assert not change.added and not change.removed and not change.blocked(strict=True)
    assert change.lost_total == change.gained_total == 0


def test_an_edit_that_breaks_a_class_blocks_and_is_blamed(tmp_path):
    change = compare(tmp_path, V1 + ":Dog rdfs:subClassOf :Plant .\n", certify=False)
    assert change.blocked()
    assert [i["subject"].split("#")[1] for i in change.new_unsatisfiable] == ["Dog"]
    assert change.new_unsatisfiable[0]["added_axioms_used"] == ["Dog ⊑ Plant"]


def test_an_edit_that_breaks_data_blocks(tmp_path):
    change = compare(tmp_path, V1 + ":rex a :Oak .\n", certify=False)
    assert change.blocked() and len(change.new_clashes) == 1
    assert change.new_clashes[0]["added_axioms_used"] == []  # it was a fact, not an axiom used


def test_a_removed_axiom_loses_what_followed_from_it(tmp_path):
    change = compare(tmp_path, V1.replace(":Dog a owl:Class ; rdfs:subClassOf :Mammal .",
                                          ":Dog a owl:Class ."), certify=False)
    lost = {item["claim"] for item in change.lost}
    assert lost == {"Dog ⊑ Mammal", "Dog ⊑ Animal"}
    assert not change.blocked() and change.blocked(strict=True)


def test_gained_facts_are_reported(tmp_path):
    change = compare(tmp_path, V1 + ":Oak rdfs:subClassOf :Tree .\n:Tree a owl:Class .\n",
                     certify=False)
    assert change.gained_total == 1 and not change.blocked(strict=True)


def test_history_goes_version_by_version(tmp_path):
    steps = versions.history([theory(tmp_path, "a", V1),
                              theory(tmp_path, "b", V1 + ":Dog rdfs:subClassOf :Plant .\n"),
                              theory(tmp_path, "c", V1)], tmp_path / "out", certify=False)
    assert [s.blocked() for s in steps] == [True, False]
    assert len(steps[1].resolved_unsatisfiable) == 1


@needs_lean
def test_the_kernel_backs_every_part_of_a_comparison(tmp_path):
    text = V1.replace(":Dog a owl:Class ; rdfs:subClassOf :Mammal .", ":Dog a owl:Class .") \
        + ":Oak rdfs:subClassOf :Animal .\n"
    change = compare(tmp_path, text)
    assert set(change.kernel) == {"accepted"}, change.kernel
    assert change.new_unsatisfiable[0]["kernel"] == "accepted"
    assert change.lost[0]["old"]["kernel"] == "accepted"
    assert change.lost[0]["new"]["verdict"] == "refuted"
    assert change.lost[0]["new"]["kernel"] == "accepted"


@needs_lean
def test_a_proof_carries_over_to_the_next_version(tmp_path, monkeypatch):
    cache = tmp_path / "cache.json"
    monkeypatch.setattr(lean, "CACHE", cache)
    monkeypatch.setattr(lean.Cache.__init__, "__defaults__", (cache,))
    broken = V1 + ":Dog rdfs:subClassOf :Plant .\n"
    first = versions.compare(theory(tmp_path, "a", V1), theory(tmp_path, "b", broken),
                             tmp_path / "one")
    assert first.new_unsatisfiable[0]["kernel"] == "accepted"
    later = theory(tmp_path, "c", broken + ":Cat a owl:Class .\n")
    second = versions.compare(theory(tmp_path, "b2", broken), later, tmp_path / "two")
    assert second.kernel.get("cached", 0) >= 1


