"""Prove things about ontologies: an untrusted search writes the proofs, Lean checks them."""

from ontoverifier.axioms import Axiom, Theory, load
from ontoverifier.search import Search
from ontoverifier.verifier import Finding, Verifier

__all__ = ["Axiom", "Finding", "Search", "Theory", "Verifier", "load"]
