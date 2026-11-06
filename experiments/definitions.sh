#!/bin/sh
# Definitions against axioms on ENVO: the same seeded sample on two models, then the
# classes that can contradict. Answers are cached under results/, so a rerun asks nothing.
set -u
ENVO=../agentic-ontologist/data/BioDiv/envo-sweet/envo.owl
SONNET='command:claude -p --model claude-sonnet-5-5 --tools "" --no-session-persistence --setting-sources ""'
PY="${PY:-python}"
$PY -m ontoverifier.cli comments "$ENVO" --model "$SONNET" --limit 60 --seed 1 --out results/envo-definitions/sonnet
$PY -m ontoverifier.cli comments "$ENVO" --model "$SONNET" --near-disjoint --limit 80 --seed 1 --out results/envo-definitions/sonnet-near-disjoint
$PY -m ontoverifier.cli comments "$ENVO" --model ollama:llama3.1-32k --limit 60 --seed 1 --out results/envo-definitions/llama3.1
