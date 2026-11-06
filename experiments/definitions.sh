#!/bin/sh
# Read the ENVO definitions with the model, on your machine and without the kernel, which
# is light. Answers are cached under results/, so a rerun asks nothing. The kernel work is
# heavy and runs on Modal: see experiments/modal_definitions.py.
set -u
ENVO=../agentic-ontologist/data/BioDiv/envo-sweet/envo.owl
SONNET='command:claude -p --model claude-sonnet-5-5 --tools "" --no-session-persistence --setting-sources ""'
PY="${PY:-python}"
nice -n 10 $PY -m ontoverifier.cli comments "$ENVO" --model "$SONNET" --no-kernel --limit 60 --seed 1 --out results/envo-definitions/sonnet
nice -n 10 $PY -m ontoverifier.cli comments "$ENVO" --model "$SONNET" --no-kernel --near-disjoint --limit 80 --seed 1 --out results/envo-definitions/sonnet-near-disjoint
