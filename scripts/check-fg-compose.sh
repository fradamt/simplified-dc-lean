#!/usr/bin/env bash
# Build and audit every Compose source. The facade does not select the scope.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
gate_options "$@"
python3 -B scripts/check-fg-compose-source.py
targets=$(lake env lean --run scripts/CheckGenFirst.lean --libraries)
gate_build --wfail AvailableChainFGCompose $targets
expected=$(python3 -B scripts/check_inventory.py scripts/fg-compose-expected.txt)
lake env lean --run scripts/CheckFGAxioms.lean --compose --expect $expected
bash scripts/check-fg-syntax.sh
if [ "$NEG" = 1 ]; then
  python3 -B scripts/check-fg-compose-controls.py
fi
