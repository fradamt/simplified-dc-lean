#!/usr/bin/env bash
# All FG checks in one run. It builds the two FG libraries once (under --wfail),
# then runs the root-import check, the syntax check, the axiom check, the
# pinned-name check and the pin check, and stops at the first failure. The Lean
# checks read the built .olean files, which Lean does not compare with the
# sources, so they must run after the build. Run: bash scripts/check-fg.sh.
# Exit codes: 0 all checks pass; otherwise the exit code of the failed step.
set -euo pipefail
cd "$(dirname "$0")/.."
step() { echo "== $1"; }
step "lake build --wfail AvailableChainSimplexFG AvailableChainKitFG"
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake build --wfail AvailableChainSimplexFG AvailableChainKitFG >"$log" 2>&1 ||
  { rc=$?; echo "BUILD FAILED"; tail -30 "$log"; exit $rc; }
step "root imports"
missing=$(comm -23 \
  <(ls AvailableChainKitFG/*.lean AvailableChainSimplexFG/*.lean |
    sed 's/\.lean$//; s|/|.|g' | sort) \
  <(grep -ho 'import [A-Za-z.]*' AvailableChainKitFG.lean AvailableChainSimplexFG.lean |
    sed 's/import //' | sort))
[ -z "$missing" ] || { echo "NOT IMPORTED BY A LIBRARY ROOT: $missing"; exit 2; }
step "scripts/check-fg-syntax.sh"
bash scripts/check-fg-syntax.sh
step "scripts/CheckFGAxioms.lean"
lake env lean --run scripts/CheckFGAxioms.lean
step "scripts/FGPinIds.lean --check-names"
lake env lean --run scripts/FGPinIds.lean --check-names
step "scripts/check-fg-pins.sh"
bash scripts/check-fg-pins.sh
echo "all FG checks pass"
