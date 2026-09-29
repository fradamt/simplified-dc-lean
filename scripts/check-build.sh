#!/usr/bin/env bash
# The mechanical build checks of BUILD §7.3, (a)–(i), in order:
#   (a) check-module-headers.py   (b) check-expose.py
#   (c) rebuild-cone-test.sh <CONE_MODULE> (default
#       AvailableChainGridCO.Proofs.Map; a throwaway copy and one Lean build)
#   (d) CheckProofEqns.lean       (e) check-layers.py
#   (f) shake-report.sh (REPORT only; never fails the run unless it cannot run)
#   (g) chain-depth.py (REPORT only) (h) check-transparency.py
#   (i) check-gly-rules.sh
# (d) and (e) run when their script exists; else "SKIPPED: not yet present".
# SKIP_CONE=1 skips (c) (it needs a built tree and a Lean build).
# Every check runs; the summary lists each result. Exit 0: every check that
# ran passed; 1: a check failed.
set -uo pipefail
cd "$(dirname "$0")/.."
CONE_MODULE=${CONE_MODULE:-AvailableChainGridCO.Proofs.Map}
RESULTS=(); FAILED=0
run() {  # run <id> <name> <command...>
  local id=$1 name=$2; shift 2
  echo "=== ($id) $name"
  "$@"; local rc=$?
  if [ $rc -eq 0 ]; then RESULTS+=("($id) $name: PASS"); else RESULTS+=("($id) $name: FAIL (rc $rc)"); FAILED=1; fi
}
skip() { echo "=== ($1) $2"; echo "SKIPPED: $3"; RESULTS+=("($1) $2: SKIPPED: $3"); }

run a check-module-headers python3 scripts/check-module-headers.py
run b check-expose python3 scripts/check-expose.py
if [ "${SKIP_CONE:-0}" = 1 ]; then skip c rebuild-cone-test "SKIP_CONE=1"
else run c "rebuild-cone-test $CONE_MODULE" bash scripts/rebuild-cone-test.sh "$CONE_MODULE"; fi
if [ -f scripts/CheckProofEqns.lean ]; then
  run d CheckProofEqns bash -c 'lake build AvailableChainCheckSupport && lake env lean --run scripts/CheckProofEqns.lean --baseline scripts/baselines/check-proof-eqns.txt'
else skip d CheckProofEqns "not yet present"; fi
if [ -f scripts/check-layers.py ]; then run e check-layers python3 scripts/check-layers.py
else skip e check-layers "not yet present"; fi
echo "=== (f) shake-report"
if bash scripts/shake-report.sh; then RESULTS+=("(f) shake-report: REPORT"); else RESULTS+=("(f) shake-report: FAIL (could not run)"); FAILED=1; fi
echo "=== (g) chain-depth"
if python3 scripts/chain-depth.py; then RESULTS+=("(g) chain-depth: REPORT"); else RESULTS+=("(g) chain-depth: FAIL (could not run)"); FAILED=1; fi
run h check-transparency python3 scripts/check-transparency.py
run i check-gly-rules bash scripts/check-gly-rules.sh
echo "=== summary"
printf '%s\n' "${RESULTS[@]}"
[ $FAILED -eq 0 ] && echo "check-build: PASS" || echo "check-build: FAIL"
exit $FAILED
