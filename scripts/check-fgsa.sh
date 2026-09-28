#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the import rules (direct and closure), the Q1/Q5 boundary grep,
# and (once present) the axiom check.
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== lake build --wfail AvailableChainFGSA"
lake build --wfail AvailableChainFGSA
echo "== root imports"
missing=$(comm -23 \
  <(find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) \
  <(grep -o 'import [A-Za-z.]*' AvailableChainFGSA.lean | sed 's/import //' | sort))
[ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; exit 2; }
echo "== native evaluation"
status=0
for f in $(find AvailableChainFGSA -name '*.lean') AvailableChainFGSA.lean; do
  if perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== direct imports"
if grep -rnE '^(public )?import (AvailableChainFramework|AvailableChainRegistry|AvailableChainStatements|AvailableChainWitnesses|AvailableChainSAPC)' \
    AvailableChainFGSA AvailableChainFGSA.lean; then
  echo "FORBIDDEN DIRECT IMPORT"; exit 1
fi
echo "== import closure"
seen=" "
todo=$(grep -rhoE '^(public )?import [A-Za-z0-9_.]+' AvailableChainFGSA AvailableChainFGSA.lean | awk '{print $NF}' | sort -u)
while [ -n "$todo" ]; do
  next=""
  for m in $todo; do
    case "$seen" in *" $m "*) continue ;; esac
    seen="$seen$m "
    f="${m//.//}.lean"
    if [ -f "$f" ]; then
      next="$next $(grep -hoE '^(public )?import [A-Za-z0-9_.]+' "$f" | awk '{print $NF}')"
    fi
  done
  todo=$next
done
if echo "$seen" | tr ' ' '\n' | grep -E '^AvailableChain(Framework|Registry|SAPC|Witnesses)(\.|$)'; then
  echo "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE"; exit 1
fi
echo "== Q1/Q5 boundary"
if grep -rnE 'ProtocolSpec|Generic\.Run|World|pendingRow' AvailableChainFGSA AvailableChainFGSA.lean; then
  echo "ENGINE REFERENCE"; exit 1
fi
if [ -f scripts/CheckFGSAAxioms.lean ]; then
  echo "== axioms"
  lake env lean --run scripts/CheckFGSAAxioms.lean
fi
echo "all FGSA checks pass"
