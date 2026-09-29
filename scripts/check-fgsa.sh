#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the import rules (direct and closure), the Q1/Q5 boundary grep,
# the axiom check, and the lease-instance check with a negative control.
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== lake build --wfail AvailableChainFGSA"
lake build --wfail AvailableChainFGSA
echo "== root imports"
missing=$(comm -23 \
  <(find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) \
  <( (grep -hoE '^[[:space:]]*(public )?(meta )?import (all )?[A-Za-z0-9_.]+' AvailableChainFGSA.lean || true) | awk '{print $NF}' | sort))
[ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; exit 2; }
echo "== native evaluation"
# Remove comments with a small tokenizer that knows strings, character
# literals, raw strings (r"...", r#"..."#) and nested block comments. A "--"
# in a string does not start a comment, and a "/-" in a line comment does not
# open a block comment.
strip_comments='
  local $/; my $s = <STDIN>; my $o = ""; my $d = 0;
  while ((pos($s) // 0) < length $s) {
    if ($d > 0) {
      if    ($s =~ /\G\/-/gc)   { $d++ }
      elsif ($s =~ /\G-\//gc)   { $d--; $o .= " " }
      elsif ($s =~ /\G(\n)/gc)  { $o .= $1 }
      else                      { $s =~ /\G./gcs }
    }
    elsif ($s =~ /\G--[^\n]*/gc)                         { }
    elsif ($s =~ /\G\/-/gc)                              { $d = 1 }
    elsif ($s =~ /\Gr(#*)".*?"\1/gcs)                    { $o .= "\"\"" }
    elsif ($s =~ /\G"(?:\\.|[^"\\])*"/gcs)               { $o .= "\"\"" }
    elsif ($s =~ /\G([\w\p{N}.!?][\w\p{N}.!?\x27]*)/gc)  { $o .= $1 }
    elsif ($s =~ /\G\x27(?:\\.|[^\\\x27])\x27/gc)        { $o .= "c" }
    else                                                 { $s =~ /\G(.)/gcs; $o .= $1 }
  }
  print $o;'
status=0
for f in $(find AvailableChainFGSA -name '*.lean') AvailableChainFGSA.lean; do
  if perl -CSD -e "$strip_comments" < "$f" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== direct imports"
if grep -rnE '^[[:space:]]*(public )?(meta )?import (all )?(AvailableChainFramework|AvailableChainRegistry|AvailableChainStatements|AvailableChainWitnesses|AvailableChainSAPC)' \
    AvailableChainFGSA AvailableChainFGSA.lean; then
  echo "FORBIDDEN DIRECT IMPORT"; exit 1
fi
echo "== import closure"
seen=" "
todo=$( (grep -rhoE '^[[:space:]]*(public )?(meta )?import (all )?[A-Za-z0-9_.]+' AvailableChainFGSA AvailableChainFGSA.lean || true) | awk '{print $NF}' | sort -u)
while [ -n "$todo" ]; do
  next=""
  for m in $todo; do
    case "$seen" in *" $m "*) continue ;; esac
    seen="$seen$m "
    f="${m//.//}.lean"
    if [ -f "$f" ]; then
      next="$next $( (grep -hoE '^[[:space:]]*(public )?(meta )?import (all )?[A-Za-z0-9_.]+' "$f" || true) | awk '{print $NF}')"
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
if [ -f scripts/CheckFGSALease.lean ]; then
  echo "== lease instances"
  lake env lean --run scripts/CheckFGSALease.lean
  # Negative control: a use at the default instance must fail the check.
  neg=$(mktemp -d "$PWD/.lake/fgsa-lease-neg.XXXXXX")
  trap 'rm -rf "$neg"' EXIT
  cat > "$neg/FGSALeaseNeg.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.FGSA
/-- A GridCO gate at the default instance `gridLeasePolicy`. -/
def leaseNegControl (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.gate p st r
end AvailableChain.FGSA
LEAN
  lake env lean -o "$neg/FGSALeaseNeg.olean" "$neg/FGSALeaseNeg.lean"
  set +e
  out=$(lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean FGSALeaseNeg' "$neg")
  code=$?
  set -e
  if [ $code -ne 1 ] || ! echo "$out" | grep -q 'leaseNegControl: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy'; then
    echo "$out"
    echo "LEASE NEGATIVE CONTROL NOT DETECTED (exit $code)"; exit 1
  fi
  echo "negative control rejected, as expected"
fi
echo "all FGSA checks pass"
