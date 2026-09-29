#!/usr/bin/env bash
# All FG checks in one run. It builds the two FG libraries once (under --wfail),
# then runs the root-import check, the syntax check, the axiom check, the
# pinned-name check, the pin check and the negative controls of the pin check,
# and stops at the first failure. The Lean
# checks read the built .olean files, which Lean does not compare with the
# sources, so they must run after the build. Run: bash scripts/check-fg.sh.
# Exit codes: 0 all checks pass; otherwise the exit code of the failed step.
set -euo pipefail
cd "$(dirname "$0")/.."
step() { echo "== $1"; }
step "lake build --wfail AvailableChainSimplexFG AvailableChainKitFG"
log=$(mktemp)
neg=$(mktemp -d "$PWD/.lake/fg-neg.XXXXXX")
trap 'rm -f "$log"; rm -rf "$neg"' EXIT
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
step "negative controls of scripts/check-fg-pins.sh"
# Each control runs the pin check on temporary copies: an emitter script that
# changes the elaborated table (FGPINIDS), a registry copy (FGREG) or an
# allowlist copy (FGHISTALLOW). Each control must fail and print its message.
# FGNEGSHOW=1 also prints the output of each control.
run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }
expect_fail() {  # NAME PATTERN: the check failed and printed PATTERN (fixed string)
  if [ "$code" -eq 0 ]; then echo "$out"; echo "NEGATIVE CONTROL NOT DETECTED: $1"; exit 1; fi
  if ! printf '%s\n' "$out" | grep -qF -- "$2"; then
    echo "$out"; echo "NEGATIVE CONTROL $1: missing \"$2\""; exit 1
  fi
  echo "rejected, as expected: $1"; [ -z "${FGNEGSHOW:-}" ] || printf "%s\n" "$out" | sed "s/^/    /"
}
emitter() {  # NAME PINS HIST: an emitter of the manifest of these Lean values
  cat > "$neg/$1.lean" <<LEAN
import AvailableChainKitFG.Pins
open AvailableChain.KitFG
def main : IO Unit := do
  for l in manifest ($2) defPins notFormalized ($3) do IO.println l
LEAN
}
withdraw() {  # ID: a registry copy with the Index status of ID set to WITHDRAWN (control)
  I="$1" LC_ALL=C awk -F'│' -v OFS='│' '/^## Index/ { s = 1 } /^## / && !/^## Index/ { s = 0 }
    s && index($0, "│ " ENVIRON["I"] " ") == 1 { $4 = " WITHDRAWN (control) "; n++ }
    { print } END { if (n != 1) exit 1 }' docs/FG-COMPOSITION.md > "$neg/reg-$1.md" ||
    { echo "NO INDEX ROW FOR THE CONTROL: $1"; exit 1; }
}
# A current pin (not a hist pin) that the controls change.
cur=fg.accountable.v1
addRef() { echo "pins.map fun p => if p.id == \"$cur\" then { p with clauses := p.clauses ++ \
  [⟨\"control\", .$1 \"$2\" \"\"⟩] } else p"; }
emitter NegA "$(addRef ap ap.headReachesLo.v5)" historicalPins
withdraw ap.headReachesLo.v5
run env FGPINIDS="$neg/NegA.lean" FGREG="$neg/reg-ap.headReachesLo.v5.md" bash scripts/check-fg-pins.sh
expect_fail "(a) a current .ap to a withdrawn AP id" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN (control)), named by the current pin $cur"
emitter NegB "$(addRef external fj.frame.v3)" historicalPins
withdraw fj.frame.v3
run env FGPINIDS="$neg/NegB.lean" FGREG="$neg/reg-fj.frame.v3.md" bash scripts/check-fg-pins.sh
expect_fail "(b) a current dep on a withdrawn pin" \
  "NOT CURRENT: fj.frame.v3 (WITHDRAWN (control)), named by the current pin $cur"
emitter NegC pins "historicalPins ++ [\"$cur\"]"
run env FGPINIDS="$neg/NegC.lean" bash scripts/check-fg-pins.sh
expect_fail "(c) a hist pin not on the allowlist" "HIST PIN NOT ON THE ALLOWLIST: $cur"
# The allowlist of the script, plus one entry for a pin with no hist record.
sed -n "/^HIST='\$/,/^'\$/p" scripts/check-fg-pins.sh | sed '1d;$d' > "$neg/allow"
echo "$cur 2026-09-29 control (d)" >> "$neg/allow"
run env FGHISTALLOW="$neg/allow" bash scripts/check-fg-pins.sh
expect_fail "(d) an allowlist entry with no hist record" \
  "ALLOWLIST ENTRY WITHOUT A HIST RECORD: $cur"
echo "all FG checks pass"
