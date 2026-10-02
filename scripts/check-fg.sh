#!/usr/bin/env bash
# All FG checks in one run. It builds the two FG libraries once (under --wfail),
# then runs the root-import check, the syntax check, the axiom check, the
# pinned-name check, the pin check and the negative controls of the pin check
# and of the FG import-closure check, and stops at the first failure. The
# test-only overrides FGPINIDS, FGREG and FGHISTALLOW are unset for the
# positive runs. The Lean
# checks read the built .olean files, which Lean does not compare with the
# sources, so they must run after the build. Run: bash scripts/check-fg.sh.
# Exit codes: 0 all checks pass; otherwise the exit code of the failed step.
set -euo pipefail
unset FGPINIDS FGREG FGHISTALLOW
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
lake env lean --run scripts/CheckFGAxioms.lean --expect \
  finalityOf_def simplexFinalityView_def StrictPrefix_def TargetQCAt_def \
  JustificationBirth_def FinalityQCAfter_def NoSlashOutside_def acceptedThreshold_def \
  heightOf_def simplexHeightView_def HeightBridge_def HeightRowsEq_def \
  HeightSelector_def selectHeightRows_def HeightStepBridge_def deriveWithSelector_def \
  heightSelector_id heightSelector_selectHeightRows process_row_height_congr \
  foldRows_height_eq_of_rowsEq process_height_events_height_congr \
  transition_height_eq_of_rowsEq deriveWithSelector_id deriveWithSelector_height \
  simplexHeightRefinement heightBridge_of_refinement heightStepBridge_selector \
  heightBridge_selector heightBridge_fields heightBridge_selector_fields \
  simplexHeightLaws heightLaws_of_bridge \
  bit_process_iff bit_fold_iff bit_first_inclusion progress_first_inclusion \
  bit_first_inclusion_persist finality_match_before finality_first_inclusion_persist \
  transition_finality_of_cover derive_finality_of_cover \
  transition_target_of_cover transition_progress_of_cover \
  derive_target_of_cover derive_progress_of_cover \
  no_mixed_cross_before_maturity first_height_crossing_edge \
  crossing_honest_matching_row justification_eq_on_plateau \
  transition_target_of_cover_of_bridge \
  transition_progress_of_cover_of_bridge \
  derive_target_of_cover_of_bridge \
  derive_progress_of_cover_of_bridge \
  no_mixed_cross_before_maturity_of_bridge \
  first_height_crossing_edge_of_bridge \
  crossing_honest_matching_row_of_bridge \
  justification_eq_on_plateau_of_bridge \
  height_occurrence_keys_of_bridge \
  height_occurrence_keys finality_occurrence_history \
  simplexPending_def simplexSelectionView_def simplex_finalized_mono \
  simplex_justification_birth_interval simplex_prefinal_entry_origin \
  simplex_finality_origin simplexCertificateLaws simplexSelectionLaws simplexChainCertificate \
  finalized_preceq_chain_of_certificate \
  finalized_below_height_of_certificate \
  finality_certificate_of_certificate \
  slashableWeight_or_justified_eq_of_certificate \
  e1Weight_or_finalized_preceq_of_certificate \
  slashableWeight_or_finalized_preceq_of_certificate \
  e1Weight_or_finalized_compatible_of_le_of_certificate \
  slashableWeight_or_finalized_compatible_of_certificate \
  exists_crossing_quorum_ne_justified_of_heightLaws \
  e1Weight_of_finalityQC_not_preceq_of_heightLaws \
  slashableWeight_of_finalized_crossing_of_certificate \
  exists_honest_timeout_of_crossing_of_heightLaws \
  crossing_maturity_of_heightBridge \
  certificateHeadFields \
  certificateHeadFields_def \
  provenance_entry_of_heightLaws \
  provenance_finalityRow_of_heightLaws \
  provenance_finalityQC_of_heightLaws \
  provenance_finality_of_certificate \
  justification_certificate_rows_of_heightLaws \
  slashableWeight_of_finalized_pair_crossing_of_certificate \
  pruneCertEntries pruneCertEntries_def \
  mem_pruneCertEntries \
  certEntry_preceq_of_le \
  FGSelectionLaws.of_core \
  FGSelectionLaws.prune_eq \
  selection_chosen_spec \
  selection_ready_covered \
  selection_chosen_removed \
  selection_retained_iff \
  selection_removed_covered \
  selection_finalized_zero \
  selection_finalized_mono \
  selection_finality_origin \
  FGCertificateLaws.of_selection \
  no_slashableWeight_of_fault_bound \
  finalized_preceq_of_no_evidence \
  finalized_preceq_of_fault_bound \
  finalized_compatible_of_fault_bound \
  viewLock_of_certificate \
  viewLock_of_fault_certificate \
  accepted_lock_of_no_evidence \
  accepted_lock_of_fault_bound \
  FGStoreSafety.of_certificate \
  FGStoreSafety.accepted_lock_no_evidence \
  FGStoreSafety.accepted_lock_fault \
  simplex_certificateHeadFields_eq \
  simplexStoreInvariant \
  simplexStoreSafety \
  frontierView_def lexMaxView_def filteredFromView_def storeControlsView_def storeFrameView_def \
  hOf_of_bridge frontier_of_bridge lexMax_of_bridge filteredFrom_of_bridge \
  storeControls_of_bridge storeFrame_of_bridge
step "scripts/FGPinIds.lean --check-names"
lake env lean --run scripts/FGPinIds.lean --check-names
step "scripts/check-fg-pins.sh"
bash scripts/check-fg-pins.sh
step "negative controls of scripts/check-fg-pins.sh"
# Each control runs the pin check on temporary copies: an emitter script that
# changes the elaborated table (FGPINIDS), a registry copy (FGREG) or an
# allowlist copy (FGHISTALLOW); some controls use the real registry. Each
# control must fail and print its message (expect_pass: must pass).
# FGNEGSHOW=1 also prints the output of each control.
run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }
show() { [ -z "${FGNEGSHOW:-}" ] || printf "%s\n" "$out" | sed "s/^/    /"; }
expect_fail() {  # NAME PATTERN...: the check failed and printed each PATTERN (fixed strings)
  local name=$1 p; shift
  if [ "$code" -eq 0 ]; then echo "$out"; echo "NEGATIVE CONTROL NOT DETECTED: $name"; exit 1; fi
  for p in "$@"; do
    if ! printf '%s\n' "$out" | grep -qF -- "$p"; then
      echo "$out"; echo "NEGATIVE CONTROL $name: missing \"$p\""; exit 1
    fi
  done
  echo "rejected, as expected: $name"; show
}
expect_pass() {  # NAME: the check passed
  if [ "$code" -ne 0 ]; then echo "$out"; echo "POSITIVE CONTROL FAILED: $1"; exit 1; fi
  echo "passed, as expected: $1"; show
}
emitter() {  # NAME PINS HIST: an emitter of the manifest of these Lean values
  cat > "$neg/$1.lean" <<LEAN
import AvailableChainKitFG.Pins
open AvailableChain.KitFG
def main : IO Unit := do
  for l in manifest ($2) defPins notFormalized ($3) do IO.println l
LEAN
}
# splice NAME COV KINDS: the manifest of the real table, except that the records
# and trailers of KINDS come from the table with one more pin neg.extra.v1 (one
# clause COV): a record of a pin that has no pin record (step 0 controls).
splice() {
  cat > "$neg/$1.lean" <<LEAN
import AvailableChainKitFG.Pins
open AvailableChain.KitFG
def kinds : List String := $3
def pick (l : String) : Bool :=
  kinds.any fun k => l.startsWith (k ++ " ") || l.startsWith ("END " ++ k ++ " ")
def main : IO Unit := do
  let base := manifest pins defPins notFormalized historicalPins
  let extra : Pin := { id := "neg.extra.v1", sources := [], clauses := [⟨"control", $2⟩] }
  let full := manifest (pins ++ [extra]) defPins notFormalized historicalPins
  let body (ls : List String) := ls.filter (!·.startsWith "END ")
  let trail (ls : List String) := ls.filter (·.startsWith "END ")
  let key (l : String) := (l.splitOn " ").take 2
  for l in (body base).filter (!pick ·) ++ (body full).filter pick do IO.println l
  for t in trail base do
    IO.println (if pick t then ((trail full).find? (key · == key t)).getD t else t)
LEAN
}
withdraw() {  # ID: a registry copy with the Index status of ID set to WITHDRAWN (control)
  I="$1" LC_ALL=C awk -F'│' -v OFS='│' '/^## Index/ { s = 1 } /^## / && !/^## Index/ { s = 0 }
    s && index($0, "│ " ENVIRON["I"] " ") == 1 { $4 = " WITHDRAWN (control) "; n++ }
    { print } END { if (n != 1) exit 1 }' docs/FG-COMPOSITION.md > "$neg/reg-$1.md" ||
    { echo "NO INDEX ROW FOR THE CONTROL: $1"; exit 1; }
}
pins_check() { run env "$@" bash scripts/check-fg-pins.sh; }
# A current pin (not a hist pin) that the controls change.
cur=fg.accountable.v1
addCov() { echo "pins.map fun p => if p.id == \"$cur\" then { p with clauses := p.clauses ++ \
  [⟨\"control\", $1⟩] } else p"; }
# The allowlist of the script.
sed -n "/^HIST='\$/,/^'\$/p" scripts/check-fg-pins.sh | sed '1d;$d' > "$neg/allow0"

# Step 4, status test.
emitter NegA "$(addCov '.ap "ap.headReachesLo.v5" ""')" historicalPins
withdraw ap.headReachesLo.v5
pins_check FGPINIDS="$neg/NegA.lean" FGREG="$neg/reg-ap.headReachesLo.v5.md"
expect_fail "(a) a current .ap to a withdrawn AP id (registry copy)" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN (control)), named by the current pin $cur (dep)"
pins_check FGPINIDS="$neg/NegA.lean"
expect_fail "(a) the same on the real registry" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN" "named by the current pin $cur (dep)"
emitter NegB "$(addCov '.external "fj.frame.v3" ""')" historicalPins
withdraw fj.frame.v3
pins_check FGPINIDS="$neg/NegB.lean" FGREG="$neg/reg-fj.frame.v3.md"
expect_fail "(b) a current dep on a withdrawn pin (registry copy)" \
  "NOT CURRENT: fj.frame.v3 (WITHDRAWN (control)), named by the current pin $cur (dep)"
pins_check FGPINIDS="$neg/NegB.lean"
expect_fail "(b) the same on the real registry" \
  "NOT CURRENT: fj.frame.v3 (WITHDRAWN" "named by the current pin $cur (dep)"
emitter NegF "$(addCov '.ap "ap.X.v1" ""')" historicalPins
pins_check FGPINIDS="$neg/NegF.lean"
expect_fail "(f) a current .ap to an id with status REFUTED; WITHDRAWN (real registry)" \
  "NOT CURRENT: ap.X.v1 (REFUTED; WITHDRAWN), named by the current pin $cur (dep)"
emitter NegG "$(addCov '.ap "ap.headReachesLo.v4" ""')" historicalPins
pins_check FGPINIDS="$neg/NegG.lean"
expect_fail "(g) a current .ap to a SUPERSEDED id (real registry)" \
  "NOT CURRENT: ap.headReachesLo.v4 (SUPERSEDED" "named by the current pin $cur (dep)"
withdraw "$cur"
pins_check FGREG="$neg/reg-$cur.md"
expect_fail "(h) a current pin whose own id is WITHDRAWN" \
  "NOT CURRENT: $cur (WITHDRAWN (control)), named by the current pin $cur (own id)"
emitter NegI "$(addCov '.paper "from ap.headReachesLo.v5 and fg.finalLock.v1"')" historicalPins
pins_check FGPINIDS="$neg/NegI.lean"
expect_fail "(i) a current pin that names a withdrawn id in its free text" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN" "named by the current pin $cur (text)" \
  "NOT CURRENT: fg.finalLock.v1 (WITHDRAWN"
emitter PosI "$(addCov '.paper "a note (history: ap.headReachesLo.v5 (R ≥ 3), fg.finalLock.v1)"')" \
  historicalPins
pins_check FGPINIDS="$neg/PosI.lean"
expect_pass "(i) the same ids inside a (history: …) marker"
emitter NegI2 "$(addCov '.paper "a note (history: ap.headReachesLo.v5"')" historicalPins
pins_check FGPINIDS="$neg/NegI2.lean"
expect_fail "(i) an unclosed (history: marker" "MALFORMED TRAILER: END mention" "$cur/!UNCLOSED"

# Step 5, the hist pins and the allowlist.
emitter NegC pins "historicalPins ++ [\"$cur\"]"
pins_check FGPINIDS="$neg/NegC.lean"
expect_fail "(c) a hist pin not on the allowlist" "HIST PIN NOT ON THE ALLOWLIST: $cur"
{ cat "$neg/allow0"; echo "$cur 2026-09-29 control (d)"; } > "$neg/allow"
pins_check FGHISTALLOW="$neg/allow"
expect_fail "(d) an allowlist entry with no hist record" \
  "ALLOWLIST ENTRY WITHOUT A HIST RECORD: $cur"
pins_check FGPINIDS="$neg/NegC.lean" FGHISTALLOW="$neg/allow"
expect_fail "(e) a hist pin with a current status (PROVED)" "HIST PIN IS CURRENT: $cur (PROVED"
{ cat "$neg/allow0"; echo "$cur 2026-09-29"; } > "$neg/allowM"
pins_check FGHISTALLOW="$neg/allowM"
expect_fail "(j) an allowlist entry with no reason" "MALFORMED ALLOWLIST ENTRY: $cur 2026-09-29"
{ cat "$neg/allow0"; head -1 "$neg/allow0"; } > "$neg/allowD"
pins_check FGHISTALLOW="$neg/allowD"
expect_fail "(j) a duplicate allowlist entry" "DUPLICATE ALLOWLIST ENTRY: fj.frame.v3"

# Step 0, the manifest.
emitter NegK1 pins 'historicalPins ++ ["no.such.v1"]'
pins_check FGPINIDS="$neg/NegK1.lean"
expect_fail "(k) a hist id that is not a pin id" "HIST ID NOT A PIN ID: no.such.v1"
emitter NegK2 pins 'historicalPins ++ ["fj.frame.v3"]'
pins_check FGPINIDS="$neg/NegK2.lean"
expect_fail "(k) a repeated hist record" "DUPLICATE: hist fj.frame.v3"
splice NegK3 '.external "comp.settle.v1" ""' '["dep"]'
pins_check FGPINIDS="$neg/NegK3.lean"
expect_fail "(k) a dep record of no pin" "DEP OF NO PIN: neg.extra.v1"
splice NegK4 '.external "fg.uniqueJust.v1" ""' '["external"]'
pins_check FGPINIDS="$neg/NegK4.lean"
expect_fail "(k) an external id with no dep record" "DEP TARGETS ARE NOT THE AP AND EXTERNAL IDS"
splice NegK5 '.paper "see fg.uniqueJust.v1"' '["mention"]'
pins_check FGPINIDS="$neg/NegK5.lean"
expect_fail "(k) a mention record of no pin" "MENTION OF NO PIN: neg.extra.v1"

# The FG import closure (CheckFGAxioms.lean): a root module that imports a
# library outside the closure allowlist (a stand-in for AvailableChainFGSA;
# scripts/check-fgsa.sh runs the control with AvailableChainFGSA itself).
printf 'def negLibX : Nat := 1\n' > "$neg/AvailableChainNegLib.lean"
printf 'import AvailableChainNegLib\n' > "$neg/FGClosureNeg.lean"
for m in AvailableChainNegLib FGClosureNeg; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGAxioms.lean --root FGClosureNeg' "$neg"
expect_fail "(l) a library above the FG libraries in the FG import closure" \
  "FORBIDDEN LIBRARY IN THE FG IMPORT CLOSURE: AvailableChainNegLib"
echo "all FG checks pass"
