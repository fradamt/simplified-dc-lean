# Outage continuation under (V)

The companion is stated. The full claim and lane Export are still open.
No FinalitySlashableBound premise has been added.

## Lead rulings of 2026-10-07

1. The lead approved the single ORDER insertion after Regimes. It is the
   first, separate policy commit in w2. No other claims guard changes.
   The claims and proofs roots now reach all new modules.
   It does not change AvailableChainFGSAClaims/FGSAClaims.lean.
2. The lead approved an exact OutageContinuation/Export import allowance
   for ContinuationTiming, Induction, Receipt, Frame, Gate, and the eventual
   joint-induction module. The allowance and Export remain deferred until
   the claim is proved. No empty Export and no Shared/Claims wiring exist.
3. No other guard change is requested. The old-read baseline is unchanged.

## Paper §3: remaining uncontested coverage producer

`outageV_head_covers_of_witnesses` instantiates the actual voter filter,
eligibility, and dominated walk. It requires these exact facts at the
scheduled label-s HEAD state, for s at least r+1:

- The live root is compatible with B.
- For each C with liveRoot ≺ C ⪯ B, there is X in `voterBlocks p st s`
  with `eraseFG X = C`. There is W in the same voter set with X ⪯ W and
  `controls.lo ≤ (heightView p W).h`.
- `voterCount (headVotes p st s) < 2 * score B` in the actual merged pools.
- Every D conflicting with B has `score D < score B` in those pools.

`outageV_head_covers_from_batch` derives the score bounds from authentic
covering HEADs in the actual merged support pool and restored participation.
`outageV_crossing_source` extracts the original honest height-(H-1) source,
its action index, its held body, and compatibility from source history.
`outageV_source_held` proves that the clock did not admit that body.
`outageV_frozen_of_receipt` preserves a carrier received before the freeze
in the actual later voter set, with its original strict stamp.

Assemble these at the uncontested scheduled HEAD read. Supply the covering
HEAD receipts and a height witness for each live-root-to-B path vertex.
If the crossing source is below B, use B. Otherwise relay that source and
its path. Prove the needed F compatibility from the current F below B and
monotonic F. Do not use a full-store witness in place of a frozen witness.

`outageV_source_gate_cutoff` proves the inclusive source-time bound from
its gate-time bound. `outageV_path_coverage` permits that inclusive cutoff.
The remaining facts are the covering HEAD receipt producer and the
assembly of the frozen height witnesses at the scheduled clocked HEAD read.
The gate receipt read at d_(s-1) is later than v_s. Do not use it unchanged
for this HEAD. Supply receipts before z_(s-1) and preserve them to v_s.

## Paper §§4–6: frames and the first regression

The HEAD-walk connection is proved. `outageV_liveRoot_compatible` handles
live locks. `outageV_head_of_filter` handles the actual walk, including an
empty tree. `outageV_contested_head` and `outageV_marker_head` handle the
contest and the three marker frame cases. `outageV_head_from_rows` obtains
the frame and crossing facts from scoped rows at an actual event cut.

`outageV_exact_carrier_receipt` recovers the SAME FG carrier P, including
its fixed justified-entry identity. It gives either B ⪯ F or stored P
with `(heightView p P).h_j ≤ local h_j`. `outageV_regression_receipt`
instantiates the actual label-s HEAD event cut and deadline v_s+Δ.
Monotonic F reduces earlier exclusion tests to this one remaining fact:

    B ∥ F_at p c E rho (idxBefore rho (v_s+Δ)) receiver.

Prove that fact for every honest receiver at the first regression from
earlier-label gate protection and original source history. Do not use
receipt of P to prove it. `outageV_gate_through_relay` proves that every
gate through this deadline has label below s. `outageV_short_horizon`
excludes the next HEAD and gate s if the deadline exceeds the horizon.
No receipt beyond the horizon is assumed.

The joint proof must also carry P forward in the cumulative store and
transfer the scoped frame facts to each scheduled clocked HEAD read.

## Paper §7: restored gates

`outageV_compatible_head_receipts` derives the authentic vote, active target,
slot bound, and strict vote/block stamps at the actual pre-gate view. It
uses full-run broadcast and acceptance relay. Targets may be below F.

`outageV_restored_gate` combines this transport with the local count.
Its history inputs are exactly current F compatibility with B and
compatibility of the earlier scheduled label-s HEADs with B. Monotonic F
supplies the receipt history when F is below B. If B is below F, the result
extends F. Its other inputs are execution, no restart, CStar, root identity,
synchrony, GST before the label-s vote, and restored participation there.
No separate receipt or count premise remains in this gate theorem.

The joint induction must supply the two compatibility facts causally.
They have not been proved from OutageContinuationPrem for all event cuts.

## Paper §§8–10: local steps and joint induction

The local current-result steps are proved. `outageV_gateStep_covers`
retains B through empty, vetoed, already-saved, and passed gates plus
normalization. `outageV_fastSet_compatible` and `outageV_source_compatible`
use only the current result. `outageV_live_locks` uses lease-below-S.
No premise requires old saved outage results to be compatible.
The existing delivery-frame proof retains original emission indices and
uses the retained-finalization argument in PersistenceHistory.

The remaining joint event/label induction must connect these producers:
S covers B; F and live locks are compatible; original honest source
history is compatible; restored HEADs cover B until the first regression
and are compatible afterwards; the first-regression marker has its causal
deadline and receiver facts. Seed with `outageV_arming_prem` and
`outageV_armed_to_expiry`. Do not assume the continuation invariant as a
new claim premise.

The first restored HEAD coverage also needs an assembled producer: use
pending/in-flight arming fields before d_j, and pre-expiry live-root
protection for d_j ≤ v_r < e₀. Exclude future duties beyond the horizon.

`outageV_inclusive_outputs` closes the final read conversion from the
local S/F invariant. It includes all events at t and horizon deliveries.
The invariant itself, and thus OutageContinuationClaim, remain unproved.

## Non-vacuity

The 583cee0 parameters violate (V), by a kernel decide proof.
The 168-event full-sleep run satisfies (V) at equality. Its 18 executable
audits pass. A kernel inhabitant of OutageContinuationPrem remains open.
