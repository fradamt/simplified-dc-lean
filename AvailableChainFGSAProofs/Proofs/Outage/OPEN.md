# Outage continuation under (V)

The full companion is proved as `fgsa_outageContinuationClaim` in
`Assembly/Clean.lean:78`.
No FinalitySlashableBound premise was added.

## Lead rulings of 2026-10-07

1. Policy commit 1 (5dd22552) inserts OutageContinuation immediately after
   Regimes in ORDER. W3 verified it and did not repeat the change.
2. Policy commit 2 allows OutageContinuation/Export to import exactly
   Outage/ContinuationTiming, Induction, Receipt, Frame, Gate, and Joint.
   The import-policy comment names this ruling. No other rule is widened.
   The Export was added only after the complete theorem passed Lean.
3. No further guard ruling is needed. No old-read baseline was changed.

## Closed paper facts

- §3: `outageV_uncontested_head` assembles the actual merged support batch
  and frozen height witnesses. `outageV_covering_head_receipts` uses the
  early receipt cut. `outageV_frozen_path_receipt` permits source acceptance
  at that early boundary and still supplies the path before freeze.
- §§4–6: the actual clocked root and contested HEAD are connected to scoped
  source names. `outageV_history_through_relay` derives receiver F compatibility
  through v_s+Δ from earlier-label gates. `outageV_contest_relay` supplies the
  same exact carrier to every honest receiver. `outageV_received_marker_head`
  preserves it in the cumulative store and protects later scheduled reads.
- §7: `outageV_restored_gate` consumes authentic compatible HEAD receipts.
  The event and label inductions now supply its causal history inputs.
- §§8–9: `outageV_events_through_relay` preserves original source history
  and S across gates and deliveries. Only current results constrain writes.
  Old saved results require no compatibility premise. Live locks follow S.
- §10: `outageV_first_restored_head` supplies the pending or pre-expiry seed.
  `outageV_restored_heads` proves all restored HEADs compatible by strong
  label induction and the first-regression marker. `outageV_armed_outputs`
  and `outageV_body` close the inclusive outputs from the original premise.
  No continuation invariant was added to the claim premise.

The claim-to-claim bridge is in Shared/Claims. The unconditional theorem
is beside the existing Clean cut producer in Assembly/Clean. This placement
uses current layer rules and needs no additional Assembly import allowance.
The frozen FGSAClaims record and existing Statements/Claims are unchanged.

## Non-vacuity: kernel premise witness complete

`Tests/OutageContinuationInhabit.lean` supplies the completed kernel witness.
`outageContinuation_inhabited_sleep` proves every field of
`OutageContinuationPrem` in both modes for a 1-node run with full honest
sleep on [8,13). Condition (V) holds at equality. `not_outage₂` proves that
the old budget fails for this run.

`Tests/OutageAfterWindowCounterexample.lean` checks the old budget and
output loss after recovery. It is an executable counterexample to extending
the old budget through the horizon, not to the old finite-window claim.

## Optional 168-event kernel fixture remains open

The exact missing result is a kernel inhabitant of
`OutageContinuationPrem p unitCodec fast E rho 10 17 21 1`, using the
parameters and run in `Tests/OutageContinuationSleep.lean`, for either mode.
The existing audits check the execution, synchrony, healthy-prefix,
participation, and output facts by evaluation. Those finite checks have
not been lifted to all quantified fields of Base₂, HealthyPrefix₂, and
PartialSynchronyBy. No kernel inhabitant is claimed for this 168-event fixture.

The 168-event fixture permits full honest sleep on [17,21), satisfies (V)
at equality, and retains B through horizon 30. All 18 executable audits pass.
The 583cee0 parameters violate (V), by decide. The original brief permits
this kernel fixture to remain open when its construction is costly.

## Old reads

The final audit scans 8,781 constants in 471 active modules. Its six
old/finality readers and 185 height-only readers match the unchanged
baseline. No new read requires a lead ruling.
No new height-only old derive read was added to the baseline.

## FG-SA port WP08 STOP (2026-10-09)

At integration base `4ee95891`, `ExactProposalReceipts.lean:63` fails in
`inclusion_proposer_prior`. Canonical proposer support requires
`Block.Preceq (eraseFG st.fg.F) K` for each resolved head K. The helper takes
an arbitrary st and equates only its votes with a run read. Its receipt premise
supplies resolution in `actView st`, resolution in the cumulative block list,
the slot bound, and `D0 ⪯ K`. It supplies no `F ⪯ D0` or `F ⪯ K` fact.
An ancestor of F can resolve in actView and still fail the new prefix filter.
A canonical frame conversion does not supply this missing support fact.

A replacement helper with a new name and the added premise
`Block.Preceq (eraseFG st.fg.F) D0` needs a lead ruling before implementation.
Both callers already have this fact: `hFs` in `ArmingCover.lean:332`, and
`hFx`, `hD`, and `clock_fg` in `ExactProposalRetained.lean:551`.
No claim premise, slashing premise, conclusion, or bound needs to change.
The old theorem and both callers remain unchanged pending that ruling.

The all-WP08 target build also fails in WP03c `Shared/Regimes.lean:368`:
the score call passes D where destination proposal retention is now required.
Ten independent WP08 modules pass with `LEAN_SLOTS=2 lake build --wfail`
(exit 0, 3325 jobs). The full 38-module build fails (exit 1, 3419 jobs).
These are red-window TARGET results, not a FULL or MERGE pass.

The canonical-domain repairs identified in `ArmingCover`, `ArmingGate`, and
`PersistenceFrame` remain behind the failed receipt helper. No old-frame
comparison was restored and no top-retention premise was added to a claim.

A local kernel check confirms the failed support inference: one held vote
resolves to a strict ancestor of F, meets the slot and self-prefix bounds,
but canonical proposer support is empty (raw voter count 1, score 0).
This is a local-state counterexample, not a complete run counterexample.
A separate local check proves the proposed retained helper with the same
conclusion and verifies the canonical domain-to-fullTree conversion.
Neither local check changes a repository theorem or bypasses a failed import.
