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

## FG-SA port WP08 ruling Q resolution (2026-10-09)

Ruling Q replaces `inclusion_proposer_prior` with
`inclusion_proposer_prior_of_F_prefix`. The conclusion and all old parameters
are unchanged. The new premise after D0 is
`Block.Preceq (eraseFG st.fg.F) D0`. Each received head extends D0, so this
premise supplies the canonical proposer-support guard.

Both callers supply the premise from existing facts: `hFs` in `ArmingCover`,
and `hFx`, `hD`, and `clock_fg` in `ExactProposalRetained`. No caller or claim
statement changes. No slashing premise or larger bound is added.

The Arming and Persistence proofs use the canonical domain-to-fullTree bridge.
The Arming HEAD path retains each vertex above destination F and uses the
canonical voter filter directly. It needs no universal top-retention premise.
Clock congruence uses `treeStoreControlsView`.

The replacement helper passes `LEAN_SLOTS=2 lake build --wfail`
(exit 0, 3325 jobs). The caller batch is blocked by WP03c
`Shared/Regimes.lean:368`: its score call lacks destination proposal retention
(exit 1, 3355 jobs). Caller bodies still need a build after that repair.
These are red-window TARGET results, not a FULL or MERGE pass.

WP13v must replace the old helper reference in `Tests/Axioms.lean:1222`.
WP16 must update `scripts/proof-audit-coverage.txt` and attribute the helper
replacement and affected fingerprints. These paths are outside WP08 ownership.

The earlier local kernel counterexample shows a resolved vote below F that
fails canonical proposer support. It is local-state evidence, not a complete
run counterexample. Ruling Q resolves that support obligation.

## FG-SA port WP08 ruling S resolution (2026-10-09)

Ruling S replaces `outageV_frozen_of_receipt` with
`outageV_frozen_of_receipt_of_F_prefix`. All old parameters and the conclusion
stay unchanged. The new premise after hP is
`FGBlock.Preceq (storeAt p c E rho i x).fg.F P`.

Only the ancestor-membership conclusions of `outageV_covering_head_receipts`
and `outageV_frozen_path_receipt` change: each requested ancestor X must extend
the destination F. All other premises and conjuncts stay unchanged.

`outageV_uncontested_head` keeps its statement. It supplies retention for B
from hF, for U from hF and hBU, and for each strict path vertex from
`F_preceq_liveRoot` and the strict path prefix. No vertex below F is required.
No claim premise, slashing premise, bound, or read scope changes.

`ContinuationReceipt` passes `LEAN_SLOTS=2 lake build --wfail`
(exit 0, 3335 jobs). The former receipt-contract STOP is closed.
The remaining WP08 modules and direct importers still need validation at this base.
This is red-window TARGET evidence, not a FULL or MERGE pass.

WP13v must rename the receipt audit in `Tests/OutageContinuationAxioms.lean`.
WP16 must attribute the renamed helper and both retained-path contracts in
coverage, inventory, and shallow/deep fingerprints. No audit data is edited here.
