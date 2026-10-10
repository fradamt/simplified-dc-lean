# P-As Round 6 — current blocker types

Base: ef1b0e43, branch sleep-pas6. Full P-As remains OPEN.
Healing is OUT OF SCOPE. Public Claims/Statements are unchanged.
Evidence: .lake/sleep-pas-r6/. This register replaces the Round 5 requests.

## Closed requests

- B02, owner P-Cl2: CLOSED. Assembly/Clean:53 `assembly_clean_state` composes
  Clean/Safety:74 `clean_sCompatible` with Clean/Closure:380 `sExtends`.
  Foundations/Export supplies the foundation and source records. The exact CleanSet
  produces the all-node state pair before reader restriction. `fgsa_cleanSafetyClaim`
  passes that producer to `cleanSafety_of_cut`. No scoped output is used as an all-node input.
- B19, owner P-Ar: CLOSED. The duplicate names no longer block this base.
  ArmingKernel and the actual RestoredBatch consumer build.
- B20, owner P-Ou: RETIRED. `outage_arming_sources` and its all-honest legacy seed
  are no longer current producer requests. ScopedInduction:351
  `outage_armed_induction_scoped` and :386 `outage_armed_read_scoped` are the current
  pre-restoration producers. Their endpoint does not cover full continuation.
- ZERO-BASE, owner P-As: CLOSED. Both Zero fixtures have current receipt roots,
  SleepWellFormed, RestartsAtWakes and joined participation. The delayed-row fixture
  retains its actual trace, positive safety witness and failure of the equal-delay regime.
- P-Ar continuation prefix: CLOSED. Tests/OutageAssemblyAxioms:10 composes
  `arming_continuation_prefix_receipt` with `outage_continuation_receipt_of_prefix`.
  No assumed prefix receipt or complete receipt-service callback remains in that check.

## New closed requests from P-Ou Round 8

- OU-INPUTS: CLOSED. ReceiverInputs:1059 `inclusion_receiver_inputs_of_clean`
  produces InclusionReceiverInputs from the actual CleanSet. Suppliers:151 exports
  `outage_supplier_inclusion_inputs`. The three Clean exporters construct it themselves.
- OU-SCOPES: CLOSED. InclusionGateService and InclusionGateBody produce the actual
  enabled-gate receipt scope, with receiver floors and the required post-GST cuts.
  No hScopes callback remains in the three Clean exporters or their assembly callers.
- Clean growth callbacks: CLOSED producer request. GrowthSuppliers:15
  `clean_growth_suppliers` supplies the gate witness, compatibility and later inclusion.
  Assembly/Outage:161 `assembly_clean_growth_suppliers` supplies its full field inputs
  from the actual CleanSet, CleanCutClaim and Foundations. Its growth wrapper no longer
  takes hWitness or hInclusion. Exact production bodies pass an eight-command audit.
  Full Assembly/Outage remains OPEN through the separate P-Ou imports below.
  EXPORT ROUTE OPEN, owner P-Ou: Outage/Export does not yet import GrowthSuppliers.
  Add `public import AvailableChainFGSAProofs.Proofs.Outage.GrowthSuppliers` there,
  or export that exact existing producer through the lane Export. P-As uses the
  permitted Export route and does not add a direct lane import or layer exception.
  The body audit explicitly imports the existing producer; it does not close the route.
- Continuation receipt: RestoredBatch:388 `outage_continuation_receipt` now consumes
  P-Ar's concrete prefix producer. It is a receipt producer, not a continuation induction.
- Post-E count: ReceiverInputs:1064 `outage_post_e_joined_count` proves the strict count
  at actual votes within the horizon. No fixed A union W count is extended beyond E.

## B04 / OU-CONT — exact P-Ou obligation

Current failing consumers:

- Proofs/Outage/ContinuationReceipt.lean:19 `outageV_source_path`, with failing
  source/acceptance calls at :36/:134/:201 and old duty projections at :388/:552/:746.
- Proofs/Outage/ContinuationInduction.lean:40 `outage_event_induction_le_expiry`;
  :284 still calls removed `outage_arming_local`.
- Proofs/Outage/ContinuationJoint.lean:871 `outageV_body`.
- Proofs/OutageContinuation/Export.lean:12 `outageContinuation_claim_of`.

Paths start with AvailableChainFGSAProofs/. P-Ou owns the continuation induction,
restored HEAD history, expiry handover, healthy suffix and complete exporter.
The exact final conclusion, under the existing family foundation/source suppliers, is:

```lean
(h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
  OutageContinuationConcl p c E rho fast T b₀ b₁
```

This is the existing public endpoint, not an added premise. The base has no complete
producer for it. Root supplies StoreAt, ActiveViewAt, FrameAt, SrcFrameAboveStmt,
SourceDisciplineAt and the exact healthy sleep cut from the named Foundations/Clean
claims. P-As supplies no NoRestart, future hResults or all-honest seed.

ReceiverInputs:1097 `outage_continuation_results_of_head_history` has one exact
conditional invariant input. P-Ou's joint induction must produce it for the selected B:

```lean
∀ s q K, restoredLabel p b₁ < s →
  outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
    (SA.voteTime p.toParams s) →
  HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
    (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
  Block.Compatible K B
```

This field concerns actual emitted HEADs in the public reader scope. E supplies its
count in the restored window; the new post-E producer supplies later joined counts.
Services keep their actual vote-time GST cut, receiver floor and epoch. This adapter
is conditional until P-Ou proves the history. It is not a producer of that history.
Later conditional hTargets stay P-Ou induction work. No new assembly callback is added.

## OU-CLOSE — exact P-Ou obligation

Proofs/Outage/Close.lean:84 `outage_protected_read` and :178 `outage_compat_body`;
Proofs/Outage/Export.lean:405 `outage_compat_body_of_cut`.
Paths start with AvailableChainFGSAProofs/.

Close still uses removed Base₂.noRestart at :113/:121 and removed duties_and_outputs
at :147. Those old shapes are not requested. Port this existing cut endpoint:

```lean
(hcut : CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀)
(h : OutagePrem p c fast E rho pt ΔF)
(hstrat : RStrat p c E rho) : OutageCompatAt p c E rho fast pt
```

Assembly produces the cut and foundation/source arguments. Keep covered receivers,
joined transfer readers, enabled gates, saved-cache epochs and the public reader scope.
Export:424 still omits fast in its result type. P-Ou must port that internal consumer
without changing the public predicate. The new Clean service/growth producers do not
close this outage endpoint. Its producer is not available on this base.

## FAST — P-Fd, CLOSED in Round 6

`AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:642` —
`fgsa_leaseOrigins_fastWrites_epoch` is the named producer on ef1b0e43.
WC/WCG assembly takes its ScheduleWellFormed input from the actual source or
continuation Base₂.valid. No explicit FAST request remains at Root or a WC caller.
Restart clears the fast cache, so the origin is in the receiver's current epoch.
The finite-facts and discharge helpers pass the actual producer to the lane kernels.

```lean
(hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (x : V) :
  ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
    ∃ j < i, V2.D.restartFree rho x j i ∧ enabledGateAt p c E rho j x s ∧
      gatePassedAt p c E rho j ∧ ∃ B, gateResultAt p c E rho j = some (some B) ∧
        Block.Preceq X B ∧ fastAt p c E rho x s X
```

## OU-FIXTURE — P-As, CLOSED in Round 6

`AvailableChainFGSAProofs/Tests/OutageContinuationInhabit.lean` now proves
`OutageContinuationSleepPrem p unitCodec fast E rho 4 12 18 3` in both modes.
The run has one honest node, Δ=1, k=3, η=2, and horizon 37.
It sleeps at time 15, after the covering gate at 14; restart 16 precedes tick 16.
The restored label is 5, with first vote 21 and join cutoff 16.
The generator omits every asleep tick and delivery. Schedule, SleepWellFormed,
RestartsAtWakes, execution validity and receipt collision freedom are kernel-checked.
The joined counts hold before the outage, at each E vote, and after OutageEnd=37.
The public (V) premise holds; the legacy budget still fails: 18-12 > min η L.

The old fixture's full sleep on [8,13) was not valid. Even after adding restart 13,
a one-node full sleep ending at the restored vote cannot meet OutageE: its only
node is unjoined at vote 13. The new fixture changes only private parameters and
events. The public claim and its premise and conclusion definitions are unchanged.

## WCROOT — P-As, only deferred H-time closure remains

Assembly/Root:139 `assembly_weakContinuationGrowth` and :152
`assembly_weakContinuationClaims` now take HTimeClaim explicitly and no FAST input.
The source and continuation FAST facts come from the schedule of each actual run.
The source witness retains its H0 join cutoff and finite seed. The nonempty suffix
uses its own finite facts and joined count. The empty route uses the source seed and
join cutoff, without added suffix participation. Four exact Root body commands pass.

Assembly/Root:57 `fgsaClaims_of_open` now takes hH for weakContinuationLive;
:104 `fgsaClaims_of_hTime` passes the same hH. No hidden healing producer is used
in that conditional weak-continuation field. The unconditional :121 `fgsaClaims`
and :125 `fgsa_weakContinuationGrowthClaim` still depend on the deferred named target:

```lean
AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:501
healing_hTimeClaim (p : Params) : HTimeClaim p
```

Owner P-H1/P-H2 supplies HTimeClaim under the unchanged HealingTimePrem. It is OPEN,
not supplied or marked proved by P-As. The current import build fails in healing
scope/repair consumers, including OpeningServiceGate, FrontierServiceGate, Repair and
FrontierSeed. Their legacy scopes are not accepted as assumptions. SCOPE-NARROW rules
1–5 apply to the future producers. This is the whole deferred owner obligation.

## ROOT-TESTS / deferred local fixture ports — P-As

The unchanged FGSAClaims structure builds. The aggregate proof and its actual Root
importers stay EXPECTED-FAIL through OU-CONT, OU-CLOSE and healing closure.
FGCompose requires fgsaClaims; LiveDC reads its GST fields. No fake aggregate is supplied.
NonVacuity/FinalityClaims also imports healing. NonVacuity/Adversarial retains the known
Base₂ sleep/receipt and restart-step ports behind Root; its repair is P-As work after
that closure. W1's full fixture and all current independent WC tests remain GREEN.
No positive public claim test is weakened or removed.

B16/B17 retain the deferred HealingPackages/HealingReset fixture repairs. Their old
restore calls omit the wake time. They are code repairs, not valid input requests.
No NoRestart premise is supplied to repair them. No healing source or fixture is edited.
Bare P23, G-S2, final regeneration and deferred initialAt cleanup remain OPEN.

## Explicit input audit

- Proved: actual schedule, sleep validity, receipt roots, restart epochs and awake-only
  positive fixture events. Joined counts include suppressed duties and wakes.
- Named producer: FAST current-cache origins from fgsa_leaseOrigins_fastWrites_epoch.
- Named producer: WC finite facts/seeds from wc_finiteFacts / wcg_finiteSeed and the
  HTime-selected source; replay uses actual run agreement. Invariants/services remain
  lane kernel outputs through discharge. Scoped row origins use wc_scopedRowOrigins
  with ExecutionValid; they concern actual honest-holder rows, not universal receipts.
- Named producer: Clean cut from fgsa_cleanCutClaim; state pair from clean_sCompatible
  and sExtends; Foundations supply store, frame, source and strat facts.
- Named producer: P-Ar prefix and P-Ou restored receipts; actual inclusion records,
  enabled gate scopes, later origins, Clean growth callbacks and post-E joined counts.
- Exact owner obligation: P-Ou's scoped continuation history and the two public outage
  endpoints above; P-H1/P-H2's HTimeClaim. No unproduced record is instantiated.

All used cross-node service inputs retain their post-GST cut, receiver floor, actual
read tick, history and epoch. Local provenance asks for no pre-GST service. Suppressed
gates are handled by the lane's enabled-gate split. Exclusion remains an actual
service guard. No universal delivery, join, retained-body or future-result shape is added.
