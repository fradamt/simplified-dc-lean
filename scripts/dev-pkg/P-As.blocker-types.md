# P-As Round 5 — current blocker types

Base: 7a30ce82 = P-As 1b7c9cf2 plus sleep-int 3ca33648.
Full P-As remains OPEN. Healing work remains OUT OF SCOPE.
Public Claims/Statements are unchanged. No open record is supplied as a premise of a public claim.
Evidence: .lake/sleep-pas-r5/. This register replaces the Round 4 requests.

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

## B03 — P-H1

`AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226` — `healing_support_honest_head`.

OUT OF SCOPE. This is an inherited import blocker. No H1 scope record is supplied or consumed. Its
unrestricted sleep scope is not accepted as TRUE in this round.

```lean
theorem healing_support_honest_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot} {k : Fin p.n}
    {o : GridCO.Wire p.n .root} (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base (.head s)) k)
        (SA.voteTime p.toParams s)) ∧
      GridCO.headTarget? o = some (headVote p (FGSA.clock p
        (V2.D.Run.stateBefore E rho j (rho.seatOf (.base (.head s)) k)).st
        (SA.voteTime p.toParams s)) s).root
```

## B16 — P-As

`AvailableChainFGSAProofs/Tests/NonVacuity/HealingPackages.lean:450` — `step_constant`.

OUT OF SCOPE because this is a healing test. The old restore expression omits the exact wake time;
it is not a well-typed sleep step. The repair must use the actual time, not assume NoRestart.

```lean
theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ _ => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd)
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o
```

## B17 — P-As

`AvailableChainFGSAProofs/Tests/NonVacuity/HealingReset.lean:199` — `step_constant`.

OUT OF SCOPE because this is a healing test. The old restore expression omits the exact wake time.
The prior stash patch is not used for this file.

```lean
theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ _ => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd)
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o
```

## B04 — P-Ou

`AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19` — `outageV_source_path`.

The statement is a source-path obligation, not a new regime field. Its proof still uses the old
block-stamp/acceptance telescope. Global NoRestart is FALSE for ordinary finite runs with wakes; none is supplied.

```lean
theorem outageV_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {K : Block} {u : Time}
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t ≤ u
```

## OU-CONT — P-Ou

`Proofs/Outage/ContinuationInduction.lean:39`, `outage_event_induction_le_expiry`.
`Proofs/Outage/ContinuationJoint.lean:871`, `outageV_body`.
`Proofs/OutageContinuation/Export.lean:12`, `outageContinuation_claim_of`.
Paths start with AvailableChainFGSAProofs/.

The first consumer still uses global NoRestart and the removed all-honest arming seed
(`outage_arming_local` at :284). Those shapes are FALSE for ordinary finite sleep runs
and are NOT requested. Port the continuation induction to the actual covered receiver,
joined duty, enabled gate, receipt epoch, restored source and post-GST service scopes.
P-Ar's complete prefix receipt is now produced; it is not a remaining input.
The exact final producer target is the existing public conclusion below, under its existing
foundation/source/healthy-cut suppliers; no extra public premise is proposed.

```lean
(h : OutageContinuationPrem p c fast E rho T b₀ b₁ ΔF)
(hstrat : RStrat p c E rho) (hcumul : RStoreCumul p c E rho)
(origin : RQCOrigin p c E rho) : OutageContinuationConcl p c E rho T b₀
```

P-Ou must also supply the continued good-HEAD compatibility and counts after E's label window.
ReceiverInputs:757 supplies actual fresh HEAD receipts at enabled, post-GST gates; its
actual emitted-target compatibility input is still conditional. It is not global hResults.
No future result, all-honest duty history or universal target receipt is supplied by P-As.

## OU-CLOSE — P-Ou

`Proofs/Outage/Close.lean:84`, `outage_protected_read`, and :178 `outage_compat_body`.
`Proofs/Outage/Export.lean:417`, `outage_compat_body_of_cut`.
Paths start with AvailableChainFGSAProofs/.

Close still projects Base₂.noRestart at :113/:121 and calls removed `duties_and_outputs`
at :147. Assembly and Tests/OutageExport cannot build through that import.
Port the public wrapper to P-Ar's current certificate and P-Ou's scoped induction.
Keep enabled gates, actual joined transfer readers, saved-cache restart epochs and the
public protected-reader scope. The legacy all-gate nonempty and saved-preservation
inputs are not accepted as TRUE under suppression or wakes.
The exact existing cut-consumer endpoint is:

```lean
(hcut : CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀)
(h : OutagePrem p c fast E rho pt ΔF)
(hstrat : RStrat p c E rho) : OutageCompatAt p c E rho fast pt
```

Export:437 currently omits `fast` in that result type; P-Ou must restore the actual
existing public predicate argument. The foundation/source arguments of Export:417
are produced at Assembly/Outage.
The public claim is unchanged. A pre-restoration G proof is not its full producer.

## OU-INPUTS — P-Ou

`AvailableChainFGSAProofs/Proofs/Outage/Export.lean:93`.

Not established TRUE by this base. The early, relay and retained services must use actual emissions,
the joined receiver, and its receipt epoch. P-As adds no universal service input.

```lean
hInputs : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF → InclusionReceiverInputs E rho
```

## OU-SCOPES — P-Ou

`AvailableChainFGSAProofs/Proofs/Outage/Export.lean:129`.

The enabled/current-epoch scope is required. Not established TRUE by this base as a complete receipt
record. P-As supplies no unguarded scope; P-Ou must construct the services.

```lean
hScopes : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF → ∀ s i x, x ∈ rho.honest →
        enabledGateAt p c E rho i x s ∨
          confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
            (SA.gateTime p.toParams s) →
        IsGateTick p c rho i x s → GateReceiptScope E rho i x s
```

## Existing conditional growth inputs — P-Ou

Assembly/Outage keeps hWitness and hInclusion. Their guarded Clean conclusions are expected
under the ordinary finite Clean regime, including restart, join, suppression and exclusion.
This base does not provide their proofs. They remain conditional and are not instantiated at Root.
Their exact types are in the source at the following locations.

`AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:160`.

```lean
hWitness : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams s) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams s)) y)
```

`AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:166`.

```lean
hInclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon → ∀ u x g,
      SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon → confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Preceq B (V2.D.outputAt E rho g x u)
```

## FAST — P-Fd

`AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:541`.

The existing origin theorem builds. The requested receiver-epoch companion is TRUE for current fast
writes, because restart clears that cache. Its proof is not supplied by this base. The exact
stronger field used by P-As is quoted below.

```lean
theorem fgsa_leaseOrigins_fastWrites (hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (x : V) :
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X
```

`AvailableChainFGSAProofs/Proofs/Assembly/ContinuationService.lean:156`.

```lean
hfast : ∀ i x s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧ enabledGateAt p c E rho j x s ∧
        gatePassedAt p c E rho j ∧ ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X
```

## OU-FIXTURE — P-As

`AvailableChainFGSAProofs/Tests/OutageContinuationInhabit.lean:358`.

LATE LOCAL PORT, hidden by B04/B20. The old trace schedules ticks while its E marks the node as
asleep and does not implement each wake as a restart. Its current concrete Base2 input is not TRUE
for the sleep engine. STOP this item: the inherited positive witness is not ExecutionValid under sleep.
A separate fixture repair needs actual awake-only steps and phase-zero wake restarts. No invalid fixture record is
supplied by P-As.

```lean
theorem outageContinuation_inhabited_sleep (fast : Bool) :
    OutageContinuationPrem p unitCodec fast E rho 4 8 13 3 where
  pre
```

The exact original generator is checked in OutageFixtureCounterexample.lean.
It contains `.tick 0 8` while E.awake 0 8 = false, and no `.restart 0 13` at the wake.
The kernel proves both facts and `¬ SleepWellFormed E rho`. The inherited test is unchanged.
This is a fixture STOP, not a counterexample to a public claim.

## WCROOT — P-As, dependent on FAST and deferred H-time closure

`Proofs/Assembly/Root.lean:137`, `assembly_weakContinuationGrowth`, and :158,
`assembly_weakContinuationClaims`, keep HTimeClaim and the exact FAST producer explicit.
The exact source bodies pass a four-command extracted strict audit with the two unchanged
safety aggregates. This is PREPARED caller evidence; the full Root module remains OPEN.
The source witness uses `wcg_sourceWitness_joined` plus `wcg_finiteSeed`, retaining H0's
join cutoff. The nonempty branch uses continuation FAST, that cutoff and the retained seed.
The empty branch uses source FAST and the source seed, without suffix participation.
Root:98 and :124 still need the actual FAST producer before their unconditional callers
can be completed. No FAST premise is added to FGSAClaims or either public continuation claim.
`healing_hTimeClaim` is still a separate, deferred P-H1/P-H2 obligation.

`fgsa_outageContinuationClaim` has the same name and type at Root:171. Its former import
blocked Clean on the unfinished continuation family. Root is the permitted assembly join.
Tests/OutageContinuationAxioms now imports its actual owning Root and stays EXPECTED-FAIL.
Full FGSAClaims, FGCompose, LiveDC and Root-importing non-vacuity tests remain OPEN.
Bare P23, G-S2, final regeneration and the deferred initialAt consumers remain OPEN.

## Supplied input audit

- TRUE: CleanSet's exact sleep cut, quorum, foundation/source facts and all-node state pair.
  P-Cl2 then restricts to confirmed readers. Both Zero fixture traces remain valid and positive.
- TRUE: P-Ar's prefix receipts under HealthyPrefix₂, with each earlyTime(q) ≤ b₀ cut.
  RestoredBatch uses actual emissions, receiver epochs and the regime's post-GST service.
- TRUE at their stated scopes: the selected WC source join cutoff, inclusive source count,
  strict suffix count, cached safety and original enabled-gate proposal evidence.
- TRUE as an exact open obligation: FAST current-cache origins have a restart-free epoch,
  since restart clears that cache. Its P-Fd proof is absent from this base.
- HTimeClaim and P-Ou's public endpoints are open owner proof requests. No H1/H2 aggregate,
  InclusionReceiverInputs, GateReceiptScope, future hResults, hWitness or hInclusion is supplied.
  P-Ou must certify the actual records under their Clean/continuation guards. CleanSet has GST = 0;
  joined + enabled alone is never used as a pre-GST cross-node service premise.
- FALSE and rejected: global NoRestart from sleep, all-honest joined duties, suppressed-gate
  nonempty results, saved-cache preservation across a restart, or the inherited outage fixture's
  SleepWellFormed record. No such value is passed to an assembly theorem.
- Healing requests are historical and OUT OF SCOPE; their universal service shapes are not certified.

## ROOT-TESTS — P-As, behind the open Root import

`Tests/NonVacuity/Adversarial.lean:2327/:3559/:3578` — nvExecution, base, nvRecovery.
`Tests/NonVacuity/FinalityClaims.lean:1128/:1149/:1194` — nvExecution, base, nvRecovery.
Paths start with AvailableChainFGSAProofs/.

Their actual Base₂ targets are `Base₂ params unitCodec env run`; the old builders still
set removed noRestart/idealization fields. They need the concrete fixture's SleepWellFormed,
RestartsAtWakes, NamedReceiptRootCollisionFree and joined recovery fields. They are local
fixture ports, not new assumptions of public claims. The existing all-awake no-restart proofs
may be used only for those traces; no universal NoRestart is requested.
Adversarial's initialAt consumers at :1889-1891 and :2981-2983 remain deferred until these
ports and the Root import compile. Neither fixture is repaired or certified by Round 5.
No positive witness is removed or replaced by an assumed invalid record.
