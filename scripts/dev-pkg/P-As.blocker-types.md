# P-As round 3 — current blocker types
Base: f5c77257 on sleep-pas3b. These are current source declarations in failed import closures.
Types are quoted with their source section variables. They are not added assumptions.
Current checks: `.lake/sleep-pas-r3/targets-build.log` and `consumers-final.log`.
The first log predates the final growth repair; that full target now builds with strict audits.
B01, B05–B08, B10–B11 and B18 are removed as satisfied requests.
B09 and B13 now name the current failing declarations. B16/B17 are deferred by the round scope.
No public Claims/Statements file changed. No healing scope record is passed.

## B02 — P-Cl2

`AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` — `cleanSafetyAt_of_trunc`.

The scoped truncation is true under Clean sleep. The old all-node transport input is not supplied.
Repair the export transport; Assembly/Clean already uses the all-node family core before reader
restriction.

```lean
theorem cleanSafetyAt_of_trunc (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (ht : CleanTruncAt p c E rho rho.horizon) : CleanSafetyAt p c E rho
```

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

## B04 — P-Ou

`AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19` — `outageV_source_path`.

The statement is a source-path obligation, not a new regime field. Its proof still uses the old
restart telescope. Global NoRestart is FALSE for ordinary finite runs with wakes; none is supplied.

```lean
theorem outageV_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {K : Block} {u : Time}
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t ≤ u
```

## B09 — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56` — `wc_headRead_stamped`.

The current restarts-at-wakes law is TRUE under Base2. It does not imply an unchanged block stamp
across restart. Exact receiver epochs must be proved at the read; no global stamp preservation is
supplied.

```lean
theorem wc_headRead_stamped {k : Nat} {x : V} {r : Slot} {D : Block}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.RestartsAtWakes E rho)
    (h : WCHeadRead p c E rho k x r D) :
    ∀ A, Block.Preceq A D →
      A ∈ (storeAt p c E rho k x).base.blocks ∧
      GridCO.stampBlock (storeAt p c E rho k x).base A < SA.voteTime p.toParams r
```

## B12 — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21` — `wc_retrospective`.

The body still applies the changed gate-result producer and requests an unguarded later tick.
Awake-now or honest membership does not imply that tick under sleep. No such universal field is
supplied.

```lean
theorem wc_retrospective : WCRetrospectiveStatement p c E rho ΔF w iStar
```

## B13 — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254` — `wcg_retrospective`.

The earlier receiptOrigins request is satisfied. This is the current first failing declaration. A
later tick needs its awake/joined receiver scope; the old all-honest lane is not supplied.

```lean
theorem wcg_retrospective (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGRetrospectiveStatement p c E rho ΔF w iStar
```

## B14 — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55` — `wcg_empty_outputDomain`.

The legacy all-honest output telescope is not accepted as TRUE for sleepy endpoint readers. Port to
the actual retained confirmed-reader scope. Do not add participation or a half-cap to the empty
route.

```lean
theorem wcg_empty_outputDomain
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat} {ΔF : Time}
    (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hsafe : SSafeFromCut₂ p c E source iSource w.QStar ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t)
```

## B15 — P-H1

`AvailableChainFGSAProofs/Tests/HealingBase.lean:28` — `example`.

OUT OF SCOPE. The old fixture uses the obsolete receipt arguments. No healing receipt record is
supplied.

```lean
example (ΔF : Time) (hΔ : E.Δ = p.Δ) (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF) {j r : Nat} {y x : V} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j y r a) (hpre : p.actionTime r < E.t_GST)
    (hhor : E.t_GST + ΔF ≤ rho.horizon) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (E.t_GST + ΔF)
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

## B19 — P-Ar

`AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40` —
`inclusion_proposer_prior_of_F_prefix_on`.

INTEGRATION BLOCKER. The same public name is also declared in ArmingSleep. The imported module fails
before assembly can consume it. This requests one definition, not a universal supplier.

```lean
theorem inclusion_proposer_prior_of_F_prefix_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head (s - 1))) q) (s - 1)
        (SA.voteTime p.toParams (s - 1)))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hFD : Block.Preceq (eraseFG st.fg.F) D0)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L)
```

## B20 — P-Ou

`AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` — `outage_arming_sources`.

LEGACY CONSUMER REPAIR. ArmingCert is not in the current import environment. The old all-honest
pending-action history is not accepted as TRUE under suppression/exclusion. Use P-Ar r5 scoped
history and prove the actual pending-source compatibility; no old record is supplied.

```lean
theorem outage_arming_sources (hs : V2.D.ScheduleWellFormed E rho)
    (htsrc : TSrc p c E rho) {fast : Bool} {T b₀ b₁ : Time} {B : Block}
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1)))
```

## B21 — P-As

`AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` — `w1_tickBatch_st`.

FALSE without an awake guard. At time 248, node 1 is asleep in weakEnv. Its batch store is
unchanged; clock at 248 changes now. The later uniform-store and receipt consumers also need awake
recipient scopes. The repaired B01 prefix does not close this module.

```lean
theorem w1_tickBatch_st (t : Time) (w : World) (u : Validator) :
    ((tickBatch t w).1 u).st = FGSA.clock params (w u).st t
```

## B22 — P-As

`AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` — `w1_strongRecovery`.

FALSE for the current fixture endpoint: source.horizon is 247, but recoveryStart + B_HF is 253. The
strict negative check is in .lake/sleep-pas-r3/W1Prefix.lean. Rebuild the local witness; do not
change the public recovery claim.

```lean
theorem w1_strongRecovery : StrongRecoverySearchPrefix₂ params unitCodec strongEnv source 4 1 where
  sync
```

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

`AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:148`.

```lean
hWitness : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams s) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams s)) y)
```

`AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:154`.

```lean
hInclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon → ∀ u x g,
      SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon → confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Preceq B (V2.D.outputAt E rho g x u)
```

## Inputs that P-As actually supplies

- Clean sleep cut/history/truncation: TRUE in the guarded Clean regime. Assembly uses
  sleepPre, confirmed-reader guards, enabled gates and receiver restart epochs.
- Later-reader gate projection and bounded public S monotonicity: TRUE. Both exact bodies
  pass strict checks in outage-readers-final.log. They use actual Clean and Foundations proofs.
- P15-CUT prefix receipt: TRUE with earlyTime(q) <= b0. The existing P-Ar producer is used.
- W1 known-fold no-restart input: FALSE for arbitrary finite sleep runs. It is TRUE for
  the actual generated prefix/suffix, proved by prefix_no_restart/suffix_no_restart.
  It is used only for that local fixture; no sleep regime is converted to global NoRestart.
- Growth restriction schedule and kept-node membership: TRUE for ordinary valid finite
  runs at those scopes. The proof transports both service alternatives and exact action cuts.
- Growth fixture execution, sleep law, receipt roots, pending service, suffixNoRestart and
  joinedGap: proved for the actual always-awake source/retained continuation at 253/254.
  This fixture does not prove a universal all-awake law for arbitrary sleep runs.
- NoHealing records: none. The healing targets and B16/B17 stay unchanged.

## Header blockers — family owners

The required header command fails on existing `import all` statements:
ArmingKernel:2/3 and ArmingLocal:2 (P-Ar); GoodVotes:2 and RestoredBatch:2 (P-Ou).
These files are outside this writer's scope. No checker, allowance or baseline changed.

## OU-PENDING — P-Ou

`AvailableChainFGSAProofs/Proofs/Outage/PersistenceSleep.lean:193`.

hPending is not established TRUE by this base. It is compatibility for actual pending action
sources; it must come from the scoped joint induction. No all-honest source history is supplied.

```lean
theorem outage_arming_sources_on
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ : Time} {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hPending : ∀ y r C, y ∈ rho.honest →
      p.actionTime r = SA.gateTime p.toParams (l + 1) →
      actionSource p c E rho y r = some (some C) → Block.Compatible C B) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1)))
```

## OU-PREFIX — P-Ar

`AvailableChainFGSAProofs/Proofs/Outage/RestoredBatch.lean:377`.

hPrefix is not supplied. The corrected P15-CUT OutageSleep2 producer is proved, but its regime has a
different budget from OutageContinuationSleepPrem. The continuation adapter is not established TRUE
by this base. It must preserve each earlyTime(q) <= b0 guard.

```lean
theorem outage_continuation_receipt_of_prefix [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hPrefix : OutagePrefixReceipt p c E rho fast T b₀) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁
```

OutageExport's explicit hstore, hframe, hsrc, htsrc and hnamed inputs are TRUE under
its valid outage sleep regime and source fault bound. The actual Foundations exports
supply those scoped facts. The test no longer takes unrestricted nonempty gates,
saved-cache retention, all-node output monotonicity or all-honest clean gates.

## WCSEED — P-As

`AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowthSeed.lean:156`.

PORT. The family finite-facts producer is now proved in WeakContinuationGrowth/StepFacts:297. Its
exact inputs use receiptIdealization and current-epoch fast writes. The old caller supplies the
weaker root projection and the old fast-origin theorem. Receipt scope is TRUE under Base2. The fast
epoch companion is still a P-Fd request; it is not assumed.

```lean
theorem wcg_finiteSeed (hb : Base₂ p c E rho)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (i : Nat) :
    WCFiniteFacts p c E rho i
```

## WCIND — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:788`.

Current seeded induction remains blocked by B13. RestartsAtWakes and joined participation are the
proper finite sleep inputs; no global NoRestart is supplied.

```lean
theorem wcg_seededInduction (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGSeededInductionStatement p c E rho ΔF w iStar
```

## WCEMPTY — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:481`.

The NoRestart parameter has been removed. The all-honest hfinal input is still not accepted as TRUE
for sleepy endpoint readers. Preserve the public confirmed-reader scope and the empty route.

```lean
theorem wcg_empty_live_of_finalBelow
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hb : Base₂ p c E' rho) (hs : V2.D.ScheduleWellFormed E source)
    (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat} {ΔF : Time}
    (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hlive : WeakContinuationLiveAt₂ p c E source w.u w.QStar iSource ΔF)
    (hfinal : ∀ i x y, afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ i →
      i ≤ rho.events.length → x ∈ rho.honest → y ∈ rho.honest →
      Block.Preceq (F_at p c E' rho i x) (S_at p c E' rho i y)) :
    WeakContinuationLiveAt₂ p c E' rho w.u w.QStar
      (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF
```

## WCREADS — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactProposal.lean:39`.

LEGACY. NoRestart is FALSE for ordinary finite runs with wakes. Unguarded reads across restart are
not supplied. Port this consumer to joined receivers and retained exact epochs.

```lean
theorem wc_retainedReads
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho) (hmono : RMono p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
    (hseed : WCSeed p c E rho w iStar) (pt : PtSP) (D0 : Block)
    (hstart : w.u + 2 ≤ pt.s)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hpivot : WCProposalPivot p c E rho w iStar pt D0) :
    ∃ (ip : Nat) (N : NamedProposal p.n) (D : FGBlock (Fin p.n)), N.erase = pt.P ∧
      rho.events[ip]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
        (SA.proposalTime p.toParams pt.s)) ∧
      (⟨.seat (.prop pt.s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip ∧
      ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams pt.s)) →
        ∃ Kc, RetainedReadPremises p
          (clock p (rho.stateBefore E ip
            (V2.D.proposerOf rho (fgsaInterface p c) pt.s)).st
            (SA.proposalTime p.toParams pt.s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams pt.s))
          pt.s D N.erase Kc
```

## WCGATES — P-WC

`AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:131`.

LEGACY. NoRestart and a nonempty result at every honest IsGateTick are not TRUE for ordinary finite
sleep runs. A wake before the same-time gate can suppress the gate. No such fields are supplied.

```lean
theorem wc_proposal_gates [Fintype V]
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (pt : PtSP) (hstart : w.u + 2 ≤ pt.s)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y pt.s = some pt.P)
    (had : ∀ y ∈ rho.honest, WCProposalAdmittedBeforeVote p c E rho y pt)
    (hQP : Block.Preceq w.QStar pt.P)
    (hprior : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r < pt.s → Block.Preceq B pt.P)
    (hfl : ∀ i x phase st WStar (Bfg : FGBlock (Fin p.n)),
      WCDutyInput p c E rho i x phase st → x ∈ rho.honest → iStar ≤ i →
      WStar ∈ st.fg.TF → eraseFG WStar = w.CStar → (heightView p WStar).h = w.M + 1 →
      Block.Preceq w.QStar (eraseFG Bfg) →
      WCUsableHighSourcesBelow p c E rho w i x st (eraseFG Bfg) →
      (∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
        Block.Preceq row.1 (eraseFG Bfg)) →
      ∀ view, WCDutyView p st phase view → view ⊆ st.fg.TF →
        WCFrameLiveBelow p st phase Bfg view)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams pt.s) (SA.gateTime p.toParams pt.s))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams pt.s)).card) :
    ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x pt.s →
      gateResultAt p c E rho i = some (some pt.P) ∧
        Block.Preceq pt.P (S_at p c E rho (i + 1) x)
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

## ZERO-BASE — P-As

`AvailableChainFGSAProofs/Tests/Zero.lean:57`.

LATE LOCAL PORT, hidden by B02. The zero fixture permits this Base2 record, but the old body uses
the removed noRestart/idealization fields and omits SleepWellFormed. These are local fixture
repairs, not additional public assumptions. TRUE for the concrete valid zero run; not a universal
no-restart law for arbitrary finite sleep runs.

```lean
private theorem base0 : Base₂ p4 unitCodec env0 rho0 where
  valid
```

## OU-FIXTURE — P-As

`AvailableChainFGSAProofs/Tests/OutageContinuationInhabit.lean:358`.

LATE LOCAL PORT, hidden by B04/B20. The old trace schedules ticks while its E marks the node as
asleep and does not implement each wake as a restart. Its current concrete Base2 input is not TRUE
for the sleep engine. Rebuild the fixture with actual awake-only steps. No invalid fixture record is
supplied by P-As.

```lean
theorem outageContinuation_inhabited_sleep (fast : Bool) :
    OutageContinuationPrem p unitCodec fast E rho 4 8 13 3 where
  pre
```
