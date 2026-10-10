# P-As Round 4 — current blocker types
Base: 3a538409, including sleep-int dcdb4a06 and P-As Round 3 06b683de.
Full P-As remains OPEN. These are source declarations and exact open producer requests.
They are not new assumptions of public claims. Healing targets remain OUT OF SCOPE.
B09/B12/B13/B14 and WCSEED/WCIND/WCEMPTY/WCREADS/WCGATES are satisfied by the P-WC
exports and the compiled P-As caller ports. B21/B22 are satisfied by the full W1 fixture.
Current evidence is in .lake/sleep-pas-r4/. Public Claims/Statements are unchanged.

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

INTEGRATION BLOCKER, owner P-Ar. The exact duplicate names are:

- `AvailableChain.FGSA.Run.inclusion_proposer_prior_of_F_prefix_on`
- `AvailableChain.FGSA.Run.inclusion_reader_scores_on`

ArmingScores declares them at :40/:110 after importing ExactProposalReceipts, which
already declares them at :420/:475. ArmingSleep imports ArmingInput, which imports
ArmingCover, which imports ArmingScores. Thus ArmingSleep receives this collision
through its imports. The earlier Round 3 description placed the second declarations
in ArmingSleep; that location was wrong.

YES: sleep-int dcdb4a06 fails to build this import closure. The three declaration
files are byte-for-byte unchanged from that pin. The build errors in
.lake/sleep-pas-r4/ports5.log name both duplicate declarations. This is a name conflict,
not an unproduced universal service field. P-As did not edit P-Ar files.

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
  joinedGap: proved for the separate always-awake growth fixture at 253/254.
  This fixture does not prove a universal all-awake law for arbitrary sleep runs.
- NoHealing records: none. The healing targets and B16/B17 stay unchanged.


- WC source join cutoff: TRUE for the selected H0 witness. Named producers are
  wc_sourceJoinCut and wcg_sourceJoinCut. A seed's firstVoteAfterGST alone is weaker.
- Source joined count: TRUE under StrongRecoverySearchPrefix2 plus that exact cutoff;
  wc_sourceParticipation and wcg_sourceParticipation produce it at every covered time.
- Combined source/suffix count: TRUE under CleanContinuationSleep2 or
  CleanGrowthContinuationSleep2 plus the source cutoff. wc_participation and
  wcg_participation keep the inclusive endpoint and strict suffix. No all-node join
  law is asserted outside those intervals.
- Source seed: TRUE from the selected HealingInput and finite facts. Producers are
  wc_heightSeed_of_finite and wcg_heightSeed_of_finite. wc_finiteFacts/wcg_finiteSeed
  still require FAST. wcg_sourceWitness_joined retains the selected cutoff with its seed.
- Cached safety: TRUE from the finite seeded induction; wc_cachedSafety and
  wcg_cachedSafety are the P-WC producers. Cached proposal coverage is produced from
  the exact original WCResult and cached monotonicity, rather than assumed.
- Inclusion: TRUE for actual enabled gates. wcg_inclusion6_result retains the exact
  original gate evidence. Later endpoint readers use their own confirmed-reader scope.
- Empty suffix: TRUE from source cached safety, exact source proposal coverage and
  scoped source service. No continuation participation or half-cap is added.
- Common internal lane inputs: TRUE in their stated public regimes. Base2 supplies
  validity, links, CStar, wakes, delta and receipt idealization. Synchrony, fault bounds,
  accountability and participation are existing conditional public premises.
  Foundations supplies durable/epoch stores, all-run monotonicity, frame epochs,
  recurrence, geometry, certificates, source discipline, labels, QC/stratification,
  no slash, emitted names, targets, lease origins, deadlines and held-row origins.
  wc_scopedRowOrigins/wcg_scopedRowOrigins supply actual root-scope row origins;
  cap_finality_head supplies finality-head provenance. FAST is the one open producer.
- Invariant, pivot, admission, frame-live and service inputs: TRUE under those same
  lane premises and seed; the named P-WC producers supply them. Assembly only composes
  those proofs. Data indices, selected memberships, horizon guards and exact read
  facts remain conditional facts about the consumer's selected event.
- W1: execution, sleep law, receipt roots, synchrony, recovery endpoint, suffixNoRestart,
  joinedGap and joined suffix count are proved for source 253 / continuation 269.
  Generic batch and receipt helpers use actual awake receivers. Sleeping stores stay
  fixed. NoRestart is proved only for this concrete no-wake trace; the separate
  SleepPositive fixture still checks an actual wake restart.

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

## WCROOT — P-As, dependent on FAST and deferred H-time closure

`AvailableChainFGSAProofs/Proofs/Assembly/Root.lean:98/:123/:125/:131/:133`.
`Tests/WeakContinuationGrowthAssemblyAxioms.lean:2` imports that Root and remains OPEN.
Its local WC component audit passes through Tests/WeakContinuationGrowthAxioms.
The full Root audit was not reclassified GREEN or bypassed.

```lean
-- Root:98, field of fgsaClaims_of_open:
weakContinuationLive := fgsa_weakContinuationLiveClaim_of_hTime (healing_hTimeClaim p)

-- Root:123:
theorem fgsa_weakContinuationGrowthClaim (p : Params) (G : Time) :
    WeakContinuationGrowthClaim p G
```

The internal live supplier now keeps the exact FAST producer explicit. Root needs a
concrete P-Fd theorem with the FAST type for each Base2 run, including source and suffix.
It must not add that supplier to FGSAClaims or WeakContinuationGrowthClaim.
For growth, use wcg_sourceWitness_joined with wcg_finiteSeed and retain its H0 cutoff.
Pass that cutoff and FAST to wcg_nonemptyLive; pass source FAST to wcg_emptyLive.
The source and retained seed adapters already build with this exact obligation.
No assembly family proof is invented. HTimeClaim closure is a separate, deferred
P-H1/P-H2 obligation; no healing scope record is supplied in this round.
