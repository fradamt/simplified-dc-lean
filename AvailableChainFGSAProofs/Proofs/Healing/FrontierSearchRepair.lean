module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.Frame
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSeed
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair

public section

/-! Blueprint 21 HG.3; run 2 R2-b.
Settlement uses healing_settle_start, including the inclusive cut.
The TRepair input has producer healing_tRepair. It retains both first labels.
No weak served witness is used to construct a seed. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cRepCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private theorem p0d5cRepCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d5cRepCore p c) := by
  have h : p0d5cRepCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm
  rw [h]
  exact fgsaCoreLaws p c

private def p0d5cRepTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cRepTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cRepTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5cRepObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5cRepCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5cRepObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5cRepCore p c) (p0d5cRepObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5cRepSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d5cRepKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private abbrev p0d5cRepPair (a : RowWire p.n) : NamedHeightPair := a.payload.height_pair

private theorem p0d5cRepPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5cRepCore p c) E rho (p0d5cRepObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

omit [DecidableEq V] in
private theorem p0d5cRepSeed_iff (E : Generic.Env V) {u : Time} {q : Slot} :
    FGCompose.FrontierSeedQualification (p0d5cRepTiming p) p.k E.t_GST u q ↔
      FrontierSeedQualification p E u q :=
  (frontierSeedQualification_iff p E u q).symm

private theorem p0d5cRepStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (h : FrontierSearchStart p c E rho i ev m kind) :
    FGCompose.FrontierSearchStart (p0d5cRepCore p c) E rho (p0d5cRepObs p c) (p0d5cRepTiming p)
      (recoveryStart p E) i ev m (p0d5cRepKind kind) := by
  have h' := (frontierSearchStart_iff p c E rho i ev m kind).mp h
  cases kind <;> exact h'

-- The proved TFrontier route from the recovery regime (FrontierService).
private theorem p0d5cRepRoute [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) : TFrontier p c E rho :=
  frontier_service E rho hrec mono crossing
    (fun q v _ _ _ => healing_frontier_service_scopes_recovery E rho hrec mono q v)
    (fun i x row hr => fgsa_leaseOrigins_lastWrite p c E rho
      hrec.base.valid.toScheduleWellFormed i x row hr)
    (rowPermission_covered E rho hrec.base hrec.fault)

-- Proposer floor leaf: healing_proposer_floor at the proposer's phase read.
private theorem p0d5cRepFloor [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.AttemptProposalFloor (p0d5cRepCore p c) E rho (p0d5cRepObs p c) (p0d5cRepTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u v m J contested q Q Qfg _ hp hu hgate hQ heq
  have hp' := (p0d5cRepPhase_iff E rho).mp hp
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _hem, hst, _hslot, _hb, _hrows⟩ :=
    healing_promotion_proposal_read p c E rho hS hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
    (SA.proposalTime p.toParams q)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hui := healing_support_idxBefore_le p c E rho hS hj hu
  have hjD := (healing_phase_lt_timeIdx p c E rho hS hj (hqg.trans hgate)).le
  obtain ⟨hH, hc, _hr⟩ := hp'.2.2.2 j x hui hjD hx
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, _hB, heB, hlo⟩ := healing_proposer_floor p c E rho hS q Q st hQ hst hne
  have he : B = Qfg.parent := eraseFG_injective (heB.trans
    (by rw [← eraseFG_parent]; exact congrArg Block.parent heq.symm))
  have hH' : st.fg.h_max = m := by rw [hfg]; exact hH
  have hc' : (FGSA.controls p st).contest = contested := by
    change (KitFG.treeStoreControlsView (heightView p) st.fg).contest = contested
    rw [hfg]
    exact hc
  change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _ at hlo
  rw [hH', hc', he] at hlo
  exact hlo

private theorem p0d5cRepWitness (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (p0d5cRepCore p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem p0d5cRepReceipts (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {deadline : Time} (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (p0d5cRepCore p c) E rho (p0d5cRepObs p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, p0d5cRepWitness E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, p0d5cRepWitness E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, p0d5cRepWitness E rho hrC, p0d5cRepWitness E rho
      hrW⟩


omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME inclusive-prefix monotonicity. -/
theorem frontierSearch_timeIdx_mono (rho : V2.D.Run V (fgsa p c))
    {u v : Time} (h : u ≤ v) : timeIdx rho u ≤ timeIdx rho v := by
  exact FGCompose.frontierSearch_timeIdx_mono rho h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME a shorter phase keeps the lower read cut. -/
theorem frontierSearch_phase_cut (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {u v w : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hp : PhaseInterval p c E rho u v m J contested) (huw : u ≤ w) (hwv : w ≤ v) :
    PhaseInterval p c E rho u w m J contested := by
  exact (p0d5cRepPhase_iff E rho).mp (FGCompose.frontierSearch_phase_cut (p0d5cRepCore p c) E rho
    (p0d5cRepObs p c) ((p0d5cRepPhase_iff E rho).mpr hp) huw hwv)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 H.6/H.6-S and HG.3. DC: SAME full frozen seed adapters. -/
theorem frontierSearch_repair_seed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (repair : TRepair p c E rho)
    {G u v ρbar : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G)
    (hready : recoveryStart p E ≤ u) (hp : PhaseInterval p c E rho u v m J contested)
    (mode : FrontierRepairStart p E G u ρbar) (hbudget : u + ρbar ≤ v) :
    ∃ q Q, FrontierSeedQualification p E u q ∧
      SA.gateTime p.toParams q ≤ u + ρbar ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  cases mode with
  | two β after least =>
    exact tfSeed_two_from_tRepair p c E rho repair hgap hG hready hp after least hbudget
  | one b after least window sync =>
    obtain ⟨q, Q, hs, hg, hQ, he⟩ :=
      tfSeed_one_from_tRepair p c E rho repair hgap hG hready hp after least window sync hbudget
    exact ⟨q, Q, hs, hg.le, hQ, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME a seed follows its phase start in both arms. -/
theorem frontierSearch_seed_after {V : Type} (E : Generic.Env V)
    {u : Time} {q : Slot} (hseed : FrontierSeedQualification p E u q) :
    u ≤ SA.proposalTime p.toParams q := by
  have hk : 1 ≤ p.k := by have := p.kLarge; omega
  exact FGCompose.frontierSearch_seed_after (p0d5cRepTiming p) p.k (p0d5cRepTimingLaws p) hk
    ((p0d5cRepSeed_iff E).mpr hseed)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3. DC: SAME the proposer floor and exact-gate cap. -/
theorem frontierSearch_proposal_heights [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u D m J contested)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams q ≤ D)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (heq : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q) :
    (if contested then m else m - 1) ≤ (heightView p Qfg).h ∧
      (heightView p Qfg).h ≤ m := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨i, K, hi, hK, heK⟩ := healing_rise_one_gate_copy p c E rho hS hexact
    (hgate.trans hp.2.1) hx
    (healing_recovery_gate_reader hrec hx (hGST.trans hu) (hgate.trans hp.2.1))
  have hKe : K = Qfg := eraseFG_injective (heK.trans heq.symm)
  subst K
  exact FGCompose.frontierSearch_proposal_heights (p0d5cRepCore p c) E rho (p0d5cRepObs p c)
      (p0d5cRepTiming p)
    (fgsaInterface p c) (recoveryStart p E) p.E (p0d5cRepObsLaws p c) (fgCertificateLaws p)
    (fun i x => (storeBundle_stateBefore E rho i x).cstore.fg) (p0d5cRepFloor E rho hrec crossing)
    hready ((p0d5cRepPhase_iff E rho).mpr hp) hu hgate hQ heq
    ⟨i, x, healing_support_idxBefore_le p c E rho hS hi (hu.trans hqg),
      (healing_phase_lt_timeIdx p c E rho hS hi hgate).le, hx, hK⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME the saved seed keeps its repair threshold. -/
theorem frontierSearch_seed_repair (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (repair : TRepair p c E rho)
    {G u : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G) (hready : recoveryStart p E ≤ u)
    (hseed : FrontierSeedQualification p E u q) :
    ∃ l, SA.proposalTime p.toParams l < SA.proposalTime p.toParams q ∧
      ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  rcases (frontierSeedQualification_iff p E u q).mp hseed with
    ⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, hkb, hsync, hlt⟩
  · exact ⟨_, hlt, fun v hp =>
      ((repair G u v m J contested hgap hG hready hp).1 β hβ hmin).1⟩
  · exact ⟨_, hlt, fun v hp =>
      ((repair G u v m J contested hgap hG hready hp).2 b hb hmin hkb hsync).1⟩


-- The frozen repair arm gives exact service to each seed-qualified window proposal.
private theorem p0d5cRepExact [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {u v : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {Q : Block}
    (hready : recoveryStart p E ≤ u) (hseed : FrontierSeedQualification p E u q)
    (hp : PhaseInterval p c E rho u v m J contested) (hg : SA.gateTime p.toParams q ≤ v)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) : ExactService p c E rho q Q := by
  obtain ⟨l, hlq, hrep⟩ := frontierSearch_seed_repair E rho repair
    (healing_proposal_gap hrec) hrec.gapPos hready hseed (m := m) (J := J)
    (contested := contested)
  exact hrep v hp q Q hlq hg hQ

-- Gate copy leaf: the exact gate service of a repair-window proposal (RiseOne).
private theorem p0d5cRepGateCopy [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho) :
    ∀ u v m J contested q Q, recoveryStart p E ≤ u →
      FGCompose.PhaseInterval (p0d5cRepCore p c) E rho (p0d5cRepObs p c) u v m J contested →
      FGCompose.FrontierSeedQualification (p0d5cRepTiming p) p.k E.t_GST u q →
      SA.gateTime p.toParams q ≤ v → HonestProposal E rho (fgsaInterface p c) q Q →
      ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧ i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ ((p0d5cRepCore p c).core (rho.stateBefore E i x)).fg.TF ∧
        (p0d5cRepCore p c).erase Qfg = Q := by
  intro u v m J contested q Q hready hp hseed hg hQ
  have hp' := (p0d5cRepPhase_iff E rho).mp hp
  have hseed' := (p0d5cRepSeed_iff E).mp hseed
  have hexact := p0d5cRepExact E rho hrec repair hready hseed' hp' hg hQ
  have hu := frontierSearch_seed_after E hseed'
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hs := hrec.base.valid.toScheduleWellFormed
  have hx := hQ.1.2
  have hgh := hg.trans hp'.2.1
  obtain ⟨j, Qfg, hj, hmem, he⟩ := healing_rise_one_gate_copy p c E rho hs hexact hgh hx
    (healing_recovery_gate_reader hrec hx (hGST.trans hu) hgh)
  have hug : u ≤ SA.gateTime p.toParams q := by
    change u ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  exact ⟨j, _, Qfg, healing_support_idxBefore_le p c E rho hs hj hug,
    (healing_phase_lt_timeIdx p c E rho hs hj hg).le, hx, hmem, he⟩

-- Continuing local service leaf: TFrontier at the exact-service seed.
private theorem p0d5cRepService [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (frontier : TFrontier p c E rho) :
    ∀ u v m J contested q Q Qfg, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q →
      (p0d5cRepCore p c).erase Qfg = Q → ((p0d5cRepObs p c).height Qfg).h = m →
      FGCompose.FrontierProposalService (p0d5cRepCore p c) E rho (p0d5cRepTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cRepTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q →
      FGCompose.PhaseInterval (p0d5cRepCore p c) E rho (p0d5cRepObs p c) u (SA.gateTime p.toParams
        q)
        m J contested → SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cRepCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cRepCore p c) (p0d5cRepSafety p c) E rho (p0d5cRepObs p c)
        (p0d5cRepTiming p) (fgsaInterface p c) p0d5cRepPair q Q Qfg m v := by
  intro u v m J contested q Q Qfg hready hQ he hh _ hseed hu hp hg hv hcap
  have hp' := (p0d5cRepPhase_iff E rho).mp hp
  have hseed' := (p0d5cRepSeed_iff E).mp hseed
  have hexact := p0d5cRepExact E rho hrec repair hready hseed' hp' le_rfl hQ
  obtain ⟨htransfer, hrepair, hopen⟩ := frontier u v m J contested q Q Qfg hready hQ he hh
    hexact ((frontierSeedQualification_iff p E u q).mp hseed') hu hp' hg hv hcap
  refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
  · intro s B hqs hgate hprop
    exact (hrepair s B hqs hgate hprop).1
  · intro r hqr hrt
    obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
    refine ⟨?_, hent, hheight, htime⟩
    intro x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ', hr, ha, hn⟩ := hcov x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ', hr, ha, hn⟩

-- Local repair allowance: both frozen TRepair arms at the frozen first labels.
private theorem p0d5cRepAllowance [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar u : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (mode : FrontierRepairStart p E G u ρbar) :
    FGCompose.FrontierRepairAllowance (p0d5cRepCore p c) E rho (p0d5cRepObs p c) (p0d5cRepTiming p)
      (fgsaInterface p c) (recoveryStart p E) p.k G ρbar u := by
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  have hG := (fgsa_gamma_bounds p G).1
  cases mode with
  | two β after least =>
    refine ⟨by
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .two β after least, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5cRepPhase_iff E rho).mp hp)).1 β after least
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2, hQ, he.1⟩
  | one b after least window sync =>
    refine ⟨by
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .one b after least window sync, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5cRepPhase_iff E rho).mp hp)).2 b after least window sync
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2.le, hQ, he.1⟩

-- The generic saved seed of a repair-window proposal keeps its frozen exact service.
private theorem p0d5cRepServedBack [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {m : Nat} {t : Time}
    (h : FGCompose.StrongServed (p0d5cRepCore p c) (p0d5cRepSafety p c) E rho (p0d5cRepObs p c)
      (p0d5cRepTiming p) (fgsaInterface p c) p0d5cRepPair (recoveryStart p E) p.k m t) :
    StrongServed p c E rho m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh, _, hseed, hu, hp, hg, hth, hcap,
    _⟩ := h
  have hp' := (p0d5cRepPhase_iff E rho).mp hp
  have hseed' := (p0d5cRepSeed_iff E).mp hseed
  exact (strongServed_iff p c E rho m t).mpr ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh,
    p0d5cRepExact E rho hrec repair hready hseed' hp' le_rfl hQ, hseed', hu, hp', hg, hth, hcap⟩

private theorem p0d5cRepResultBack [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {i m : Nat} {start dl : Time}
    (h : FGCompose.FrontierHG3Result (p0d5cRepCore p c) (p0d5cRepSafety p c) E rho (p0d5cRepObs p c)
      (p0d5cRepTiming p) (fgsaInterface p c) p0d5cRepPair (recoveryStart p E) p.k i m start dl) :
    FrontierHG3Result p c E rho i m start dl := by
  apply (frontierHG3Result_iff p c E rho i m start dl).mpr
  rcases h with h | h | ⟨t, h1, h2, hs⟩
  · exact Or.inl ((firstPhaseStopBy_iff p c E rho i m dl).mpr h)
  · exact Or.inr (Or.inl ((firstRiseStopBy_iff p c E rho i m dl).mpr h))
  · exact Or.inr (Or.inr ⟨t, h1, h2, p0d5cRepServedBack E rho hrec repair hs⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME save a complete seed at its actual gate. -/
theorem frontierSearch_save_seed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hp : PhaseInterval p c E rho u D m J contested)
    (hseed : FrontierSeedQualification p E u q)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (he : eraseFG Qfg = Q)
    (hh : (heightView p Qfg).h = m) (hs : ExactService p c E rho q Q)
    (hg : SA.gateTime p.toParams q ≤ D) :
    StrongServed p c E rho m (SA.gateTime p.toParams q) := by
  have hk : 1 ≤ p.k := by have := p.kLarge; omega
  have hu := FGCompose.frontierSearch_seed_after (p0d5cRepTiming p) p.k (p0d5cRepTimingLaws p) hk
    ((p0d5cRepSeed_iff E).mpr hseed)
  change u ≤ SA.proposalTime p.toParams q at hu
  have huq : u ≤ SA.gateTime p.toParams q := by
    change u ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hp' := (p0d5cRepPhase_iff E rho).mpr hp
  apply (strongServed_iff p c E rho m (SA.gateTime p.toParams q)).mpr
  exact ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh, hs, hseed, hu,
    (p0d5cRepPhase_iff E rho).mp (FGCompose.frontierSearch_phase_cut (p0d5cRepCore p c) E rho
      (p0d5cRepObs p c)
      hp' huq hg), le_rfl, hg.trans hp.2.1,
    FGCompose.frontierSearch_phase_cap (p0d5cRepCore p c) E rho (p0d5cRepObs p c) (p0d5cRepObsLaws
      p c) hp' hg⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 contest; plan R2-b.
DC: SAME stop at the finite first event, or save the repaired height-m seed.
The horizon is closed. TRepair has producer healing_tRepair. -/
theorem frontier_hg3_contest [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) (monoAll : RMonoAll p
      c E rho)
    (repair : TRepair p c E rho)
    {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .contest)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + (ρbar + 3 * p.Δ) ≤ rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time (ev.time + (ρbar + 3 * p.Δ)) := by
  have hk : 1 ≤ p.k := by have := p.kLarge; omega
  have hJst : E.t_GST ≤ recoveryStart p E := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  exact p0d5cRepResultBack E rho hrec repair (FGCompose.frontier_hg3_contest (p0d5cRepCore p c)
    (p0d5cRepSafety p c) E rho (p0d5cRepObs p c) (p0d5cRepTiming p) (fgsaInterface p c) p0d5cRepPair
    (recoveryStart p E) p.k p.E (p0d5cRepObsLaws p c) (fgCertificateLaws p)
    (fun i x => (storeBundle_stateBefore E rho i x).cstore.fg) (fgJustificationLaws p)
    (fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1) p.deltaPos (p0d5cRepCoreLaws p c)
    (fun h => eraseFG_preceq h) (fun nd => joinedNow p nd.st) (TargetReceiptService E rho)
    (p0d5cRepTimingLaws p) hk crossing hrec.base.valid.toScheduleWellFormed ⟨monoAll⟩
    hrec.base.delta hJst hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    (fun _ ht => healing_ready_read_cutoff E ht)
    (fun j e m hj hr hm hf hh => p0d5cRepReceipts E rho
      (healing_phase_witness_receipts_recovery E rho hrec j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    hrec.gapPos (p0d5cRepFloor E rho hrec crossing) (p0d5cRepGateCopy E rho hrec repair)
    (p0d5cRepService E rho hrec repair (p0d5cRepRoute E rho hrec monoAll crossing))
    (p0d5cRepStart E rho hstart) (p0d5cRepAllowance E rho hrec repair mode) hhor)

end AvailableChain.FGSA.Run
end
