module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchGap
public import AvailableChainFGSAProofs.Proofs.Healing.Descent
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportFrame

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop

public section

/-! Blueprint 21 HG.3 top J. The fixed entry age must come from the
accepted carrier at the actual start, including the inclusive cut. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cTopCore (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem p0d5cTopCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d5cTopCore p c) := by
  have h : p0d5cTopCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm
  rw [h]
  exact fgsaCoreLaws p c

private def p0d5cTopTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cTopTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cTopTiming p) where
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

private def p0d5cTopObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5cTopCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5cTopObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5cTopCore p c) (p0d5cTopObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5cTopSafety (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d5cTopSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5cTopDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

private def p0d5cTopWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5cTopSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5cTopSigner
  decode_height a u ha := by
    delta p0d5cTopSafety at ha
    rw [p0d5cTopDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5cTopSafety at ha
    rw [p0d5cTopDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5cTopSafety at ha
    rw [p0d5cTopDecodeRow ha]
    rfl

private def p0d5cTopDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5cTopDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5cTopDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5cTopDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5cTopPayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5cTopSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5cTopSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5cTopSigner; simp
  | proposer s => delta p0d5cTopSigner; simp
  | seat label j => cases label <;> delta p0d5cTopSigner <;> simp

private def p0d5cTopWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5cTopR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5cTopWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5cTopWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d5cTopKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private abbrev p0d5cTopPair (a : RowWire p.n) : NamedHeightPair := a.payload.height_pair

private theorem p0d5cTopPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5cTopCore p c) E rho (p0d5cTopObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

omit [DecidableEq V] in
private theorem p0d5cTopSeed_iff (E : Generic.Env V) {u : Time} {q : Slot} :
    FGCompose.FrontierSeedQualification (p0d5cTopTiming p) p.k E.t_GST u q ↔
      FrontierSeedQualification p E u q :=
  (frontierSeedQualification_iff p E u q).symm

private theorem p0d5cTopStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (h : FrontierSearchStart p c E rho i ev m kind) :
    FGCompose.FrontierSearchStart (p0d5cTopCore p c) E rho (p0d5cTopObs p c) (p0d5cTopTiming p)
      (recoveryStart p E) i ev m (p0d5cTopKind kind) := by
  have h' := (frontierSearchStart_iff p c E rho i ev m kind).mp h
  cases kind <;> exact h'

-- The proved TFrontier route from the recovery regime (FrontierService).
private theorem p0d5cTopRoute [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) : TFrontier p c E rho :=
  frontier_service E rho hrec mono crossing
    (fun q v _ _ _ => healing_frontier_service_scopes_recovery E rho hrec mono q v)
    (fun i x row hr => fgsa_leaseOrigins_lastWrite p c E rho
      hrec.base.valid.toScheduleWellFormed i x row hr)
    (rowPermission_covered E rho hrec.base hrec.fault)

-- Proposer floor leaf: healing_proposer_floor at the proposer's phase read.
private theorem p0d5cTopFloor [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.AttemptProposalFloor (p0d5cTopCore p c) E rho (p0d5cTopObs p c) (p0d5cTopTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u v m J contested q Q Qfg _ hp hu hgate hQ heq
  have hp' := (p0d5cTopPhase_iff E rho).mp hp
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

private theorem p0d5cTopWitness (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (p0d5cTopCore p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem p0d5cTopReceipts (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {deadline : Time} (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (p0d5cTopCore p c) E rho (p0d5cTopObs p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, p0d5cTopWitness E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, p0d5cTopWitness E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, p0d5cTopWitness E rho hrC, p0d5cTopWitness E rho
      hrW⟩

-- The frozen repair arm gives exact service to each seed-qualified window proposal.
private theorem p0d5cTopExact [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
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
private theorem p0d5cTopGateCopy [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho) :
    ∀ u v m J contested q Q, recoveryStart p E ≤ u →
      FGCompose.PhaseInterval (p0d5cTopCore p c) E rho (p0d5cTopObs p c) u v m J contested →
      FGCompose.FrontierSeedQualification (p0d5cTopTiming p) p.k E.t_GST u q →
      SA.gateTime p.toParams q ≤ v → HonestProposal E rho (fgsaInterface p c) q Q →
      ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧ i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ ((p0d5cTopCore p c).core (rho.stateBefore E i x)).fg.TF ∧
        (p0d5cTopCore p c).erase Qfg = Q := by
  intro u v m J contested q Q hready hp hseed hg hQ
  have hp' := (p0d5cTopPhase_iff E rho).mp hp
  have hseed' := (p0d5cTopSeed_iff E).mp hseed
  have hexact := p0d5cTopExact E rho hrec repair hready hseed' hp' hg hQ
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
private theorem p0d5cTopService [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (frontier : TFrontier p c E rho) :
    ∀ u v m J contested q Q Qfg, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q →
      (p0d5cTopCore p c).erase Qfg = Q → ((p0d5cTopObs p c).height Qfg).h = m →
      FGCompose.FrontierProposalService (p0d5cTopCore p c) E rho (p0d5cTopTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cTopTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q →
      FGCompose.PhaseInterval (p0d5cTopCore p c) E rho (p0d5cTopObs p c) u (SA.gateTime p.toParams
        q)
        m J contested → SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cTopCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cTopCore p c) (p0d5cTopSafety p c) E rho (p0d5cTopObs p c)
        (p0d5cTopTiming p) (fgsaInterface p c) p0d5cTopPair q Q Qfg m v := by
  intro u v m J contested q Q Qfg hready hQ he hh _ hseed hu hp hg hv hcap
  have hp' := (p0d5cTopPhase_iff E rho).mp hp
  have hseed' := (p0d5cTopSeed_iff E).mp hseed
  have hexact := p0d5cTopExact E rho hrec repair hready hseed' hp' le_rfl hQ
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
private theorem p0d5cTopAllowance [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar u : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (mode : FrontierRepairStart p E G u ρbar) :
    FGCompose.FrontierRepairAllowance (p0d5cTopCore p c) E rho (p0d5cTopObs p c) (p0d5cTopTiming p)
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
      ((p0d5cTopPhase_iff E rho).mp hp)).1 β after least
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2, hQ, he.1⟩
  | one b after least window sync =>
    refine ⟨by
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .one b after least window sync, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5cTopPhase_iff E rho).mp hp)).2 b after least window sync
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2.le, hQ, he.1⟩

-- The generic saved seed of a repair-window proposal keeps its frozen exact service.
private theorem p0d5cTopServedBack [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {m : Nat} {t : Time}
    (h : FGCompose.StrongServed (p0d5cTopCore p c) (p0d5cTopSafety p c) E rho (p0d5cTopObs p c)
      (p0d5cTopTiming p) (fgsaInterface p c) p0d5cTopPair (recoveryStart p E) p.k m t) :
    StrongServed p c E rho m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh, _, hseed, hu, hp, hg, hth, hcap,
    _⟩ := h
  have hp' := (p0d5cTopPhase_iff E rho).mp hp
  have hseed' := (p0d5cTopSeed_iff E).mp hseed
  exact (strongServed_iff p c E rho m t).mpr ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh,
    p0d5cTopExact E rho hrec repair hready hseed' hp' le_rfl hQ, hseed', hu, hp', hg, hth, hcap⟩

private theorem p0d5cTopResultBack [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {i m : Nat} {start dl : Time}
    (h : FGCompose.FrontierHG3Result (p0d5cTopCore p c) (p0d5cTopSafety p c) E rho (p0d5cTopObs p c)
      (p0d5cTopTiming p) (fgsaInterface p c) p0d5cTopPair (recoveryStart p E) p.k i m start dl) :
    FrontierHG3Result p c E rho i m start dl := by
  apply (frontierHG3Result_iff p c E rho i m start dl).mpr
  rcases h with h | h | ⟨t, h1, h2, hs⟩
  · exact Or.inl ((firstPhaseStopBy_iff p c E rho i m dl).mpr h)
  · exact Or.inr (Or.inl ((firstRiseStopBy_iff p c E rho i m dl).mpr h))
  · exact Or.inr (Or.inr ⟨t, h1, h2, p0d5cTopServedBack E rho hrec repair hs⟩)


section p0d5cTopD5b
variable [Fintype V]


omit [Fintype V] in
private abbrev p0d5cTopBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5cTopCore p c) (p0d5cTopSafety p c) (p0d5cTopObs p c)
    (p0d5cTopTiming p) E rho (fgsaInterface p c) (p0d5cTopWire p c) p.E
    p0d5cTopDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5cTopCarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5cTopDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5cTopPayload o s N ((p0d5cTopDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5cTopBatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5cTopBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5cTopCarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5cTopSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5cTopFoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5cTopFault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5cTopSafety p c) rho) < p.E.q := by
  classical
  let S := p0d5cTopSafety p c
  have linked : Function.Injective (FGCompose.safetyHolder S rho) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hsub : (FGCompose.historyFaulty S rho).image (FGCompose.safetyHolder S rho) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hc := (Finset.card_image_of_injective _ linked).symm.trans_le
    (Finset.card_le_card hsub)
  have hw : p.E.weightOf (FGCompose.historyFaulty S rho) =
      (FGCompose.historyFaulty S rho).card := by
    delta Electorate.weightOf
    simp only [show ∀ i, p.E.weight i = 1 from fun _ => rfl, Finset.sum_const,
      smul_eq_mul, mul_one]
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt faultQ.lt

-- Proposal leaf: the actual carrier and the post-clock parent read (PromotionCarrier route).
private theorem p0d5cTopRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5cTopCore p c) (p0d5cTopSafety p c) E rho
      (p0d5cTopObs p c) (fgsaInterface p c) p0d5cTopDecode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5cTopWindow (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5cTopDecode NamedProposal.erase NamedProposal.rows) s
      (eraseFG X) rows ∧ X.rows = rows.filterMap RowWire.toRow?) ∧ _
  rw [hXQ]
  obtain ⟨j, N, heN, hj, hem, hst, _hslot, hb, hrows⟩ :=
    healing_promotion_proposal_read p c E rho hrec.base.valid.toScheduleWellFormed hQX
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v)
    (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : Q.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk Q N.rows = true := by
    rw [hb, hrows]
    exact rowsOk_node_packBody _ _ _ _ _
  have hne : Q ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st Q.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  have hXeq : X = fgBlock P Q N.rows :=
    eraseFG_injective (hXQ.trans (eraseFG_fgBlock hne (hPe.trans hpar.symm) N.rows hok).symm)
  subst hXeq
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  have hdec : p0d5cTopDecode o = some (s, N) :=
    (p0d5cTopDecode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5cTopR6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5cTopSafety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5cTopOrder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5cTopCore p c) E rho (p0d5cTopObs p c) (fgsaInterface p c) := by
  intro s X height U hnew _ hpar hUP i W hW hn
  obtain ⟨Y, he, _, _, st, hst, hlookup⟩ := healing_promotion_carrier E rho hrec hnew
  have hYX : Y = X := eraseFG_injective he
  subst Y
  have hinv := (storeBundle_of_reachable p st
    (healing_promotion_proposal_reachable p c E rho hst)).cstore
  have hparent : X.parent ∈ st.fg.TF := ((fgBlockOf_spec p st hinv _ _).mp hlookup).1
  exact healing_rows_above_entry_at_height p st
    (healing_promotion_proposal_reachable p c E rho hst) .progress height U X.parent
    hparent hpar hUP i W hW hn

omit [Fintype V] in
-- Row leaf: honest rows decode and carry their holder's seat (linked seats).
private theorem p0d5cTopRowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5cTopSafety p c) E rho (p0d5cTopTiming p)
      (p0d5cTopWire p c) := by
  refine ⟨?_, ?_⟩
  · intro j x r a hrow
    obtain ⟨i, hauth⟩ := honestRow_auth p c rho E base.valid hrow
    cases a with
    | mk auth payload =>
      change auth = .seat .fg i at hauth
      subst auth
      exact ⟨_, rfl⟩
  · intro i j r a hrow
    obtain ⟨i', hauth⟩ := honestRow_auth p c rho E base.valid hrow
    have hseat : rho.seatOf (.base .fg) i' = rho.seatOf (.base .fg) i := by
      have hem := hrow.2.2
      cases a with
      | mk auth body =>
        change auth = .seat .fg i' at hauth
        subst auth
        exact ((fgsa_emitsAt_row E rho j _ _ hrow.2.1 i' body).mp hem).2.1
    have hii : i' = i := (base.linked.toCStar (.base .fg) trivial).1 hseat
    subst i'
    exact (p0d5cTopSigner_iff a i).mpr hauth

-- Construction leaf: healing_promotion_slot_proposal with the restart bound.
private theorem p0d5cTopSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    FGCompose.PromotionSlotProposal (p0d5cTopCore p c) E rho (p0d5cTopTiming p)
      (fgsaInterface p c) := by
  intro s hslot hgsts hhor
  change E.t_GST + 4 * p.Δ ≤ SA.proposalTime p.toParams s at hgsts
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    change E.t_GST + 4 * p.Δ ≤ 4 * p.Δ * (s : Int) at hgsts
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    linarith
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ hws he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hwgst : w ≤ E.t_GST := by
      by_contra hn
      exact hrec.suffixNoRestart _ hslot.2 j w hj (lt_of_not_ge hn)
        ((hws.trans hhor).trans_lt (lt_add_of_pos_right _ (by decide)))
    exact hwgst.trans hcut
  obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
    hslot (by linarith [p.deltaPos]) hhor hjoin
  exact ⟨X, hnew, hXslot⟩

omit [Fintype V] in
-- Source transfer leaf: healing_promotion_source_parent (TPerm at the source body).
private theorem p0d5cTopSourceParent (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (perm : TPerm p c E rho) :
    FGCompose.PromotionSourceParent (p0d5cTopCore p c) E rho (p0d5cTopObs p c) (p0d5cTopTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested r s X x K hready hphase hu hgate hs hnew hx hK
  have hp := healing_promotion_source_parent E rho perm hready
    ((p0d5cTopPhase_iff E rho).mp hphase) hu hgate hx hK hs hnew
  change Block.Preceq (eraseFG K) (eraseFG X).parent at hp
  rw [eraseFG_parent] at hp
  exact eraseFG_preceq_iff.mp hp

omit [Fintype V] in
private theorem p0d5cTopCovered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block} (h : OpeningCovered p c E rho r Q) :
    FGCompose.OpeningCovered (p0d5cTopCore p c) (p0d5cTopSafety p c) E rho
      (heightView p) (p0d5cTopTiming p) (p0d5cTopWire p c).heightPair r Q := by
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
  have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
  exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

omit [Fintype V] in
private theorem p0d5cTopParentSlot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hne : W ≠ .genesis) :
    W.parent.slot < W.slot := by
  have hm := ((cstoreInv_stateBefore E rho i x).baseTree (eraseFG W)).mpr ⟨W, hW, rfl⟩
  obtain ⟨w, hw, hb, j, o, t, _, hd, ho, _⟩ :=
    fgsa_stored_block_origin E rho i x (eraseFG W) hm (by
      intro he; exact hne (eraseFG_eq_genesis.mp he))
  obtain ⟨s, N, rfl, _, _, _⟩ :=
    (metaInv_stateBefore E rho i x).wireTree w hw
  have hQ : N.erase = eraseFG W := Option.some.inj hb
  have hf := hv.wire j x o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : N.erase.parent.slot < N.erase.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rwa [hQ, eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [Fintype V] in
private theorem p0d5cTopAncestorSlot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) {U K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hUK : FGBlock.Preceq U K) :
    U.slot ≤ K.slot := by
  induction K with
  | genesis => obtain rfl := KitFG.preceq_genesis.mp hUK; exact le_rfl
  | node P s root body rows ih =>
      by_cases he : U = .node P s root body rows
      · subst U; exact le_rfl
      · have hUP := KitFG.preceq_parent_of_preceq_node hUK he
        have hP := (cstoreInv_stateBefore E rho i x).fg.closed _ hK
        exact (ih hP hUP).trans
          (p0d5cTopParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5cTopAncestor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hUK : FGBlock.Preceq U K) : U.slot ≤ K.slot := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).1
    have hs := ((KitFG.mem_filteredFromView _ _ _ _).mp hm).1
    change K ∈ (clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at hs
    rw [clock_fg] at hs
    exact p0d5cTopAncestorSlot E rho hrec.base.valid i x hs hUK



end p0d5cTopD5b

-- Common opening leaf: TCommon at the exact-service seed (CommonEntry producer).
private theorem p0d5cTopCommon [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (common : TCommon p c E rho) :
    ∀ u m J contested q Q Qfg r, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cTopCore p c).erase Qfg = Q →
      FGCompose.FrontierProposalService (p0d5cTopCore p c) E rho (p0d5cTopTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cTopTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R → (∀ r', q ≤ r' * p.R → r ≤ r') →
      FGCompose.PhaseInterval (p0d5cTopCore p c) E rho (p0d5cTopObs p c) u (p.actionTime r) m J
        contested →
      FGCompose.OpeningCovered (p0d5cTopCore p c) (p0d5cTopSafety p c) E rho (heightView p)
        (p0d5cTopTiming p) p0d5cTopPair r Q ∧
      ((heightView p Qfg).h = m - 1 →
        FGCompose.OpeningEntry (p0d5cTopCore p c) E rho (heightView p) (p0d5cTopTiming p) r (m -
          1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
          (heightView p K).h = m) := by
  intro u m J contested q Q Qfg r hready hQ he _ hseed hu hqr hfirst hp
  have hp' := (p0d5cTopPhase_iff E rho).mp hp
  have hga : SA.gateTime p.toParams q ≤ p.actionTime r := by
    have := (common_first_time_bound (p := p) q r hqr hfirst).1
    linarith
  have hexact := p0d5cTopExact E rho hrec repair hready ((p0d5cTopSeed_iff E).mp hseed) hp' hga hQ
  obtain ⟨_, _, hc, _, _, hlowOr⟩ := common u m J contested q Q Qfg r hready hQ he hexact hu
    hqr hfirst hp'
  refine ⟨p0d5cTopCovered E rho hc, fun hlow => ?_⟩
  rcases hlowOr hlow with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

-- Stored-slot leaf of an honest proposal's own slot (repair_proposal_slot).
private theorem p0d5cTopProposalSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    ∀ q Q K, HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cTopCore p c).erase K = Q →
      K.slot = q := by
  intro q Q K hQ he
  have h := repair_proposal_slot E rho hQ
  rw [← he] at h
  change (eraseFG K).slot = q at h
  rwa [eraseFG_slot] at h

-- Justified-source leaf: the frozen QC origin (Descent).
private theorem p0d5cTopJustified [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (origin : RQCOrigin p c E rho) :
    ∀ i x, x ∈ rho.honest → ((p0d5cTopCore p c).core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ FGCompose.HonestRowAt (p0d5cTopSafety p c) E rho (p0d5cTopTiming p) j y
        r a ∧
        actionSourceFG p c E rho y r = some (some K) ∧
        (heightView p K).T_h = ((p0d5cTopCore p c).core (rho.stateBefore E i x)).fg.J := by
  intro i x hx hj
  obtain ⟨K, _, ⟨j, y, r, a, hji, ha, hK, _⟩, _, hT, _⟩ :=
    healing_justified_source (hroots := hrec.base.idealization) p c E rho
      hrec.base.valid.toScheduleWellFormed origin hx hj
  exact ⟨j, y, r, a, K, hji, ha, hK, hT⟩

-- Proposer frame leaf: the proposer's parent lies in its full tree above the root.
private theorem p0d5cTopParentFrame [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) :
    ∀ q Q, HonestProposal E rho (fgsaInterface p c) q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) q)
        (SA.proposalTime p.toParams q)) ∧
      ∀ Qfg, (p0d5cTopCore p c).erase Qfg = Q → FGBlock.Preceq
        ((p0d5cTopObs p c).controls (rho.stateBefore E j
          (V2.D.proposerOf rho (fgsaInterface p c) q))).Z Qfg.parent := by
  intro q Q hQ
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _, hst, _, _, _⟩ := healing_promotion_proposal_read p c E rho hs hQ
  refine ⟨j, hj, fun Qfg he => ?_⟩
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (rho.stateBefore E j x) (SA.proposalTime p.toParams q)).st
  have hx := hQ.1.2
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, hB, heB⟩ := healing_proposal_full_witness p c E rho hs hQ hst hne
  have hBQ : B = Qfg.parent := eraseFG_injective
    (heB.trans (by rw [← eraseFG_parent]; exact congrArg Block.parent he.symm))
  have hZB := ((KitFG.mem_filteredFromView _ _ _ _).mp hB).2.2.1
  have hc : FGSA.controls p st = FGSA.controls p (rho.stateBefore E j x).st := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho j x).fg
    rw [hfg]
  change FGBlock.Preceq (FGSA.controls p (rho.stateBefore E j x).st).Z Qfg.parent
  rw [← hc, ← hBQ]
  exact hZB


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME an accepted nonzero J has an
actual earlier honest source; its slot is at least 6Δ before the start. -/
theorem frontierSearch_initial_J_age [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (origin : RQCOrigin p c E rho)
    {i : Nat} {ev : V2.Event V (Obj p)} {x : V}
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest)
    (hj : (storeAt p c E rho (i + 1) x).fg.h_j ≠ 0) :
    SA.proposalTime p.toParams (storeAt p c E rho (i + 1) x).fg.J.slot ≤
      ev.time - 6 * p.Δ := by
  exact FGCompose.frontierSearch_initial_J_age (p0d5cTopCore p c) (p0d5cTopSafety p c)
      (p0d5cTopObs p c)
    (p0d5cTopTiming p) E rho p.E (fgCertificateLaws p) (p0d5cTopTimingLaws p)
    hrec.base.valid.toScheduleWellFormed (p0d5cTopJustified E rho hrec origin)
    (fun r x K hx hK => healing_source_slot p c E rho hx hK)
    (fun r x K A _ hK hAK => p0d5cTopAncestor E rho hrec.toRecovery₂ hK hAK) hi hx hj

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 top J; run 2 R2-b.
DC: SAME keep both E_jF branches. The actual accepted J supplies its age;
no ExactService-to-seed reconstruction or E_jF collapse is used. -/
theorem frontier_hg3_topJ [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) (monoAll : RMonoAll p
      c E rho)
    (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .topJ)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_jF p ΔF G ρbar ≤ rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time (ev.time + E_jF p ΔF G ρbar) := by
  have hk : 1 ≤ p.k := by have := p.kLarge; omega
  have hJst : E.t_GST ≤ recoveryStart p E := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  exact p0d5cTopResultBack E rho hrec repair (FGCompose.frontier_hg3_topJ (p0d5cTopCore p c)
      (p0d5cTopSafety p c) (p0d5cTopObs p c) (p0d5cTopTiming p) E rho
    (fgsaInterface p c) (p0d5cTopWire p c) p.E p0d5cTopDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H))
    (fun _ s H => p0d5cTopWindow (parentFoldState p s H)) (recoveryStart p E) p.k
    (p0d5cTopObsLaws p c) (fgCertificateLaws p)
    (fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (fgJustificationLaws p)
    (fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1) p.deltaPos (p0d5cTopCoreLaws p c)
    (fun h => eraseFG_preceq h) (fun nd => joinedNow p nd.st) (TargetReceiptService E rho)
    (p0d5cTopTimingLaws p) hk crossing hrec.base.valid.toScheduleWellFormed
    ⟨monoAll⟩ hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    (fun _ ht => healing_ready_read_cutoff E ht)
    (fun j e m hj hr hm hf hh => p0d5cTopReceipts E rho
      (healing_phase_witness_receipts_recovery E rho hrec j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W d y hy hr)
    (p0d5cTopFault rho hrec.base faultQ) hrec.deltaF hrec.base.delta
    (fun t ht hh => by
      obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
      rw [proposalTime_fgsa] at hlo hhi
      exact ⟨s, hlo, hhi, hs⟩) hJst hrec.gapPos (p0d5cTopSlot E rho hrec)
    (p0d5cTopRead E rho hrec.toRecovery₂) (p0d5cTopOrder E rho hrec.toRecovery₂)
    (p0d5cTopRowSigner E rho hrec.base) (p0d5cTopSourceParent E rho perm) hδ ⟨hbound.1⟩ rowsReceipt
    (fun r' y U' X' hb hy => progressCoverage r' y U' X'
      (p0d5cTopBatchFrom E rho ΔF hrec.base faultQ r' y U' X' hb) hy)
    (p0d5cTopFoldAdvance hfold)
    ⟨honestSeats p c rho, fun i hi => (kmid_honestSeats_mem p c rho i).mp hi, honestQuorum⟩
    (fun r x y K L hx hy hK hL he => rootScope_eq hrec.base.idealization
      (rootScope_entry (rootScope_source hx hK)) (rootScope_entry (rootScope_source hy hL)) he)
    (fun r x K hx hK => healing_source_slot p c E rho hx hK)
    (fun r x K A _ hK hAK => p0d5cTopAncestor E rho hrec.toRecovery₂ hK hAK)
    (fun A B h => eraseFG_preceq_iff.mp h) (p0d5cTopFloor E rho hrec crossing) (p0d5cTopGateCopy E
      rho hrec repair)
    (p0d5cTopService E rho hrec repair (p0d5cTopRoute E rho hrec monoAll crossing))
    (p0d5cTopCommon E rho hrec repair common)
    (p0d5cTopJustified E rho hrec origin) (p0d5cTopParentFrame E rho hrec crossing)
    (p0d5cTopStart E rho hstart) (p0d5cTopAllowance E rho hrec repair mode) hhor)

end AvailableChain.FGSA.Run
end
