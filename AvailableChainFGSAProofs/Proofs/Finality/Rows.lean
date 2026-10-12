module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGCompose.Proofs.SourceHead
public import AvailableChainFGCompose.Proofs.ServiceTransport
public import AvailableChainFGSAProofs.Proofs.Shared.Gate
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSA.Proofs.EmissionFields
public import AvailableChainKitFG.HeightHistoryTransfer
public import AvailableChainFGSA.Proofs.WindowRetention

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem rows_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  have hnd' : FGCompose.postClock E rho x t = some nd := by
    rw [← (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1]
    exact hnd
  exact FGCompose.postClock_tick E rho hnd'

private def c2_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def c2_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private def c2_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def c2_reads (w : HealingWitness) : FGCompose.FGACServiceReads V where
  honest x := x ∈ rho.honest
  proposal := HonestProposal E rho (fgsaInterface p c)
  proposalTime := SA.proposalTime p.toParams
  voteTime := SA.voteTime p.toParams
  gateTime := SA.gateTime p.toParams
  gateLabel q := q * p.R
  actionHeadLabel q := q * p.R + 1
  actionTime := p.actionTime
  proposalScope s _ := w.sStar + 2 ≤ s
  sourceScope x r B := ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
    eraseFG C = B ∧ high p w C
  headScope x s := joinedAt p E rho x s (SA.voteTime p.toParams s)
  gateScope x s := confirmedReaderAtIdx p c E rho x
    (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s)
  actionScope x q := ∃ nd, postClock E rho x (p.actionTime q) = some nd
  headAtLabel := headAtLabel p c E rho
  actionHead x q := (postClock E rho x (p.actionTime q)).map
    (fun nd => (fgBlockOf nd.st (fgHead p nd.st)).map eraseFG)
  gate := gateResult p c E rho
  source := actionSource p c E rho
  parent := proposalHeadAt p c E rho
  gateFloor x s := (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F)
  frame x q B := ∀ nd, postClock E rho x (p.actionTime q) = some nd →
    ∃ D, eraseFG D = B ∧ D ∈ nd.st.fg.TF ∧
      FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h
  below := Block.Preceq

private theorem c2_observation_laws (w : HealingWitness) :
    FGCompose.FGACServiceObservationLaws (c2_reads p c E rho w) (c2_timing p)
      (fgsaCoreReads p c) (c2_observations p c) E rho (fgsaInterface p c)
      (gateResult p c E rho)
      (fun x s => (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F))
      (proposalHeadAt p c E rho) (fun s _ => w.sStar + 2 ≤ s)
      (fun x r B => ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        eraseFG C = B ∧ high p w C)
      (fun x s => joinedAt p E rho x s (SA.voteTime p.toParams s))
      (fun x s => confirmedReaderAtIdx p c E rho x
        (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s))
      (fun x q => ∃ nd, postClock E rho x (p.actionTime q) = some nd) where
  honest_eq _ := Iff.rfl
  proposal_eq _ _ := Iff.rfl
  proposal_time _ := rfl
  duty_time _ := rfl
  vote_time _ := rfl
  gate_time _ := rfl
  action_time _ := rfl
  gate_label _ := rfl
  action_head_label _ := rfl
  head_eq _ _ := by rw [fgsaCoreReads_def]; rfl
  action_head_eq _ _ := by rw [fgsaCoreReads_def]; rfl
  source_eq x q := by
    rw [fgsaCoreReads_def]
    change ((postClock E rho x (p.actionTime q)).map
      (fun nd => FGSA.fgSource p nd.st)).map (Option.map eraseFG) = _
    rw [Option.map_map]
    rfl
  gate_eq _ _ := rfl
  parent_eq _ := rfl
  floor_eq _ _ := rfl
  below_eq _ _ := Iff.rfl
  proposal_scope _ _ := Iff.rfl
  source_scope _ _ _ := Iff.rfl
  head_scope _ _ := Iff.rfl
  gate_scope _ _ := Iff.rfl
  action_scope _ _ := Iff.rfl
  frame_eq _ _ _ := by
    dsimp only [c2_observations, c2_reads]
    rw [fgsaCoreReads_def]
    rfl

private theorem c2_history_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c) (c2_observations p c)
      (c2_timing p) E rho (fgsaInterface p c) (c2_point p w) horizon := by
  intro x r C hx hC hh _ v Q hQ _ hgap
  rw [fgsaCoreReads_def] at hC ⊢
  exact h x r C v Q hx hC hh hQ hgap

private theorem c2_history_chain (w : HealingWitness) (h : THigh p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (c2_observations p c)
      (c2_timing p) E rho (c2_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [fgsaCoreReads_def] at hC hD ⊢
  exact h x y r q C D hx hy hC hD hc hd

private theorem c2_service_laws (w : HealingWitness)
    (h1 : THigh p c E rho w) (h2 : TCarrier p c E rho w)
    (h2p : H2Prime p c E rho w) (h2a : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h6 : H6GateService p c E rho w) :
    FGCompose.FGACServiceLaws (c2_reads p c E rho w) (c2_point p w)
      (recoveryStart p E) rho.horizon where
  source_chain := by
    intro x y r q C D hx hy hc hd _ _ _ _
    obtain ⟨C', hs, he, hh⟩ := hc
    obtain ⟨D', ht, hf, hk⟩ := hd
    subst C D
    exact (h1 x y r q C' D' hx hy hs ht hh hk).1
  exact_head := by
    intro s Q x hQ hs _ hh hx hr
    exact (h3 s Q hQ hs).1 hh x hx hr
  exact_gate := by
    intro s Q x hQ hs _ hh hx hr
    exact ((h3 s Q hQ hs).2 hh x hx hr).1
  opening_source := by
    intro q Q x hQ hs _ hh hx _ hr
    exact ((h3 (q * p.R) Q hQ hs).2 hh x hx hr).2.2.2.2 q rfl
  proposal_later_head := by
    intro s Q x i H hQ hs _ hx hr hi _ hH
    exact h2p s Q hQ hs x i H ⟨hx, hr⟩ hi hH
  source_next_head := by
    intro y r C x i H hy hc _ _ hx hr hi _ hH
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact (h2a y r C' hy hs hh).1 x i H ⟨hx, hr⟩ hi hH
  covered_source := by
    intro s Q q x _ _ _ hne _ _ ht hs hGST hheads hfloor hx _ hframe
    have hcover : ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y (q * p.R) = some H ∧ Block.Preceq Q H := by
      intro y hy
      obtain ⟨H, _, hH, hQ⟩ := hheads y hy
      exact ⟨H, hH, hQ⟩
    have hF : ∀ y st, y ∈ rho.honest → gateIn p c E rho y (q * p.R) = some st →
        Block.Preceq (eraseFG st.fg.F) Q := by
      intro y st hy hst
      exact hfloor y (eraseFG st.fg.F) hy (by
        change (gateIn p c E rho y (q * p.R)).map _ = _
        rw [hst, Option.map_some])
    obtain ⟨_, _, nd, d, hnd, hwrite, hlease, _, hlive⟩ :=
      h6 (q * p.R) Q hs hGST ht.2 hne hcover hF x hx
    obtain ⟨D, hD, hmem, hFD, hZD, hlo⟩ := hframe nd hnd
    obtain ⟨j, _, hclock⟩ := rows_clock_read p c E rho x (p.actionTime q) nd hnd
    have hkept : D ∈ domainR p nd.st (treeT p nd.st) := by
      rw [domainR_def, treeT_def, frameR_def]
      exact (KitFG.mem_filteredFromView (heightView p) _ _ D).mpr
        ⟨hmem, hFD, hZD, D, hmem, KitFG.preceq_refl D, hlo⟩
    have hround : p.round (nd.st.slot p) = q := by
      rw [← hclock]
      exact (fgsa_action_slot_round (c := c) _ q).2
    have hnow : nd.st.base.now = p.actionTime q := by
      rw [← hclock]
      exact (fgsa_postClock_slot (c := c) _ _).1
    have hserved : eraseFG D ∈ sourceCandidates p nd.st := by
      rw [sourceCandidates_def, hround, hD]
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hwrite,
        by rw [hlease]; exact decide_eq_true (hnow ▸ hlive)⟩
    rw [← hclock] at hkept hserved
    obtain ⟨C, hsource, hDC⟩ := openingSource_extends_served E rho j x q D hkept hserved
    change FGSA.fgSource p (((fgsa p c).clock _ _).st) = some C at hsource
    rw [hclock] at hsource
    refine ⟨eraseFG C, ?_, ?_⟩
    · change actionSource p c E rho x q = some (some (eraseFG C))
      change postClock E rho x (p.actionTime q) = some nd at hnd
      delta actionSource
      simp only [actionSourceFG, hnd, Option.map_some, hsource]
    · change Block.Preceq Q (eraseFG C)
      rw [← hD]
      exact eraseFG_preceq hDC
  parent_transfer := by
    intro x r C s Q hx hc _ _ hQ _ hgap _
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact h2 x r C' s Q hx hs hh hQ hgap

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1254: the full action walk covers D and keeps the pending fields.
DC: INTENTIONAL: height plateau and a separate finality-lag bound; no exact head body. -/
private theorem rows_pending_action_head
    (k : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = y + 1)
    (hDJ : (heightView p D).J = U)
    (hDj : (heightView p D).h_j = y)
    (hcap : ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1)
    (hfin : ∀ B ∈ nd.st.fg.TF, (finalityView p B).h_F < y) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq D H ∧
      (heightView p H).h = y + 1 ∧
      (heightView p H).J = U ∧
      (heightView p H).h_j = y ∧
      (finalityView p H).h_F < y ∧
      (heightView p H).T_h = (heightView p D).T_h := by
  obtain ⟨j, _hj, hclock⟩ := rows_clock_read p c E rho x (p.actionTime q) nd hnd
  have hinv : CStoreInv p nd.st := by
    rw [← hclock]
    exact (storeBundle_postClock E rho j x (p.actionTime q)).cstore
  have hcover := (hwalk k x (q * p.R + 1) raw support D seats m hx hcount
    (by simpa only [hread] using hD) (by simpa only [hread] using hcompat)
    (by simpa only [hread] using hbatch)).1
  rw [hread, ← hhead] at hcover
  obtain ⟨H, hH, hHe⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
  have hdecode := (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hH, hHe⟩
  have hDmem : D ∈ nd.st.fg.TF := (Finset.filter_subset _ _) hD
  have hDH := preceq_of_eraseFG_preceq (viewRootInj_TF p nd.st hinv)
    ⟨D, hDmem, KitFG.preceq_refl D⟩ ⟨H, hH, KitFG.preceq_refl H⟩
    (by simpa only [hHe] using hcover)
  have hlaws := (fgCertificateLaws p).height
  have hmono : (heightView p D).h ≤ (heightView p H).h := hlaws.h_mono hDH
  have hHh : (heightView p H).h = y + 1 := by
    exact Nat.le_antisymm (hcap H hH) (hDh ▸ hmono)
  have hplateau := KitFG.justification_eq_on_plateau_of_bridge p.E p.cfg
    (heightView p) (heightView_bridge p) hDH (hDh.trans hHh.symm)
  exact ⟨H, hdecode, hDH, hHh, hplateau.1.trans hDJ, hplateau.2.trans hDj,
    hfin H hH, (hlaws.entry_plateau hDH (hDh.trans hHh.symm)).symm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1254: the full action walk covers D; held caps bound its head fields.
DC: INTENTIONAL: public form of the capped walk step; the caller supplies both caps. -/
theorem pending_action_head_capped
    (k : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = y + 1)
    (hDJ : (heightView p D).J = U)
    (hDj : (heightView p D).h_j = y)
    (hcap : ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1)
    (hfin : ∀ B ∈ nd.st.fg.TF, (finalityView p B).h_F < y) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
      FGBlock.Preceq D H ∧
      (heightView p H).h = y + 1 ∧
      (heightView p H).J = U ∧
      (heightView p H).h_j = y ∧
      (finalityView p H).h_F < y ∧
      (heightView p H).T_h = (heightView p D).T_h :=
  rows_pending_action_head p c E rho k x q y D U nd raw support seats m hx hnd hread hwalk
    hhead hcount hD hcompat hbatch hDh hDJ hDj hcap hfin

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1236–1239,1667–1687: translate the strict causal cap to a held domain.
DC: INTENTIONAL: height-only cap through a TF inclusion at the actual read. -/
theorem pending_action_domain_cap
    (before : Nat) (x : V) (q y : Nat) (nd : Node p)
    (hx : x ∈ rho.honest)
    (hfgread : nd.st.fg.TF ⊆ (storeAt p c E rho before x).fg.TF)
    (hbefore : before ≤ V2.D.Run.idxBefore rho (p.actionTime q))
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2)
    (hrows : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime q → h < y + 1) :
    ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1 := by
  intro B hB
  exact Nat.le_of_lt_succ
    (hcapBefore (p.actionTime q) y before x B hbefore ⟨hx, hfgread hB⟩ hrows)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1254: the actual full action walk has the pending fields.
DC: INTENTIONAL: separate held-domain causal cap and finality lag, with read-index bridges. -/
theorem pending_action_head
    (k before : Nat) (x : V) (q y : Nat) (D U : FGBlock (Fin p.n))
    (nd : Node p) (raw support : List (GridCO.Wire p.n .root))
    (seats : Finset (Fin p.n)) (m : Nat)
    (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime q) = some nd)
    (hread : storeAt p c E rho k x = nd.st)
    (hfgread : nd.st.fg.TF ⊆ (storeAt p c E rho before x).fg.TF)
    (hbefore : before ≤ V2.D.Run.idxBefore rho (p.actionTime q))
    (hq : 0 < q)
    (hwalk : TWalk p c E rho)
    (hhead : FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support)
    (hcount : Gen.Pure.Batch seats.card m)
    (hD : D ∈ FGSA.fullTree p nd.st)
    (hcompat : Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG D))
    (hbatch : WalkBatch p c rho nd.st (q * p.R + 1)
      raw support (eraseFG D) seats m)
    (hDh : (heightView p D).h = y + 1)
    (hDJ : (heightView p D).J = U) (hDj : (heightView p D).h_j = y)
    (hDfin : (finalityView p D).h_F < y)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2)
    (hfinalityLag : ∀ (r y i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      0 < y → i ≤ V2.D.Run.idxBefore rho (p.actionTime (r + 1)) →
      HeldAt p c E rho i x W →
      (∀ j z s a u T timeout, HonestRowAt p c E rho j z s a →
        RowWire.toRow? a = some u → u.height_pair = .vote y T timeout →
        ¬ p.actionTime s < p.actionTime r) → (finalityView p W).h_F < y)
    (hrows : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime q → h < y + 1)
    (hnoRow : ∀ j z r a u T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote y T timeout →
      ¬ p.actionTime r < p.actionTime (q - 1)) :
    ∃ H : FGBlock (Fin p.n),
      FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧ FGBlock.Preceq D H ∧
      (heightView p H).h = y + 1 ∧ (heightView p H).J = U ∧
      (heightView p H).h_j = y ∧ (finalityView p H).h_F < y ∧
      (heightView p H).T_h = (heightView p D).T_h := by
  have held : ∀ B ∈ nd.st.fg.TF, HeldAt p c E rho before x B := by
    intro B hB
    change x ∈ rho.honest ∧ B ∈ (storeAt p c E rho before x).fg.TF
    exact ⟨hx, hfgread hB⟩
  have hcap := pending_action_domain_cap p c E rho before x q y nd
    hx hfgread hbefore hcapBefore hrows
  have hfin : ∀ B ∈ nd.st.fg.TF, (finalityView p B).h_F < y := by
    intro B hB
    exact hfinalityLag (q - 1) y before x B ((Nat.zero_le _).trans_lt hDfin)
      (by simpa only [Nat.sub_add_cancel (Nat.one_le_of_lt hq)] using hbefore)
      (held B hB) hnoRow
  exact rows_pending_action_head p c E rho k x q y D U nd raw support seats m
    hx hnd hread hwalk hhead hcount hD hcompat hbatch hDh hDJ hDj hcap hfin

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1256–1263, 1667–1687: H3 supplies the exact source at c = z;
H2′ and H6 supply a covering source at c < z, with the full filter guards.
DC: INTENTIONAL: deepest fresh FG-SA selector; height plateau fixes the same entry. -/
theorem finality_action_source (w : HealingWitness) (q y opening : Nat)
    (D : FGBlock (Fin p.n)) (hx : V) (hhonest : hx ∈ rho.honest)
    (hbefore : opening ≤ q * p.R) (hstart : w.sStar + 2 ≤ opening)
    (hproposal : HonestProposal E rho (fgsaInterface p c) opening (eraseFG D))
    (h2 : H2Prime p c E rho w) (h3 : H3 p c E rho w)
    (h6 : H6GateService p c E rho w)
    (hGST : recoveryStart p E ≤ SA.voteTime p.toParams (q * p.R))
    (hhor : p.actionTime q ≤ rho.horizon) (hne : eraseFG D ≠ .genesis)
    (hheads : ∀ x ∈ rho.honest, ∃ H,
      headAtLabel p c E rho x (q * p.R) = some H)
    (hjoined : ∀ x ∈ rho.honest,
      joinedAt p E rho x (q * p.R) (SA.voteTime p.toParams (q * p.R)))
    (hconfirmed : confirmedReaderAtIdx p c E rho hx
      (afterTicksIdx rho (SA.gateTime p.toParams opening))
      (SA.gateTime p.toParams opening))
    (hFgate : ∀ x st, x ∈ rho.honest → gateIn p c E rho x (q * p.R) = some st →
      Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hframe : ∀ nd, postClock E rho hx (p.actionTime q) = some nd →
      D ∈ nd.st.fg.TF ∧ FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h)
    (hDh : (heightView p D).h = y + 1)
    (hcap : ∀ nd, postClock E rho hx (p.actionTime q) = some nd →
      ∀ B ∈ nd.st.fg.TF, (heightView p B).h ≤ y + 1) :
    ∃ nd C, postClock E rho hx (p.actionTime q) = some nd ∧
      FGSA.fgSource p nd.st = some C ∧ FGBlock.Preceq D C ∧
      (heightView p C).h = y + 1 ∧ (heightView p C).T_h = (heightView p D).T_h := by
  have service : FGCompose.FGSourceService (fgsaCoreReads p c) E rho hx (p.actionTime q)
      opening (q * p.R) D := by
    constructor
    · intro heq
      have hexact := ((h3 opening (eraseFG D) hproposal hstart).2
        (by simpa only [heq, Params.actionTime] using hhor) hx hhonest hconfirmed).2.2.2.2
        q heq
      change (actionSourceFG p c E rho hx q).map (Option.map eraseFG) =
        some (some (eraseFG D)) at hexact
      obtain ⟨source, hs, he⟩ := Option.map_eq_some_iff.mp hexact
      obtain ⟨C, hC, hCe⟩ := Option.map_eq_some_iff.mp he
      have hCD : C = D := eraseFG_injective hCe
      subst C
      rw [hC] at hs
      rw [actionSourceFG_def] at hs
      obtain ⟨nd, hnd, hsource⟩ := Option.map_eq_some_iff.mp hs
      rw [fgsaCoreReads_def]
      rw [← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
      exact ⟨nd, hnd, hsource⟩
    · intro hlt
      have hcover : ∀ x ∈ rho.honest, ∃ H,
          headAtLabel p c E rho x (q * p.R) = some H ∧ Block.Preceq (eraseFG D) H := by
        have covered := FGCompose.service_head_coverage (A := c2_reads p c E rho w)
          hheads hjoined (fun x H hx hr hH =>
            h2 opening (eraseFG D) hproposal hstart x (q * p.R) H ⟨hx, hr⟩
              (Nat.succ_le_of_lt hlt) hH)
        intro x hx
        obtain ⟨H, _, hH, hDH⟩ := covered x hx
        exact ⟨H, hH, hDH⟩
      obtain ⟨_hresult, _hpassed, nd, d, hnd, hwrite, hlease, _hdeadline, hlive⟩ :=
        h6 (q * p.R) (eraseFG D) ((Nat.le_add_right w.sStar 2).trans
          (hstart.trans hbefore)) hGST hhor hne hcover hFgate hx hhonest
      obtain ⟨j, _hj, hclock⟩ := rows_clock_read p c E rho hx (p.actionTime q) nd hnd
      have hf := hframe nd hnd
      have hkept : D ∈ domainR p nd.st (treeT p nd.st) := by
        rw [domainR_def, treeT_def, frameR_def]
        exact (KitFG.mem_filteredFromView (heightView p) _ _ D).mpr
          ⟨hf.1, hf.2.1, hf.2.2.1, D, hf.1, KitFG.preceq_refl D, hf.2.2.2⟩
      have hround : p.round (nd.st.slot p) = q := by
        rw [← hclock]
        exact (fgsa_action_slot_round (c := c) _ q).2
      have hnow : nd.st.base.now = p.actionTime q := by
        rw [← hclock]
        exact (fgsa_postClock_slot (c := c) _ _).1
      have hserved : eraseFG D ∈ sourceCandidates p nd.st := by
        rw [sourceCandidates_def, hround]
        exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hwrite,
          by rw [hlease]; exact decide_eq_true (hnow ▸ hlive)⟩
      have hkept' := hkept
      have hserved' := hserved
      rw [← hclock] at hkept' hserved'
      obtain ⟨C, hsource, hDC⟩ := openingSource_extends_served E rho j hx q D hkept' hserved'
      change FGSA.fgSource p (((fgsa p c).clock _ _).st) = some C at hsource
      rw [hclock] at hsource
      rw [fgsaCoreReads_def]
      rw [← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
      exact ⟨nd, C, hnd, hsource, hDC⟩
  have hcap' : ∀ nd, FGCompose.postClock E rho hx (p.actionTime q) = some nd →
      ∀ B ∈ ((fgsaCoreReads p c).core nd).fg.TF, (heightView p B).h ≤ y + 1 := by
    rw [fgsaCoreReads_def]
    rw [← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1]
    exact hcap
  have h := FGCompose.action_source_capped (fgsaCoreReads p c) E rho (fgsaCoreLaws p c)
    p.E (heightView p) (fgCertificateLaws p).height hx (p.actionTime q) opening (q * p.R) y D
    service hbefore hDh hcap'
  rw [fgsaCoreReads_def, ← (fgsa_eventReads_eq_compose E rho hx _).2.2.2.2.2.1] at h
  exact h

private theorem rows_release (y : Nat) (U C : FGBlock (Fin p.n))
    (st : State p.n) (Λ : RecordOnce)
    (hsource : FGSA.fgSource p st = some C) (hC : (heightView p C).h = y + 1)
    (hfields : (FGSA.fgInputs p st).2.h_j = y ∧
      (FGSA.fgInputs p st).2.J = U.root ∧ (FGSA.fgInputs p st).2.h_F < y)
    (hrecord : (Λ.target y = none ∨ Λ.target y = some U.root) ∧
      Λ.timeout y = false ∧ (Λ.lock y = none ∨ Λ.lock y = some U.root) ∧
      Λ.target (y + 1) = none ∧ Λ.timeout (y + 1) = false ∧
      Λ.lock (y + 1) = none ∧
      (∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ NamedHeightPair.vote (y + 1) T timeout)) :
    (attest p st Λ ⟨0, p.nPos⟩).1 =
      some (.vote ⟨.vote (y + 1) (heightView p C).T_h.root false, some ⟨y, U.root⟩⟩) := by
  obtain ⟨ht, hto, hl, htn, hton, hln, hsent⟩ := hrecord
  have hfp : finality_pair Λ.toRecord (FGSA.fgInputs p st).2 = some ⟨y, U.root⟩ := by
    delta finality_pair
    simp only [hfields.1, hfields.2.1, hfields.2.2, ht, hto, hl,
      and_self, ↓reduceIte]
  have hsrc : (FGSA.fgInputs p st).1 = some C := hsource
  have hhp : height_pair Λ.toRecord
      ((FGSA.fgInputs p st).1.map
        (fun C => ((heightView p C).h, (heightView p C).T_h.root)))
      (some ⟨y, U.root⟩) = .vote (y + 1) (heightView p C).T_h.root false := by
    simp only [hsrc, Option.map_some, hC, height_pair, own_lock, hton, Bool.false_eq_true,
      ↓reduceIte, show y ≠ y + 1 from Nat.ne_of_lt (Nat.lt_succ_self y), hln, htn]
  have hsame : sameHeightOnce Λ (y + 1) (heightView p C).T_h.root false = false := by
    delta sameHeightOnce
    rw [List.any_eq_false]
    intro b hb
    cases hh : b.1 with
    | empty => simp only [Bool.false_eq_true, not_false_eq_true]
    | vote h T timeout =>
        have hne : h ≠ y + 1 := by
          intro he
          exact hsent b hb T timeout
            (hh.trans (congrArg (fun k => NamedHeightPair.vote k T timeout) he))
        simp only [hne, decide_false, Bool.false_and, Bool.false_eq_true,
          not_false_eq_true]
  have hkey : (NamedHeightPair.vote (y + 1) (heightView p C).T_h.root false,
      some (FinalityPair.mk y U.root)) ∉ Λ.sent := by
    intro hm
    exact hsent _ hm _ false rfl
  dsimp only [attest]
  rw [createRowOnce_def, attest_source_heightView, hfp]
  dsimp only
  rw [hhp]
  delta Row.onceKey RowBody.ofRow
  simp only [hsame, Bool.false_eq_true, ↓reduceIte,
    Option.filter_some, Nat.lt_succ_self, decide_true, hkey, Option.map_some]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1256–1263: awake actions release the same complete fresh rows and entry.
DC: INTENTIONAL: durable record and both send-once checks; source ancestry fixes the entry. -/
theorem fresh_unanimous_rows
    (q y : Nat) (D U : FGBlock (Fin p.n))
    (S : Finset (Fin p.n))
    (hS : S ⊆ honestSeats p c rho) (hQ : p.E.IsQuorum S)
    (hDh : (heightView p D).h = y + 1)
    (hreads : ∀ i ∈ S, ∃ nd C,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd ∧
      E.awake (rho.seatOf (.base .fg) i) (p.actionTime q) = true ∧
      FGSA.fgSource p nd.st = some C ∧
      FGBlock.Preceq D C ∧ (heightView p C).h = y + 1)
    (hfields : ∀ i ∈ S, ∀ nd,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd →
      (FGSA.fgInputs p nd.st).2.h_j = y ∧
      (FGSA.fgInputs p nd.st).2.J = U.root ∧
      (FGSA.fgInputs p nd.st).2.h_F < y)
    (hrecord : ∀ i ∈ S, ∀ nd,
      postClock E rho (rho.seatOf (.base .fg) i) (p.actionTime q) = some nd →
      (nd.record.target y = none ∨ nd.record.target y = some U.root) ∧
      nd.record.timeout y = false ∧
      (nd.record.lock y = none ∨ nd.record.lock y = some U.root) ∧
      nd.record.target (y + 1) = none ∧
      nd.record.timeout (y + 1) = false ∧
      nd.record.lock (y + 1) = none ∧
      (∀ b ∈ nd.record.sent, ∀ T timeout,
        b.1 ≠ NamedHeightPair.vote (y + 1) T timeout))
    (hearlier : ∀ i ∈ S, ∀ j r a h, r < q →
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a →
      rowHeight a = some h → h < y + 1) :
    ∃ rows : Fin p.n → RowWire p.n,
      FreshFinalityRows_W p c E rho q y U S rows ∧
      (∀ i ∈ S, namedEntry (rows i).payload.height_pair =
        some (y + 1, (heightView p D).T_h.root)) ∧
      (∀ i ∈ S, (rows i).payload.height_pair =
        NamedHeightPair.vote (y + 1) (heightView p D).T_h.root false) := by
  classical
  let body : RowPayload := .vote
    ⟨.vote (y + 1) (heightView p D).T_h.root false, some ⟨y, U.root⟩⟩
  let rows : Fin p.n → RowWire p.n := fun i => ⟨.seat .fg i, body⟩
  have hseat : ∀ i ∈ S, ∃ j C,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q (rows i) ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
      (rows i).auth = .seat .fg i ∧ rowHeight (rows i) = some (y + 1) ∧
      FinalityNames p (rows i) y U ∧
      actionSourceFG p c E rho (rho.seatOf (.base .fg) i) q = some (some C) ∧
      (heightView p C).h = y + 1 ∧
      ∀ j' r a h, r < q →
        HonestRowAt p c E rho j' (rho.seatOf (.base .fg) i) r a →
        rowHeight a = some h → h < y + 1 := by
    intro i hi
    obtain ⟨nd, C, hnd, hawake, hsource, hDC, hCh⟩ := hreads i hi
    have hentry := (fgCertificateLaws p).height.entry_plateau hDC (hDh.trans hCh.symm)
    have hem := rows_release p y U C nd.st nd.record hsource hCh
      (hfields i hi nd hnd) (hrecord i hi nd hnd)
    rw [← hentry] at hem
    obtain ⟨j, hj, hclock⟩ := rows_clock_read p c E rho
      (rho.seatOf (.base .fg) i) (p.actionTime q) nd hnd
    have hrelease : ofRow p (rows i) ∈ V2.D.Run.emitsAt E rho j := by
      apply (fgsa_emitsAt_row E rho j _ _ hj i body).mpr
      refine ⟨hawake, rfl, q, rfl, ?_⟩
      have hs := congrArg Node.st hclock
      have hr : (V2.D.Run.stateBefore E rho j (rho.seatOf (.base .fg) i)).record =
          nd.record := by
        exact (clock_rec (c := c)
          (V2.D.Run.stateBefore E rho j (rho.seatOf (.base .fg) i)) (p.actionTime q)).symm.trans
          (congrArg Node.record hclock)
      rw [show (FGSA.clock p _ _ ) = nd.st from hs, hr]
      exact hem
    have hhonest : rho.seatOf (.base .fg) i ∈ rho.honest := by
      have hmem := hS hi
      rw [honestSeats_def] at hmem
      exact (Finset.mem_filter.mp hmem).2
    refine ⟨j, C, ?_, ?_, rfl, rfl, ?_, ?_, hCh, hearlier i hi⟩
    · rw [HonestRowAt_def]
      exact ⟨hhonest, hj, hrelease⟩
    · change (decide (1 ≤ y + 1) && decide (y < y + 1)) = true ∧
        RowSigner p c rho (rows i) (rho.seatOf (.base .fg) i)
      refine ⟨by simp only [Nat.le_add_left, Nat.lt_succ_self, decide_true, Bool.and_self], ?_⟩
      rw [RowSigner_def]
      exact ⟨i, rfl, rfl⟩
    · rw [FinalityNames_def]
      rfl
    · simpa only [actionSourceFG_def, hnd, Option.map_some] using congrArg some hsource
  refine ⟨rows, ?_, ?_, ?_⟩
  · rw [FreshFinalityRows_W_def]
    exact ⟨hS, hQ, hseat⟩
  · intro i hi; rfl
  · intro i hi; rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289: bound held blocks through the next action cut.
DC: INTENTIONAL: held/read causal cap; Assembly supplies the causal-origin bound. -/
theorem actual_anchor_cap
    (q y : Nat)
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V)
        (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2)
    (hrows : ∀ j x r a u h T timeout,
      HonestRowAt p c E rho j x r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (q + 1) → h ≤ y + 1) :
    ∀ i x W, i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)) →
      HeldAt p c E rho i x W → (heightView p W).h ≤ y + 2 := by
  intro i x W hi hW
  have hbound := hcapBefore (p.actionTime (q + 1)) (y + 1) i x W hi hW
    (fun j z r a u h T timeout ha hu hp ht => by
      exact Nat.lt_succ_of_le (hrows j z r a u h T timeout ha hu hp ht))
  exact Nat.le_of_lt_succ (by simpa only [Nat.add_assoc, Nat.add_comm 1 2] using hbound)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289: keep the actual anchor key, or cover it by finality.
DC: INTENTIONAL: W retention with K_W ≥ 2; retention does not imply acceptance. -/
theorem actual_anchor_retained_or_covered
    (y : Nat) (D U P : FGBlock (Fin p.n))
    (hDP : FGBlock.Preceq D P)
    (hret : Window.RetainedW p D y U)
    (hcap : (heightView p P).h ≤ y + 2) :
    Window.RetainedW p P y U ∨ Window.CoveredW p P y U := by
  obtain ⟨e, he, hej, heX⟩ := (Window.RetainedW_def p D y U).mp hret
  have hj := (fgCertificateLaws p).height.justified_below_height P
  have hK := p.kWLarge
  have near : (Window.derive p p.K_W P).h_j < e.j + p.K_W := by
    rw [heightView_def, Window.projectHeight_def] at hj hcap
    dsimp only at hj hcap
    rw [hej]
    exact (Nat.lt_of_lt_of_le hj hcap).trans_le (Nat.add_le_add_left hK y)
  rcases Window.window_retained_or_covered p p.K_W hK D P hDP e he near with hr | hc
  · obtain ⟨f, hf, hfj, hfX, _hbits⟩ := hr
    exact Or.inl ((Window.RetainedW_def p P y U).mpr
      ⟨f, hf, hfj.trans hej, hfX.trans heX⟩)
  · apply Or.inr
    rw [Window.CoveredW_def]
    rw [hej, heX] at hc
    exact hc

end AvailableChain.FGSA.Run
end
