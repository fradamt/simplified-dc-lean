module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.FrameZero

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME receipt and batch count in the actual pools, without a phase or cap.
Root coverage has producer postReset_root_heads_at_cut. Target coverage has
producers postReset_source_heads_at_cut and postReset_liveLease_heads_at_cut.
The pivot floor and coverage are the C3 fields. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem cone_pool_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME held honest HEAD in the receiver store before its early deadline.
The F bound follows from root HEAD coverage or the strict target arm. -/
theorem postReset_head_receipt_at_cut [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {r : Slot} {jz j : Nat} {z x : V} {t : Time}
    (hz : z ∈ rho.honest)
    (hjz : rho.events[jz]? = some (.tick z (SA.voteTime p.toParams r)))
    (hx : x ∈ rho.honest) (ht : rho.events[j]? = some (.tick x t))
    (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hdeadline : SA.voteTime p.toParams r + p.Δ ≤ t)
    (hF : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F)
      (headVote p (clock p (storeAt p c E rho jz z) (SA.voteTime p.toParams r)) r)) :
    ∃ Kfg, Kfg ∈ (storeAt p c E rho jz z).fg.TF ∧
      eraseFG Kfg = headVote p (clock p (storeAt p c E rho jz z)
        (SA.voteTime p.toParams r)) r ∧
      Kfg ∈ (storeAt p c E rho
        (V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ)) x).fg.TF := by
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨Kfg, hKfull, heK, _⟩ := healing_full_witness_all p c E rho hS crossing hz hjz
  have hKclock := ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).1
  have hKz : Kfg ∈ (storeAt p c E rho jz z).fg.TF := by
    change Kfg ∈ (clock p (storeAt p c E rho jz z) (SA.voteTime p.toParams r)).fg.TF at hKclock
    rwa [clock_fg] at hKclock
  have hidx := healing_support_idxBefore_le p c E rho hS ht hdeadline
  have hFearly : FGBlock.Preceq (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ)) x).fg.F Kfg :=
    KitFG.preceq_trans (mono hrec.base.noRestart _ _ x hx hidx).1
      (cone_pool_lift (by rwa [heK]))
  have hreceipt := healing_held_block_receipt (hroots := hrec.base.idealization)
    p c E rho mono hrec.base.valid
    hrec.base.noRestart hrec.base.delta hrec.sync hjz hz hx hKz hgstr
    (hdeadline.trans (hS.in_horizon _ (List.mem_of_getElem? ht)).2) hFearly
  rw [Gen.V2.Duty.HoldsBefore_def,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hreceipt
  exact ⟨Kfg, hKz, heK, hreceipt⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME resolved non-equivocating honest seat in the proposer pool.
The F bound follows from root HEAD coverage or the strict target arm. -/
theorem postReset_proposal_batch_seat_at_cut [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    (mono : RMono p c E rho)
    {v : Time} (hvh : v ≤ rho.horizon)
    {r : Slot} {B : Block} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq B K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v)
    (hFHeads : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) K)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head r)) k ∈ rho.honest) :
    Gen.AC.Root.poolSupports (FGSA.clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (r + 1))).base.blocks
      (FGSA.proposerSupport (FGSA.clock p (storeAt p c E rho ip x)
        (SA.proposalTime p.toParams (r + 1))) (r + 1)) k B = true ∧
    GridCO.equivocates (FGSA.proposerVotes (FGSA.clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1))) (r + 1)) k = false := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let st := FGSA.clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))
  let z := rho.seatOf (.base (.head r)) k
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams r ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hv
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon := hvv.trans hvh
  have hawake := hrec.awake z hk _ hgstr hhorr
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk r hhorr
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams r)) r
  have hBK : Block.Preceq B K := hcover z hk K hhl
  obtain ⟨Kfg, hKz, hKe0, hrelay⟩ := postReset_head_receipt_at_cut E rho hrec mono crossing hk hjz
    hx hip hgstr hvp (hFHeads z hk K hhl)
  have hKe' : eraseFG Kfg = K := hKe0
  have hKx : Kfg ∈ (storeAt p c E rho ip x).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hip hvp) x).1 hrelay
  have hinv : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hKb : K ∈ st.base.blocks := by
    rw [← hKe']
    refine (hinv.baseTree _).mpr ⟨Kfg, ?_, rfl⟩
    change Kfg ∈ (FGSA.clock p _ _).fg.TF
    rw [clock_fg]
    exact hKx
  have hKslot : K.slot ≤ r := by
    have hm := ((cstoreInv_stateBefore E rho jz z).baseTree (eraseFG Kfg)).mpr ⟨Kfg, hKz, rfl⟩
    rw [hKe'] at hm
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hm
    have hpos : 0 < SA.voteTime p.toParams r := by
      change 0 < 4 * p.Δ * (r : Int) + p.Δ
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hjz hpos
    have hsl := Internal.slotOf_mono (p := p) (le_of_lt hn)
    have he : p.slotOf (SA.voteTime p.toParams r) = r :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ r)
    exact hb.trans (hsl.trans_eq he)
  -- The vote arrives by e_r and is kept at the proposal read.
  have hvd : SA.voteTime p.toParams r + E.Δ ≤ SA.voteTime p.toParams r + E.Δ := le_rfl
  have hdt : SA.voteTime p.toParams r + E.Δ ≤ rho.horizon := by
    rw [hDelta]
    exact (hvp.trans hv).trans hvh
  obtain ⟨dl, cut, hD, _, hlt, hdl, _, hdcut, _⟩ :=
    Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ hrec.sync
      (fgsaDelay_nonrow E.Δ _) hgstr hvd hdt
  have hdle : dl (SA.voteTime p.toParams r) ≤ SA.voteTime p.toParams r + p.Δ := by
    have h := hdl (SA.voteTime p.toParams r)
    rwa [max_self, hDelta] at h
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams r)) x).st.slot p ≤
      r + 1 := by
    have h := healing_support_read_window E rho hS hN hip _ (hdle.trans hvp)
    have he : p.slotOf (SA.proposalTime p.toParams (r + 1)) = r + 1 := by
      have h0 := slotOf_offset p (r + 1) 0 le_rfl (by positivity)
      rw [add_zero] at h0
      exact h0
    exact h.trans_eq he
  have hcut : dl (SA.voteTime p.toParams r) ≤ cut := by
    refine hdle.trans (le_trans ?_ hdcut)
    rw [hDelta]
  obtain ⟨hom, _⟩ := fgsa_honest_head_receipt E rho hDelta hE hN hrec.base.cstar dl cut r k K.root
    (SA.voteTime p.toParams r) z x hD hk hem hx hcut (hlt _) hwindow
  let o := baseVote (⟨.seat (.head r) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams r)) ≤ ip :=
    healing_support_idxBefore_le p c E rho hS hip (hdle.trans hvp)
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (dl (SA.voteTime p.toParams r))) x).base.votes := by
    change o ∈ (V2.D.Run.stateBefore E rho _ x).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, _⟩ := healing_support_vote_kept E rho hN hidx x
    (SA.proposalTime p.toParams (r + 1)) o hom'
  have hFK : Block.Compatible K (eraseFG st.fg.F) := by
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (hFHeads z hk K hhl)
  have hol : GridCO.headLabel? o = some r := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p st hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho ip x)))
    o ((actView_blocks st K).mpr ⟨hKb, hFK⟩) hoK
  have hvotes : o ∈ FGSA.proposerVotes st (r + 1) := by
    change o ∈ GridCO.votesAt st.base (r + 1 - 1)
    exact List.mem_filter.mpr ⟨hod, by
      simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some r)⟩
  have hsupp : o ∈ FGSA.proposerSupport st (r + 1) := by
    apply List.mem_filter.mpr
    refine ⟨hvotes, ?_⟩
    change (match GridCO.resolvedHead? (actView st) o with
      | some C => decide (C.slot ≤ r + 1 - 1) | none => false) = true
    rw [hresolve]
    exact decide_eq_true (by simpa only [Nat.add_sub_cancel] using hKslot)
  have hvs : Gen.AC.Root.voteSupports st.base.blocks B o = true := by
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p _ hinv) o hKb hoK,
        hKb, by simpa only [hol, Option.getD_some] using hKslot, hBK⟩
  refine ⟨(Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-r vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho ip x).base r,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE ip x r k K.root _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hvat : FGSA.proposerVotes st (r + 1) = GridCO.votesAt (storeAt p c E rho ip x).base r := by
    change GridCO.votesAt st.base (r + 1 - 1) = _
    rw [Nat.add_sub_cancel]
    unfold GridCO.votesAt
    rw [(clock_vn (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))).1]
  rw [hvat]
  cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho ip x).base r) k with
  | false => rfl
  | true =>
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (Gen.AC.Root.cap_pair _ k).mp he
    exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME resolved non-equivocating honest seat in the frozen HEAD pool.
The F bound follows from root HEAD coverage or the strict target arm. -/
theorem postReset_head_batch_seat_at_cut [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    (mono : RMono p c E rho)
    {v : Time} (hvh : v ≤ rho.horizon)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
    (hFHeads : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) K)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head i)) k ∈ rho.honest) :
    Gen.AC.Root.poolSupports (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.blocks
      (FGSA.headSupport p (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))) (i + 1)) k B = true ∧
    GridCO.equivocates (FGSA.headVotes p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1)) k = false := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  let z := rho.seatOf (.base (.head i)) k
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams i ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hv
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon := hvv.trans hvh
  have hawake := hrec.awake z hk _ hgsti hhori
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk i hhori
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams i)) i
  have hBK : Block.Preceq B K := hcover z hk K hhl
  obtain ⟨Kfg, hKz, hKe0, hrelay⟩ := postReset_head_receipt_at_cut E rho hrec mono crossing hk hjz
    hy hiy hgsti hvi (hFHeads z hk K hhl)
  have hKe' : eraseFG Kfg = K := hKe0
  have hfz : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hWf : Kfg ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams i) y).st.fg.TF := by
    have h := hrelay
    have hc := (fgsa_store_cumulative p c E rho hN
      (healing_phase_idxBefore_mono p c rho hfz) y).1 h
    change Kfg ∈ (V2.D.Run.stateBefore E rho _ y).st.fg.TF at hc
    rwa [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hc
  have hpath := healing_support_prefreeze_path E rho hS hN hiy hWf Kfg (KitFG.preceq_refl _)
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hKb : K ∈ dst.base.blocks := by
    rw [← hKe']
    exact (hinv.baseTree _).mpr ⟨Kfg, hpath.1, rfl⟩
  have hKst : GridCO.stampBlock dst.base K < SA.freezeTime p.toParams i := by
    rw [← hKe']
    exact hpath.2
  -- The HEAD block has slot at most i.
  have hKslot : K.slot ≤ i := by
    have hm := ((cstoreInv_stateBefore E rho jz z).baseTree (eraseFG Kfg)).mpr ⟨Kfg, hKz, rfl⟩
    rw [hKe'] at hm
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hm
    have hpos : 0 < SA.voteTime p.toParams i := by
      change 0 < 4 * p.Δ * (i : Int) + p.Δ
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hjz hpos
    have hsl := Internal.slotOf_mono (p := p) (le_of_lt hn)
    have he : p.slotOf (SA.voteTime p.toParams i) = i :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ i)
    exact hb.trans (hsl.trans_eq he)
  -- The vote arrives by e_i and keeps its stamp at the v_(i+1) read.
  have hvd : SA.voteTime p.toParams i + E.Δ ≤ SA.voteTime p.toParams i + E.Δ := le_rfl
  have hdt : SA.voteTime p.toParams i + E.Δ ≤ rho.horizon := by
    rw [hDelta]
    exact (hvi.trans hv).trans hvh
  obtain ⟨dl, cut, hD, _, hlt, hdl, _, hdcut, _⟩ :=
    Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ hrec.sync
      (fgsaDelay_nonrow E.Δ _) hgsti hvd hdt
  have hdle : dl (SA.voteTime p.toParams i) ≤ SA.voteTime p.toParams i + p.Δ := by
    have h := hdl (SA.voteTime p.toParams i)
    rwa [max_self, hDelta] at h
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams i)) y).st.slot p ≤
      i + 1 := by
    have h := healing_support_read_window E rho hS hN hiy _ (hdle.trans hvi)
    have he : p.slotOf (SA.voteTime p.toParams (i + 1)) = i + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho iy y) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ (i + 1))
    exact h.trans_eq he
  have hcutd : dl (SA.voteTime p.toParams i) ≤ cut := by
    refine hdle.trans (le_trans ?_ hdcut)
    rw [hDelta]
  obtain ⟨hom, hos⟩ := fgsa_honest_head_receipt E rho hDelta hE hN hrec.base.cstar dl cut i k K.root
    (SA.voteTime p.toParams i) z y hD hk hem hy hcutd (hlt _) hwindow
  let o := baseVote (⟨.seat (.head i) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams i)) ≤ iy :=
    healing_support_idxBefore_le p c E rho hS hiy (hdle.trans hvi)
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (dl (SA.voteTime p.toParams i))) y).base.votes := by
    change o ∈ (V2.D.Run.stateBefore E rho _ y).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, hods⟩ := healing_support_vote_kept E rho hN hidx y
    (SA.voteTime p.toParams (i + 1)) o hom'
  have hstampv : GridCO.stampVote dst.base o < SA.freezeTime p.toParams i := by
    change GridCO.stampVote (FGSA.clock p _ _).base o < _
    rw [hods]
    change GridCO.stampVote (V2.D.Run.stateBefore E rho _ y).st.base o < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact lt_of_lt_of_le hos (hdle.trans hfz)
  have hFK : Block.Compatible K (eraseFG dst.fg.F) := by
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (hFHeads z hk K hhl)
  have hol : GridCO.headLabel? o = some i := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p dst hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho iy y)))
    o ((actView_blocks dst K).mpr ⟨hKb, hFK⟩) hoK
  -- The vote is in the frozen support arm and supports B.
  have hsupp : o ∈ FGSA.headSupport p dst (i + 1) := by
    change o ∈ List.eraseDups (_ ++ _)
    rw [List.mem_eraseDups, List.mem_append]
    left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hod, ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some i)
    · unfold GridCO.resolvedBefore
      rw [hresolve]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel,
        hol, Option.getD_some]
      exact ⟨⟨hKslot, hstampv⟩, hKst⟩
  have hvs : Gen.AC.Root.voteSupports dst.base.blocks B o = true := by
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p _ hinv) o hKb hoK,
        hKb, by simpa only [hol, Option.getD_some] using hKslot, hBK⟩
  refine ⟨(Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-i vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho iy y).base i,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE iy y i k K.root _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hnoeq : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = false := by
    cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k with
    | false => rfl
    | true =>
      obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (Gen.AC.Root.cap_pair _ k).mp he
      exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne
  cases he : GridCO.equivocates (FGSA.headVotes p dst (i + 1)) k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (Gen.AC.Root.cap_pair _ k).mp he
    have hprov := fgsa_headVotes_provenance E rho hE hN iy y i hiy
    have hone : ∀ w ∈ FGSA.headVotes p dst (i + 1), GridCO.headSeat? w = some k → w = o := by
      intro w hw hwk
      rcases hprov w hw k hwk with hm | heq
      · exact hall w hm hwk
      · change GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = true at heq
        rw [hnoeq] at heq
        contradiction
    exact hne ((hone a ha hka).trans (hone b hb hkb).symm)

end AvailableChain.FGSA.Run
end
