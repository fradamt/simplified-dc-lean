module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportFrame
public import AvailableChainFGSAProofs.Proofs.Healing.SupportHeads

public section

/-! G-HG1 capped H.1/H.2 HEAD steps (plan fgsa-s5-frontier §3.1 steps 3–4; blueprint 21
HG.1:1536–1565). These restate `healing_support_honest_batch_seat`,
`healing_next_transfer_core` and `healing_first_transfer_core` (Healing/SupportHeads.lean,
Healing/SupportTransfer.lean) with the fixed-phase frame replaced by the capped
self-witness: each witness is an honest HEAD block above the height-m pivot. The lease
premise stays explicit at each step. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem fheads_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

omit [DecidableEq V] in
private theorem fheads_idxBefore_le_timeIdx (rho : V2.D.Run V (fgsa p c)) {t v : Time}
    (htv : t ≤ v) : V2.D.Run.idxBefore rho t ≤ timeIdx rho v := by
  change (rho.events.filter (fun e => decide (e.time < t))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ v))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).le.trans htv))

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1529–1534, H.2 S1:709–715; plan §3.1 step 4 (restates
`healing_support_honest_batch_seat`). DC: INTENTIONAL under the cap, an honest label-i
HEAD that covers the pivot and B is, at the receiver's v_(i+1) read, a clean resolved
frozen vote that supports B. The HEAD block itself is the relayed witness. -/
theorem frontier_head_batch_seat [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head i)) k ∈ rho.honest) :
    Gen.AC.poolSupports (FGSA.clock p (storeAt p c E rho iy y)
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
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ timeIdx rho v :=
    fheads_idxBefore_le_timeIdx rho (hvi.trans hv)
  -- The HEAD block itself is the witness; it reaches y before e_i (capped relay).
  obtain ⟨Kfg, hKz, hKe0, _, hrelay⟩ := frontier_head_relay (hroots := hrec.base.idealization)
    E rho crossing hE hN hDelta
    hrec.sync hQm hcap hk hjz hgsti (hcoverQ z hk K hhl) ((hvi.trans hv).trans hvh) hcut
  have hKe' : eraseFG Kfg = K := hKe0
  have hfz : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hWf : Kfg ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams i) y).st.fg.TF := by
    have h := hrelay y hy
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
  obtain ⟨hom, hos⟩ := fgsa_honest_head_receipt E rho hDelta hE hN hrec.base.cstar dl cut i k K
    (SA.voteTime p.toParams i) z y hD hk hem hy hcutd (hlt _) hwindow
  let o := baseVote (⟨.seat (.head i) k, K⟩ : HeadWire p.n)
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
  -- The receiver finality is below the height-m HEAD block (RXing under the cap).
  have hiyv : iy ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hiy hv).le
  have hjziy : jz ≤ iy := by
    have h1 : jz < V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hjz _).mpr (lt_add_of_pos_right _ p.deltaPos)
    exact h1.le.trans (healing_support_idxBefore_le p c E rho hS hiy hvi)
  have hFK0 := frontier_F_below E rho crossing hN hy (hcap iy y hiyv hy) hk hjziy hKz
    (frontier_height_eq E rho hQm (hcap jz z (hjziy.trans hiyv) hk) hKz
      (hKe' ▸ hcoverQ z hk K hhl)).1.ge
  have hFK : Block.Compatible K (eraseFG dst.fg.F) := by
    rw [clock_fg]
    rw [← hKe']
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (eraseFG_preceq hFK0)
  have hol : GridCO.headLabel? o = some i := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K := rfl
  -- The vote is in the frozen support arm and supports B.
  have hsupp : o ∈ FGSA.headSupport p dst (i + 1) := by
    change o ∈ List.eraseDups (_ ++ _)
    rw [List.mem_eraseDups, List.mem_append]
    left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hod, ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some i)
    · unfold GridCO.resolvedBefore
      rw [hoK]
      simp only [Bool.and_eq_true, decide_eq_true_eq, GridCO.blockKnown, Nat.add_sub_cancel,
        hol, Option.getD_some]
      exact ⟨⟨⟨(actView_blocks dst K).mpr ⟨hKb, hFK⟩, hKslot⟩, hstampv⟩, hKst⟩
  have hvs : Gen.AC.voteSupports dst.base.blocks B o = true := by
    rw [Gen.AC.voteSupports_def, hoK]
    simp only [Bool.and_eq_true, decide_eq_true_eq, hol, Option.getD_some]
    exact ⟨⟨hKb, hKslot⟩, hBK⟩
  refine ⟨(Gen.AC.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-i vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho iy y).base i,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE iy y i k K _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hnoeq : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = false := by
    cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k with
    | false => rfl
    | true =>
      obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
      exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne
  cases he : GridCO.equivocates (FGSA.headVotes p dst (i + 1)) k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
    have hprov := fgsa_headVotes_provenance E rho hE hN iy y i hiy
    have hone : ∀ w ∈ FGSA.headVotes p dst (i + 1), GridCO.headSeat? w = some k → w = o := by
      intro w hw hwk
      rcases hprov w hw k hwk with hm | heq
      · exact hall w hm hwk
      · change GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = true at heq
        rw [hnoeq] at heq
        contradiction
    exact hne ((hone a ha hka).trans (hone b hb hkb).symm)

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1536–1546, H.2 S1:709–715, H.3:748–783; plan §3.1 steps 3–4
(restates
`healing_next_transfer_core`). DC: INTENTIONAL one capped H.2 HEAD step. If every honest
label-i HEAD covers the pivot and B, every honest HEAD at label i+1 under the cap covers B.
The receiver's own label-i HEAD block is the witness; it has height m, so F and Z are below
it and the floor is at most m at either frame. `hlease` is the lease premise at this read. -/
theorem frontier_next_transfer_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B) :
    Block.Preceq B (headVote p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams i ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hv
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon := hvv.trans hvh
  -- The receiver's own label-i HEAD block is the witness (capped self-witness).
  obtain ⟨jy, hjy⟩ := healing_support_vote_tick E rho hS hDelta hy i hhori
  have hhl : headAtLabel p c E rho y i = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jy y).st (SA.voteTime p.toParams i)) i) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjy]
    rfl
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ timeIdx rho v :=
    fheads_idxBefore_le_timeIdx rho (hvi.trans hv)
  obtain ⟨W, _, hWe, _, hrelay⟩ := frontier_head_relay (hroots := hrec.base.idealization)
    E rho crossing hE hN hDelta
    hrec.sync hQm hcap hy hjy hgsti (hcoverQ y hy _ hhl) ((hvi.trans hv).trans hvh) hcut
  have hWd := hrelay y hy
  have hBW : Block.Preceq B (eraseFG W) := by
    rw [hWe]
    exact hcover y hy _ hhl
  have hQW : Block.Preceq (eraseFG Qfg) (eraseFG W) := by
    rw [hWe]
    exact hcoverQ y hy _ hhl
  have hiyv : iy ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hiy hv).le
  have hWy : W ∈ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hiy hvi) y).1 hWd
  obtain ⟨_, hFW, hZW, hloy⟩ := frontier_self_witness E rho crossing hQm hy
    (hcap iy y hiyv hy) hWy hQW
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.storeControlsView (heightView p) dst.fg =
      KitFG.storeControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  have hWdst : W ∈ dst.fg.TF := by
    rw [hdfg]
    exact hWy
  have hFW' : Block.Preceq (eraseFG dst.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hFW
  by_cases hBF : Block.Preceq B (eraseFG dst.fg.F)
  · exact preceq_headVote_of_preceq_F p dst hinv hBF (Nat.succ_pos i)
  have hFB : Block.Preceq (eraseFG dst.fg.F) B := by
    rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with h | h
    · exact h
    · exact absurd h hBF
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B := hdfg ▸ hFB
  -- The kept path through the frozen v_(i+1) domain.
  have hread : postClock E rho y (SA.voteTime p.toParams (i + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (i + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiy]
    rfl
  have hdpos : 0 < SA.voteTime p.toParams i + p.Δ := by
    change 0 < 4 * p.Δ * (i : Int) + p.Δ + p.Δ
    positivity
  have hdfreeze : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams (i + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hfrozen := healing_frozen_path p c E rho hS hN hdpos hvi hdfreeze hWd hread
  let X := voterBlocks p dst (i + 1)
  have hkeep : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (domainR p dst X) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ :=
      eraseFG_ancestor_preceq hinv.fg.closed hWdst (Gen.Pure.block_preceq_trans hCB hBW)
    have hFA : FGBlock.Preceq dst.fg.F A := fheads_lift
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := fheads_lift
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hfrozen A hAW, hFA, hZA, W, hfrozen W (KitFG.preceq_refl W), hAW, hRd ▸ hloy⟩
  -- The live root is compatible with B.
  have hrows := hlease hFB0
  have hanchor : Block.Compatible (liveRoot p dst) B := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq (hRd ▸ hZW)) hBW
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction
  -- The honest batch of label i.
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head i)) k ∈ rho.honest)
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head i)) k) :=
    hrec.base.cstar (.base (.head i)) trivial
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head i)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := frontier_head_batch_seat E rho hrec crossing hQm
    hvh hcap hgsti hcoverQ hcover hy hiy hv k ((hHmem k).mp hk)
  have hHon : Hon.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective Hon hbij.1]
    congr 1
    ext z
    simp only [Hon, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, hz, rfl⟩
  have hawk : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams i) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun z hz => hrec.awake z hz _ hgsti hhori)
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := by
    have h := (hrec.batch hgsti hhori).lt
    rw [hawk] at h
    exact ⟨hHon ▸ h⟩
  have hother : ((GridCO.seats p.n (FGSA.headVotes p dst (i + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head i)))
    · intro k hk
      obtain ⟨_, hn⟩ := Finset.mem_sdiff.mp hk
      rw [Finset.mem_coe, Gen.V2.Duty.faulty_def]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      exact hn ((hHmem k).mpr hh)
    · intro k _ j _ he
      exact hbij.1 he
  have hcov := batch_head_covers p dst X (FGSA.headVotes p dst (i + 1))
    (FGSA.headSupport p dst (i + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card B
    (fgsa_headSupport_subset_headVotes E rho hE iy y i) rfl
    (fun k hk => (hseat k hk).2) (fun k hk => (hseat k hk).1) hother hb hanchor hkeep
  rw [domainR_eq_storeFrame] at hcov
  rw [headVote_eq, ite_eq_right (Nat.succ_ne_zero i)]
  exact hcov

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1546–1556, H.1:673–699, H.3:748–783; plan §3.1 steps 3–4
(restates
`healing_first_transfer_core`). DC: INTENTIONAL the capped first transfer at v_(s+1). One
honest clean supporter of B at the gate d_s has a label-s HEAD above the pivot. That HEAD
block has height m and is the witness: it reaches the receiver before e_s, and F and Z are
below it at the receiver's frame. The transfer counts are those of H.1. `hlease` is the
lease premise of H.1 (release for a fast body, the window for a slow body). -/
theorem frontier_first_transfer_core (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hgsts : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
      Block.Preceq (eraseFG Qfg) K)
    {ix : Nat} {x : V} (hx : x ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    {B : Block} {k : Fin p.n} {o : GridCO.Wire p.n}
    (hkh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s)
    (hko : GridCO.headSeat? o = some k)
    (hsup : Gen.AC.voteSupports
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))).blocks
      B o = true)
    (hmaj : GridCO.voterCount (GridCO.lateVotes p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) <
      2 * GridCO.goldfishScore
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))).blocks
        (GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s)
        (GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) B)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B)
    (hroots : NamedRootCollisionFree p c E rho) :
    Block.Preceq B (headVote p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1)) := by
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hsync (fgsaDelay_nonrow E.Δ _) hgsts hvd (hgate.trans hvh)
  -- The honest supporter and its HEAD block, the capped witness.
  obtain ⟨K, hK, _, _, _, hom, hol⟩ := healing_support_clean_target E rho o ho
  have hBK : Block.Preceq B K := by
    rw [Gen.AC.voteSupports_def, hK] at hsup
    exact (Bool.and_eq_true_iff.mp hsup).2
  obtain ⟨jz, hjz, hKz⟩ := healing_support_honest_head E rho hE hom hol hko hkh
  rw [hK] at hKz
  have hKeq := Option.some.inj hKz
  have hhlz : headAtLabel p c E rho (rho.seatOf (.base (.head s)) k) s =
      some (headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz
        (rho.seatOf (.base (.head s)) k)).st (SA.voteTime p.toParams s)) s) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
    rfl
  have hvs : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hes : SA.voteTime p.toParams s + p.Δ ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) ≤ timeIdx rho v :=
    fheads_idxBefore_le_timeIdx rho (hes.trans hv)
  have hQK := hcoverQ _ hkh _ hhlz
  obtain ⟨W, _, hWe, _, hrelay⟩ := frontier_head_relay (hroots := hroots) E rho crossing hE hN
    hDelta hsync hQm
    hcap hkh hjz hgsts hQK ((hvs.trans hgate).trans hvh) hcut
  have hKe2 : eraseFG W = K := hWe.trans hKeq.symm
  have hBW : Block.Preceq B (eraseFG W) := by
    rw [hKe2]
    exact hBK
  have hQW : Block.Preceq (eraseFG Qfg) (eraseFG W) := by
    rw [hWe]
    exact hQK
  have hWd := hrelay y hy
  have hiyv : iy ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hiy hv).le
  have hWy : W ∈ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hiy hes) y).1 hWd
  obtain ⟨_, hFWy, hZWy, hloy⟩ := frontier_self_witness E rho crossing hQm hy
    (hcap iy y hiyv hy) hWy hQW
  have hZFy : FGBlock.Preceq (R_at p c E rho iy y).Z W ∧
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F W := ⟨hZWy, hFWy⟩
  -- The receiver HEAD.
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.storeControlsView (heightView p) dst.fg =
      KitFG.storeControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  have hWdst : W ∈ dst.fg.TF := hdfg ▸ hWy
  have hFW' : Block.Preceq (eraseFG dst.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hZFy.2
  by_cases hBF : Block.Preceq B (eraseFG dst.fg.F)
  · exact preceq_headVote_of_preceq_F p dst hinv hBF (Nat.succ_pos s)
  have hFB : Block.Preceq (eraseFG dst.fg.F) B := by
    rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with h | h
    · exact h
    · exact absurd h hBF
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B := hdfg ▸ hFB
  -- The kept path: W and its ancestors are in the frozen v_(s+1) domain.
  have hread : postClock E rho y (SA.voteTime p.toParams (s + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiy]
    rfl
  have hdpos : 0 < SA.voteTime p.toParams s + p.Δ := by
    change 0 < 4 * p.Δ * (s : Int) + p.Δ + p.Δ
    positivity
  have hdfreeze : SA.voteTime p.toParams s + p.Δ ≤ SA.freezeTime p.toParams (s + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    linarith
  have hfrozen := healing_frozen_path p c E rho hS hN hdpos hes hdfreeze hWd hread
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (storeFrame p.E p.cfg dst.fg (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ :=
      eraseFG_ancestor_preceq hinv.fg.closed hWdst (Gen.Pure.block_preceq_trans hCB hBW)
    have hFA : FGBlock.Preceq dst.fg.F A := fheads_lift
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := fheads_lift
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [← domainR_eq_storeFrame, domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hfrozen A hAW, hFA, hZA, W, hfrozen W (KitFG.preceq_refl W), hAW, hRd ▸ hloy⟩
  -- The live root is compatible with B (lease premise of H.1).
  have hrows := hlease hFB0
  have hanchor : Block.Compatible (liveRoot p dst) B := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq (hRd ▸ hZFy.1)) hBW
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction
  -- Majority and rival dominance at the receiver (forward and reverse relay).
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.voteSupports src.blocks B o = true →
      (o ∈ FGSA.headSupport p dst (s + 1) ∧ Gen.AC.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
    intro o' ho' seat hs' hsup'
    obtain ⟨K', hK', hKm', hKst', _, _, _⟩ := healing_support_clean_target E rho o' ho'
    have hBK' : Block.Preceq B K' := by
      rw [Gen.AC.voteSupports_def, hK'] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ := healing_support_target_path (hroots := hroots)
      E rho hE hN hDelta s hSync
      hx hy hiy K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB hBK')
    exact fgsa_cleanSupport_forward_relay E rho hE hN hDelta s hSync hx hy hix hiy o' ho'
      seat hs' Kfg' (hKe' ▸ hK') B (hKe' ▸ hBK') hpath' hFB
  have hc := Gen.AC.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) B
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay E rho hE hN hDelta s hSync hx hy hix hiy)
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.TransferBounds_def] at hc
  exact fgsa_headVote_covers_of_transfer p dst s B hanchor hpath hc.2.2.2.2.2.1 hc.2.2.2.2.2.2

end AvailableChain.FGSA.Run
end
