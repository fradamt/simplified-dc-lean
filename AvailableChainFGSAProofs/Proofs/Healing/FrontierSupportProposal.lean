module
public import AvailableChainGeneric.Proofs.AC.RootBatch
public import AvailableChainGeneric.Proofs.AC.RootSupport
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportHeads
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

/-! G-HG1 capped prior support and target scores (plan fgsa-s5-frontier §2.2, §3.1 step 5;
blueprint 21 HG.1:1557–1565, H.6:932–944). These restate the proposer batch seat of
`healing_proposal_batch_seat` (Healing/SupportProposal.lean) and the count of
`repair_prior_support` (Healing/RepairH6.lean) with the capped self-witness: the reader's
own label-r HEAD block has height m and witnesses F, Z and the floor. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem fprop_idxBefore_le_timeIdx (rho : V2.D.Run V (fgsa p c)) {t v : Time}
    (htv : t ≤ v) : V2.D.Run.idxBefore rho t ≤ timeIdx rho v := by
  change (rho.events.filter (fun e => decide (e.time < t))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ v))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).le.trans htv))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S2), 1240–1243 (proposer pools), HG.1:1557–1561; plan
§3.1
step 5 (restates `healing_proposal_batch_seat`). DC: INTENTIONAL under the cap, an honest
label-r HEAD that covers the pivot and B is, at the proposer's slot-(r+1) read, a
resolved non-equivocating proposer-support vote that supports B. The HEAD block is the
relayed witness; F is below it by RXing, so no F ⪯ B premise is needed. -/
theorem frontier_proposal_batch_seat [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {r : Slot} {B : Block} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq B K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v)
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
  -- The HEAD block itself reaches the proposer before e_r (capped relay).
  obtain ⟨Kfg, hKz, hKe0, _, hrelay⟩ := frontier_head_relay (hroots := hrec.base.idealization)
    E rho crossing hE hN hDelta
    hrec.sync hQm hcap hk hjz hgstr (hcoverQ z hk K hhl) ((hvp.trans hv).trans hvh)
    (fprop_idxBefore_le_timeIdx rho (hvp.trans hv))
  have hKe' : eraseFG Kfg = K := hKe0
  have hKx : Kfg ∈ (storeAt p c E rho ip x).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hip hvp) x).1 (hrelay x hx)
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
  -- F is below the height-m HEAD block (RXing under the cap).
  have hipv : ip ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hip hv).le
  have hjzip : jz ≤ ip := by
    have h1 : jz < V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hjz _).mpr (lt_add_of_pos_right _ p.deltaPos)
    exact h1.le.trans (healing_support_idxBefore_le p c E rho hS hip hvp)
  have hFK0 := frontier_F_below E rho crossing hN hx (hcap ip x hipv hx) hk hjzip hKz
    (frontier_height_eq E rho hQm (hcap jz z (hjzip.trans hipv) hk) hKz
      (hKe' ▸ hcoverQ z hk K hhl)).1.ge
  have hFK : Block.Compatible K (eraseFG st.fg.F) := by
    change Block.Compatible K (eraseFG (FGSA.clock p _ _).fg.F)
    rw [clock_fg, ← hKe']
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
      (eraseFG_preceq hFK0)
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
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
    exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1557–1565, H.6:928–944, H.2 S2:709–715; plan §2.2
(RetainedPriorSupport)
and §3.1 step 5. DC: INTENTIONAL a target L that every honest label-r HEAD covers has
retained prior support at the honest proposer read of slot r+1 under the cap: the
proposer's own label-r HEAD block is the height-m witness, and the honest batch of label r
gives the strict majority and the rival bound in the ACTUAL proposer pool. -/
theorem frontier_prior_support [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {r : Slot} {L : Block} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v) :
    RetainedPriorSupport p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (r + 1))) (r + 1) L := by
  classical
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (r + 1))
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams r ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hv
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon := hvv.trans hvh
  have hdfg : src.fg = (storeAt p c E rho ip x).fg := clock_fg p _ _
  have hRd : controls p src = R_at p c E rho ip x := by
    change KitFG.storeControlsView (heightView p) src.fg =
      KitFG.storeControlsView (heightView p) (storeAt p c E rho ip x).fg
    rw [hdfg]
  -- The proposer's own label-r HEAD block is the height-m witness.
  obtain ⟨jx, hjx⟩ := healing_support_vote_tick E rho hS hDelta hx r hhorr
  have hhl : headAtLabel p c E rho x r = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jx x).st (SA.voteTime p.toParams r)) r) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjx]
    rfl
  obtain ⟨W, _, hWe, _, hrelay⟩ := frontier_head_relay (hroots := hrec.base.idealization)
    E rho crossing hE hN hDelta
    hrec.sync hQm hcap hx hjx hgstr (hcoverQ x hx _ hhl) ((hvp.trans hv).trans hvh)
    (fprop_idxBefore_le_timeIdx rho (hvp.trans hv))
  have hW : W ∈ (storeAt p c E rho ip x).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hip hvp) x).1 (hrelay x hx)
  have hLW : Block.Preceq L (eraseFG W) := hWe ▸ hcover x hx _ hhl
  have hQW : Block.Preceq (eraseFG Qfg) (eraseFG W) := hWe ▸ hcoverQ x hx _ hhl
  have hipv : ip ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hip hv).le
  obtain ⟨_, _, hZW, hloW⟩ := frontier_self_witness E rho crossing hQm hx
    (hcap ip x hipv hx) hW hQW
  have hWs : W ∈ src.fg.TF := hdfg ▸ hW
  -- The honest batch of label r in the actual proposer pool.
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head r)) k ∈ rho.honest)
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head r)) k) :=
    hrec.base.cstar (.base (.head r)) trivial
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head r)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := frontier_proposal_batch_seat E rho hrec crossing
    hQm hvh hcap hgstr hcoverQ hcover hx hip hv k ((hHmem k).mp hk)
  have hHon : Hon.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective Hon hbij.1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hHmem k).mp hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, (hHmem k).mpr hz, rfl⟩
  have hawk : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun z hz => hrec.awake z hz _ hgstr hhorr)
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := by
    have h := (hrec.batch hgstr hhorr).lt
    rw [hawk] at h
    exact ⟨hHon ▸ h⟩
  have hother : ((GridCO.seats p.n (proposerVotes src (r + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
    · intro k hk
      obtain ⟨_, hn⟩ := Finset.mem_sdiff.mp hk
      rw [Finset.mem_coe, Gen.V2.Duty.faulty_def]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      exact hn ((hHmem k).mpr hh)
    · intro k _ j _ he
      exact hbij.1 he
  obtain ⟨_, _, hpath, hconflict, _⟩ := Gen.AC.Root.batch_counts src.base.blocks
    (proposerVotes src (r + 1)) (proposerVotes src (r + 1)) (proposerSupport src (r + 1))
    Hon Hon.card (Gen.V2.Duty.faulty rho).card L (fun _ h => h)
    (fun _ ho => (List.mem_filter.mp ho).1) rfl (fun k hk => (hseat k hk).2)
    (fun k hk => (hseat k hk).1) hother hb
  obtain ⟨_, hmajority⟩ := hpath L (Gen.Pure.block_preceq_refl L)
  refine ⟨?_, ⟨W, hWs, hLW, ?_⟩, hmajority, ?_⟩
  · have hZW' : Block.Preceq (z p src) (eraseFG W) := by
      change Block.Preceq (eraseFG (controls p src).Z) (eraseFG W)
      rw [hRd]
      exact eraseFG_preceq hZW
    exact Gen.Pure.block_compatible_of_common hZW' hLW
  · rw [hRd]
    exact hloW
  · intro B hB
    have h1 := hconflict B hB
    have h2 := hb.lt
    obtain ⟨hscore, _⟩ := hpath L (Gen.Pure.block_preceq_refl L)
    change GridCO.goldfishScore src.base.blocks (proposerVotes src (r + 1))
      (proposerSupport src (r + 1)) B < GridCO.goldfishScore src.base.blocks
        (proposerVotes src (r + 1)) (proposerSupport src (r + 1)) L
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1557–1565, H.17:2958–3005; plan §2.2 (target_scores) and §3.1 step 5.
DC: INTENTIONAL a target L that every honest label-r HEAD covers has, at an honest HEAD
read of label r+1 under the cap, a strict majority in the ACTUAL HEAD pool, and every
conflicting block has at most half of the raw voters (the non-strict target rival bound). -/
theorem frontier_target_scores [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {r : Slot} {L : Block} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG Qfg) K)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K)
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (hv : SA.voteTime p.toParams (r + 1) ≤ v) :
    RetainedTargetScores p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (r + 1))) (r + 1) L := by
  classical
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (r + 1))
  have hE := hrec.base.valid
  have hd := p.deltaPos
  have hvi : SA.voteTime p.toParams r ≤ v := by
    refine le_trans ?_ hv
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon := hvi.trans hvh
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head r)) k ∈ rho.honest)
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head r)) k) :=
    hrec.base.cstar (.base (.head r)) trivial
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head r)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := frontier_head_batch_seat E rho hrec crossing hQm
    hvh hcap hgstr hcoverQ hcover hy hih hv k ((hHmem k).mp hk)
  have hHon : Hon.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective Hon hbij.1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hHmem k).mp hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, (hHmem k).mpr hz, rfl⟩
  have hawk : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun z hz => hrec.awake z hz _ hgstr hhorr)
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := by
    have h := (hrec.batch hgstr hhorr).lt
    rw [hawk] at h
    exact ⟨hHon ▸ h⟩
  have hother : ((GridCO.seats p.n (FGSA.headVotes p dst (r + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
    · intro k hk
      obtain ⟨_, hn⟩ := Finset.mem_sdiff.mp hk
      rw [Finset.mem_coe, Gen.V2.Duty.faulty_def]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      exact hn ((hHmem k).mpr hh)
    · intro k _ j _ he
      exact hbij.1 he
  have hsub : FGSA.headSupport p dst (r + 1) ⊆ FGSA.headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
  obtain ⟨_, _, hpath, _, hrest⟩ := Gen.AC.Root.batch_counts dst.base.blocks
    (FGSA.headVotes p dst (r + 1)) (FGSA.headVotes p dst (r + 1))
    (FGSA.headSupport p dst (r + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card L
    (fun _ h => h) hsub rfl (fun k hk => (hseat k hk).2) (fun k hk => (hseat k hk).1) hother hb
  refine ⟨(hpath L (Gen.Pure.block_preceq_refl L)).2, ?_⟩
  intro B hB
  exact hrest B (fun k hk => Gen.AC.Root.vote_pool_support_conflict dst.base.blocks
    (FGSA.headVotes p dst (r + 1)) (FGSA.headSupport p dst (r + 1)) k hsub
    (hseat k hk).2 (hseat k hk).1 hB)

end AvailableChain.FGSA.Run
end
