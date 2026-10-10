module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetConeReceipts

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME counts in the actual pools from phase-free receipt producers. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem cone_pool_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME proposer majority and rivals from the preceding honest batch.
C1/C2 supply target coverage, the root helper supplies root coverage,
and C3 supplies the common pivot and its floor. -/
theorem postReset_priorSupport_at_cut [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    (mono : RMono p c E rho)
    {v : Time} (hvh : v ≤ rho.horizon)
    {r : Slot} {L : Block} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hcut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hv : SA.proposalTime p.toParams (r + 1) ≤ v)
    (hZHeads : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG (R_at p c E rho ip x).Z) K)
    (D : FGBlock (Fin p.n))
    (hDHeads : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG D) K)
    (hfloor : (controls p (clock p (storeAt p c E rho ip x)
      (SA.proposalTime p.toParams (r + 1)))).lo ≤ (heightView p D).h) :
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
  have hFHeads : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) K := by
    intro z hz K hK
    exact block_preceq_trans (eraseFG_preceq
      (repair_F_preceq_Z _ (cstoreInv_stateBefore E rho ip x))) (hZHeads z hz K hK)
  obtain ⟨jx, hjx⟩ := healing_support_vote_tick E rho hS hDelta hx r hhorr
    (hrec.awake x hx _ hgstr hhorr)
  have hhl : headAtLabel p c E rho x r = some (headVote p (clock p
      (storeAt p c E rho jx x) (SA.voteTime p.toParams r)) r) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjx]
    rfl
  obtain ⟨W, _, hWe, hrelay⟩ := postReset_head_receipt_at_cut E rho hrec mono crossing hx hjx hx hip
    hgstr hvp (hFHeads x hx _ hhl)
  have hW : W ∈ (storeAt p c E rho ip x).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hip hvp) x).1 hrelay
  have hLW : Block.Preceq L (eraseFG W) := hWe ▸ hcover x hx _ hhl
  have hZW : Block.Preceq (z p src) (eraseFG W) := by
    change Block.Preceq (eraseFG (controls p src).Z) (eraseFG W)
    have hcontrols : controls p src = R_at p c E rho ip x := by
      change KitFG.treeStoreControlsView (heightView p) src.fg =
        KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho ip x).fg
      rw [hdfg]
    rw [hcontrols]
    exact hWe ▸ hZHeads x hx _ hhl
  have hloW : (controls p src).lo ≤ (heightView p W).h :=
    hfloor.trans ((fgCertificateLaws p).height.h_mono
      (cone_pool_lift (hWe ▸ hDHeads x hx _ hhl)))
  have hWs : W ∈ src.fg.TF := hdfg ▸ hW
  -- The honest batch of label r in the actual proposer pool.
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head r)) k ∈ rho.honest)
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head r)) k) :=
    hrec.base.cstar (.base (.head r)) trivial
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head r)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hseat (k : Fin p.n) (hk : k ∈ Hon) :=
    postReset_proposal_batch_seat_at_cut E rho hrec crossing mono
    hvh hgstr hcut hcover hx hip hv hFHeads k ((hHmem k).mp hk)
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
  · exact Gen.Pure.block_compatible_of_common hZW hLW
  · exact hloW
  · intro B hB
    have h1 := hconflict B hB
    have h2 := hb.lt
    obtain ⟨hscore, _⟩ := hpath L (Gen.Pure.block_preceq_refl L)
    change GridCO.goldfishScore src.base.blocks (proposerVotes src (r + 1))
      (proposerSupport src (r + 1)) B < GridCO.goldfishScore src.base.blocks
        (proposerVotes src (r + 1)) (proposerSupport src (r + 1)) L
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C4.
DC: SAME HEAD majority and rival bound from the preceding honest batch.
The strict target arm has F below the live root and then below L. -/
theorem postReset_targetScores_at_cut [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    (mono : RMono p c E rho)
    {v : Time} (hvh : v ≤ rho.horizon)
    {r : Slot} {L : Block} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hcut : E.t_GST ≤ slotStartZ p ((r : Int) - 1))
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K)
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (hv : SA.voteTime p.toParams (r + 1) ≤ v)
    (hFL : Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) L) :
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
  have hseat (k : Fin p.n) (hk : k ∈ Hon) :=
    postReset_head_batch_seat_at_cut E rho hrec crossing mono
    hvh hgstr hcut hcover hy hih hv (fun z hz K hK =>
      block_preceq_trans hFL (hcover z hz K hK)) k ((hHmem k).mp hk)
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
