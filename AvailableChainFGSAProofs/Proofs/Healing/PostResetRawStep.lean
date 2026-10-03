module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseStep
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint

public section

/-! Blueprint 21 H.16:2924–2945, H.1:663–708, H.2:709–746;
plan J5-A-2; B1/B13/B17/B18. DC: SAME raw-result transfer.
First HEADs use the written-domain producer and the raw release proof.
The moving-domain guard uses the exact named J4A2-2 input. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem rawStep_result_tick {y : V} {j : Slot} {C : Block}
    (hC : gateResult p c E rho y j = some (some C)) :
    ∃ k, IsGateTick p c rho k y j := by
  rw [gateResult_def, gateIn_def, preTick_def] at hC
  cases hk : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams j) with
  | none => rw [hk] at hC; cases hC
  | some k => exact ⟨k, V2.D.Run.tickIdx?_spec hk⟩

private theorem rawStep_result_mem (hs : V2.D.ScheduleWellFormed E rho)
    {ix : Nat} {x : V} {s : Slot} {C : Block}
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C)) :
    C ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks := by
  have hconf := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  rw [gateResult_def, (healing_support_gate_reads p c E rho hs hix).1] at hconf
  have hc : SA.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s =
        some C := Option.some.inj hconf
  have hstore := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
    (SA.gateTime p.toParams s)
  have hm := compat_of_confirmation p _ hstore hc
  exact (actView_blocks _ C).mpr ⟨hm.2, hm.1⟩

private theorem rawStep_frozen_geometry [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    let X := (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF
    X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1) ∧
    ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X := by
  intro X
  have hs := hrec.base.valid.toScheduleWellFormed
  have hread : postClock E rho y (SA.voteTime p.toParams (s + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
    rfl
  have hdpos : 0 < SA.freezeTime p.toParams s := by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity
  have hdvote : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  refine ⟨fun W hW => healing_frozen_path p c E rho hs hrec.base.noRestart hdpos hdvote
    (by rw [Nat.add_sub_cancel]) hW hread W (KitFG.preceq_refl W), ?_⟩
  intro W hW A hAW
  obtain ⟨A', hA', heA'⟩ := eraseFG_ancestor_mem
    (cstoreInv_stateBefore E rho _ y).fg.closed hW (eraseFG_preceq hAW)
  exact (eraseFG_injective heA') ▸ hA'

private theorem rawStep_proposals_at_gate_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {C : Block} (hi : IsGateTick p c rho i x s) :
    ∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent := by
  intro v Q hsv hcut hp
  obtain ⟨_, o, ⟨ip, hip, _⟩, _⟩ := hp
  rw [proposalTime_fgsa p c v] at hip
  have hii : i < ip := healing_idx_lt_of_time_lt p c E rho hs hi hip (by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (v : Int)
    have hh : (s : Int) + 2 ≤ v := by exact_mod_cast hsv
    nlinarith [p.deltaPos])
  have hpc : ip < timeIdx rho (SA.proposalTime p.toParams v) :=
    (V2.D.Engine.index_lt_read_length_iff hs _ hip).mpr le_rfl
  exact False.elim (Nat.not_lt_of_ge hcut (Nat.succ_le_of_lt hii |>.trans_lt hpc))

private theorem rawStep_outputs_at_gate_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {C : Block} (hi : IsGateTick p c rho i x s) :
    ∀ a y, a < i + 1 → y ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a y) := by
  intro a y hacut _hy _hhor hsuffix
  have htime : SA.gateTime p.toParams s + 4 * p.Δ = SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  rw [htime] at hsuffix
  delta HealSuffix healStart at hsuffix
  rw [(isGateTime_iff p _).mpr ⟨s + 1, rfl⟩, ite_eq_left rfl] at hsuffix
  have hlt : i < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (by
      change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
      push_cast
      linarith [p.deltaPos])
  have hpre : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (s + 1)) ≤
      afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    rw [V2.D.Run.idxBefore_def]
    exact (preIdx_le_afterTicksIdx E rho hs _).1
  exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ hacut)
    (hlt.trans_le (hpre.trans hsuffix.1)))

variable [Fintype V] {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    (mono : RMono p c E rho) (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec emittedNonempty emittedName writes mono xing origin h0r

/-- Blueprint 21 H.16:2938–2944, H.1:673–700; plan J5-A-2 R1;
B1/B13/B17/B18. DC: SAME first HEAD above the reset block.
No write key, fast threshold or passed-gate premise is required. -/
theorem postReset_raw_first_head_above
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatibleP p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hmem := rawStep_result_mem p c E rho hs hix hres
  have hstore := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x)
    (SA.gateTime p.toParams s)
  obtain ⟨B, -, heB⟩ := hstore.baseTree C |>.mp ((actView_blocks _ C).mp hmem).1
  rw [← heB] at hCB hmem ⊢
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inr hF)
  have hyx : iy < ix := healing_idx_lt_of_time_lt p c E rho hs hiy hix (by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos])
  have hD := postReset_written_domain p c E rho hrec mono emittedNonempty emittedName
    writes xing origin h0r (healing_gate_result_supporter p c E rho) hinv hx hix hres
    hCB hmem (heB ▸ Gen.Pure.block_preceq_refl C) hy hiy (hyx.le.trans hxi) hZ hF
  obtain ⟨hXv, hXc⟩ := rawStep_frozen_geometry p c E rho hrec hiy
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hq : SA.releaseTime p.toParams s = SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 5 * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  have hread : postClock E rho y (SA.releaseTime p.toParams s) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [hq, postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
    rfl
  have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
    rw [PostResetResetLeaseCompatible_def, PostResetResetLeaseCompatibleP_def] at *
    exact hresetNext
  have hrows := postReset_raw_release_compatible p c E rho hrec emittedNonempty emittedName
    writes h0r hinv hreset hleaseNext hx hlabel hix
    ((gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres) hxi hy hread
  have hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 C := by
    intro row hr
    apply hrows row hr
    have hm := (healing_support_release_rows (storeAt p c E rho iy y) s row hr).1
    change row ∈ (GridCO.expire { (storeAt p c E rho iy y).base with
      now := SA.releaseTime p.toParams s } (SA.releaseTime p.toParams s)).obligations at hm
    change (clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.now < row.2.2
    rw [(clock_vn _ _).2, ← hq]
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  rw [heB]
  exact healing_first_transfer_raw_domain p c E rho hrec hgst.le hx hix hres heB hy hiy
    hXv hXc hD hlease

private theorem rawStep_reset_first_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (w.sStar + 1))))
    (hyi : iy ≤ i) : Block.Preceq w.CStar (headAtIdx p c E rho iy (w.sStar + 1)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨_, x0, _, B, ha, -, hsource, heB, -⟩ := h0r.fresh
  obtain ⟨-, C0, -, hG0, hBC, pre, hpre, hτ⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hsource
  rw [← h0r.label] at hG0 hpre hτ
  obtain ⟨ix, hix⟩ := rawStep_result_tick p c E rho hG0
  have hpreEq : pre = clockPre p (storeAt p c E rho ix x0)
      (SA.gateTime p.toParams w.sStar) :=
    Option.some.inj (hpre.symm.trans (healing_support_gate_reads p c E rho hs hix).1)
  subst pre
  have hres := (gateResultAt_eq_gateResult p c E rho hs hix).trans hG0
  have hmem := actView_ancestor_closed p _
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x0) _)
    (rawStep_result_mem p c E rho hs hix hres) hBC
  rw [← heB]
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := w.sStar + 1)
      (Nat.succ_ne_zero w.sStar) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := w.sStar + 1)
      (Nat.succ_ne_zero w.sStar) (Or.inr hF)
  have hD := postReset_written_domain p c E rho hrec mono emittedNonempty emittedName
    writes xing origin h0r (healing_gate_result_supporter p c E rho) hinv ha.1 hix hres
    (heB ▸ Gen.Pure.block_preceq_refl w.CStar) hmem hBC hy hiy hyi hZ hF
  obtain ⟨hXv, hXc⟩ := rawStep_frozen_geometry p c E rho hrec hiy
  exact healing_first_transfer_written p c E rho hrec mono writes ha.1 hix hres hBC
    h0r.synchronous (Or.inl hτ) hy hiy hXv hXc hD

/-- Blueprint 21 H.16:2930–2944, H.1:663–708; plan J5-A-2 R1;
B1/B13/B17/B18. DC: SAME first HEAD for every raw result.
P1 excludes conflicts with CStar. Below CStar, use the reset's first
HEAD or its prior raw-transfer clause. Above it, use the frozen domain. -/
theorem postReset_raw_first_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatibleP p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq C (headAtIdx p c E rho iy (s + 1)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hcompat := postReset_raw_reset_compatible p c E rho hrec emittedNonempty emittedName
    h0r hinv hx hlabel hix hres hxi
  rcases Bool.or_eq_true_iff.mp hcompat with hbelow | habove
  · exact postReset_raw_first_head_above p c E rho hrec emittedNonempty emittedName writes
      mono xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hbelow hy hiy
  · apply Gen.Pure.block_preceq_trans habove
    have hyx : iy < ix := healing_idx_lt_of_time_lt p c E rho hs hiy hix (by
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      linarith [p.deltaPos])
    rcases eq_or_lt_of_le hlabel with he | hlt
    · subst s
      exact rawStep_reset_first_head p c E rho hrec emittedNonempty emittedName writes mono
        xing origin h0r hinv hy hiy (hyx.le.trans hxi)
    · obtain ⟨_, x0, _, B0, ha, -, hsource, heB, -⟩ := h0r.fresh
      obtain ⟨-, C0, -, hG0, hBC, -⟩ :=
        healing_source_decode p c E rho emittedNonempty emittedName ha hsource
      rw [← h0r.label] at hG0
      obtain ⟨k0, hk0⟩ := rawStep_result_tick p c E rho hG0
      have hk0i : k0 < i := (healing_idx_lt_of_time_lt p c E rho hs hk0 hix (by
        change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
        have hh : (w.sStar : Int) < s := by exact_mod_cast hlt
        nlinarith [p.deltaPos])).trans_le hxi
      have hread : headAtLabel p c E rho y (s + 1) =
          some (headAtIdx p c E rho iy (s + 1)) := by
        rw [healing_headAtIdx_tick p c E rho hiy]
        delta headAtLabel
        rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
        rfl
      have hcut : timeIdx rho (SA.voteTime p.toParams (s + 1)) ≤ i := by
        by_contra hn
        have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hix).mp
          (hxi.trans_lt (Nat.lt_of_not_ge hn))
        change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
        push_cast at ht
        linarith [p.deltaPos]
      have hraw := hinv.raw_transfer
      rw [PostResetRawTransfer_def] at hraw
      exact Gen.Pure.block_preceq_trans (heB ▸ hBC)
        ((hraw k0 hk0i x0 w.sStar C0 ha.1 le_rfl hk0 hG0).2.1 y (s + 1) _ hy
          (Nat.succ_le_succ hlabel) hcut hread)


/-- Blueprint 21 H.16:2938–2944, H.1:663–708; plan J5-A-2 R1 label;
B1/B13/B17/B18. DC: SAME first HEAD through its complete label read. -/
theorem postReset_raw_first_head_label
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatibleP p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    {y : V} {H : Block} (hy : y ∈ rho.honest)
    (hhead : headAtLabel p c E rho y (s + 1) = some H) : Block.Preceq C H := by
  delta headAtLabel at hhead
  rw [postClock_def, preTick_def] at hhead
  cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [ht] at hhead; cases hhead
  | some iy =>
    have hiy := V2.D.Run.tickIdx?_spec ht
    have heH : headAtIdx p c E rho iy (s + 1) = H := by
      rw [healing_headAtIdx_tick p c E rho hiy]
      rw [ht] at hhead
      exact Option.some.inj hhead
    rw [← heH]
    exact postReset_raw_first_head p c E rho hrec emittedNonempty emittedName writes mono
      xing origin h0r hinv hresetNext hleaseNext hx hlabel hix hxi hres hy hiy

/-- Blueprint 21 H.16:2940–2944; plan J5-A-2 R3 new-source HEAD;
B1/B13/B17/B18. DC: SAME HEAD clause at the source event's successor cut.
Only the first label can have an actual complete HEAD cut at i+1. -/
theorem postReset_raw_heads_at_gate_cut
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatibleP p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hi : IsGateTick p c rho i x s)
    (hres : gateResultAt p c E rho i = some (some C)) :
    ∀ y l H, y ∈ rho.honest → s + 1 ≤ l →
      timeIdx rho (SA.voteTime p.toParams l) ≤ i + 1 →
      headAtLabel p c E rho y l = some H → Block.Preceq C H := by
  intro y l H hy hsl hcut hhead
  rcases eq_or_lt_of_le hsl with rfl | hlt
  · exact postReset_raw_first_head_label p c E rho hrec emittedNonempty emittedName writes
      mono xing origin h0r hinv hresetNext hleaseNext hx hlabel hi le_rfl hres hy hhead
  · delta headAtLabel at hhead
    rw [postClock_def, preTick_def] at hhead
    cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams l) with
    | none => rw [ht] at hhead; cases hhead
    | some iy =>
      have hiy := V2.D.Run.tickIdx?_spec ht
      have hyi : iy < timeIdx rho (SA.voteTime p.toParams l) :=
        (V2.D.Engine.index_lt_read_length_iff hrec.base.valid.toScheduleWellFormed _ hiy).mpr
          le_rfl
      have hii : i < iy := healing_idx_lt_of_time_lt p c E rho
        hrec.base.valid.toScheduleWellFormed hi hiy (by
          change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (l : Int) + p.Δ
          have hh : (s : Int) + 2 ≤ l := by exact_mod_cast (show s + 2 ≤ l from hlt)
          nlinarith [p.deltaPos])
      exact False.elim (Nat.not_lt_of_ge hcut (Nat.succ_le_of_lt hii |>.trans_lt hyi))

/-- Blueprint 21 H.16:2924–2945; plan J5-A-2 R3 new-source package;
B1/B13/B17/B18. DC: SAME all four raw clauses for the source at event i.
Later proposals and output suffixes cannot be readers at this cut.
This does not extend old raw results across their boundary readers. -/
theorem postReset_raw_at_gate_cut
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hresetNext : PostResetResetLeaseCompatibleP p c E rho w (i + 1))
    (hleaseNext : PostResetLeaseSafe p c E rho w (i + 1))
    {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hlabel : w.sStar ≤ s) (hi : IsGateTick p c rho i x s)
    (hres : gateResult p c E rho x s = some (some C)) :
    (∀ y nd, y ∈ rho.honest → timeIdx rho (SA.releaseTime p.toParams s) ≤ i + 1 →
      postClock E rho y (SA.releaseTime p.toParams s) = some nd →
      ∀ row ∈ nd.st.base.obligations, nd.st.base.now < row.2.2 → Block.Compatible row.1 C) ∧
    (∀ y l H, y ∈ rho.honest → s + 1 ≤ l →
      timeIdx rho (SA.voteTime p.toParams l) ≤ i + 1 →
      headAtLabel p c E rho y l = some H → Block.Preceq C H) ∧
    (∀ v Q, s + 2 ≤ v → timeIdx rho (SA.proposalTime p.toParams v) ≤ i + 1 →
      HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent) ∧
    (∀ a y, a < i + 1 → y ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      HealSuffix p c rho (SA.gateTime p.toParams s + 4 * p.Δ) a →
      Block.Preceq C (S_at p c E rho a y)) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  refine ⟨?_, ?_, rawStep_proposals_at_gate_cut p c E rho hs hi,
    rawStep_outputs_at_gate_cut p c E rho hs hi⟩
  · intro y nd hy _hcut hnd
    have hreset : PostResetResetLeaseCompatible p c E rho w (i + 1) := by
      rw [PostResetResetLeaseCompatible_def, PostResetResetLeaseCompatibleP_def] at *
      exact hresetNext
    exact postReset_raw_release_compatible p c E rho hrec emittedNonempty emittedName writes
      h0r hinv hreset hleaseNext hx hlabel hi hres le_rfl hy hnd
  · exact postReset_raw_heads_at_gate_cut p c E rho hrec emittedNonempty emittedName writes
      mono xing origin h0r hinv hresetNext hleaseNext hx hlabel hi
      ((gateResultAt_eq_gateResult p c E rho hs hi).trans hres)

variable
    (movingDomain : ∀ {i : Nat}, PostResetInv p c E rho w i →
      ∀ {l : Slot} {B : FGBlock (Fin p.n)}, E.t_GST ≤ SA.voteTime p.toParams l →
      Block.Preceq w.CStar (eraseFG B) →
      (∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
        Block.Preceq (eraseFG B) H) →
      ∀ {iy : Nat} {y : V} {t : Time}, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → iy ≤ i →
      SA.freezeTime p.toParams l < t → t ≤ SA.voteTime p.toParams (l + 1) →
      ∀ {X : Finset (FGBlock (Fin p.n))}, X ⊆ (storeAt p c E rho iy y).fg.TF →
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams l)) y).fg.TF ⊆ X →
      ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z →
      ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F → B ∈ D_at p c E rho iy y X)

include movingDomain

omit emittedNonempty emittedName writes mono xing origin h0r in
/-- Blueprint 21 H.2:723–726,736–746; plan J5-A-2 R2 domain;
B1/B13/B17/B18. DC: SAME moving reader's frozen-domain guard.
This specializes J4A2-2 G2. The live-lease guard is a separate open item. -/
theorem postReset_raw_moving_domain
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {l : Slot} {B : FGBlock (Fin p.n)} (hgst : E.t_GST ≤ SA.voteTime p.toParams l)
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams l)) y).fg.TF := by
  have hcut := healing_support_idxBefore_le p c E rho hrec.base.valid.toScheduleWellFormed
    hiy hafter.le
  have hX := (fgsa_store_cumulative p c E rho hrec.base.noRestart hcut y).1
  exact movingDomain hinv hgst hCB hbatch hy hiy hyi hafter hupper hX (Finset.Subset.refl _)
    hnZ hnF

omit writes mono origin movingDomain in
/-- Blueprint 21 H.16:2933–2938; plan J5-A-2 reset-lease adapter;
B1/B13/B17/B18. DC: INTENTIONAL; DC has no leases.
The existing C2 producer closes the joint step itself for every i. -/
theorem postReset_resetLease_succ_all (cap : RCap p c E rho) (source : TSrc p c E rho) :
    ∀ i, PostResetResetLeaseStep p c E rho w i := by
  intro i
  rw [PostResetResetLeaseStep_def]
  intro hprev
  have hreset : PostResetResetLeaseCompatible p c E rho w i := by
    rw [PostResetResetLeaseCompatible_def, PostResetResetLeaseCompatibleP_def] at *
    exact hprev.2.1
  rw [PostResetResetLeaseCompatibleP_def]
  have hn := postReset_resetLease_succ p c E rho hrec emittedNonempty emittedName xing cap
    source h0r hprev.1 hreset
  rwa [PostResetResetLeaseCompatible_def] at hn

end AvailableChain.FGSA.Run
