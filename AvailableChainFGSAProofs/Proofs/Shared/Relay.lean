module
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainGeneric.Proofs.AC.Votes
public import AvailableChainGeneric.Statements.V2.Regimes

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC

private theorem relay_vote_shape {n : Nat} (o : GridCO.Wire n) (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

private theorem relay_clean_mem (p : Params) (v : GridCO.State p.n) (s : Slot)
    (o : GridCO.Wire p.n) (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s) :
    o ∈ v.votes ∧ GridCO.headLabel? o = some s ∧
      GridCO.stampVote v o < SA.earlyTime p.toParams s ∧
      ∀ u ∈ GridCO.lateVotes p.toParams.engine v s,
        GridCO.sameSeat u o = true → u = o := by
  change o ∈ (GridCO.earlyVotes p.toParams.engine v s).filter _ at ho
  obtain ⟨he, hc⟩ := List.mem_filter.mp ho
  obtain ⟨hv, hr⟩ := List.mem_filter.mp he
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hv
  have hstamp : GridCO.stampVote v o < SA.earlyTime p.toParams s := by
    unfold GridCO.resolvedBefore at hr
    cases ht : GridCO.headTarget? o with
    | none => simp only [ht, Bool.false_eq_true] at hr
    | some B =>
      rw [ht] at hr
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).2
  refine ⟨hm, by simpa only [beq_iff_eq] using hl, hstamp, ?_⟩
  intro u hu hs
  have hc' : (GridCO.lateVotes p.toParams.engine v s).any
      (fun u => GridCO.sameSeat u o && u != o) = false := by
    simpa only [Bool.not_eq_true'] using hc
  have hn := List.any_eq_false.mp hc' u hu
  simpa only [hs, Bool.true_and, bne_iff_ne, not_not] using hn

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem relay_idx_mono (rho : V2.Run V (fgsa p c)) : Monotone (V2.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.Run.idxBefore_def, V2.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

private theorem relay_votes_mono (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hN : V2.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    (V2.Run.stateBefore E rho i x).st.base.votes ⊆
      (V2.Run.stateBefore E rho j x).st.base.votes := by
  apply V2.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => (V2.Run.stateBefore E rho i x).st.base.votes ⊆ nd.st.base.votes)
    ?_ ?_ (fun _ _ h => h) E rho hij x (hN.restartFree x i j) (List.Subset.refl _)
  · intro nd t h
    change _ ⊆ (clock p nd.st t).base.votes
    rwa [(clock_vn nd.st t).1]
  · intro nd o h
    exact List.Subset.trans h (process_votes_subset nd.st (toWire p o))

private theorem relay_read_stamp (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (i : Nat) (x : V) (readTime : Time) (o : GridCO.Wire p.n)
    (hm : o ∈ (V2.Run.stateBefore E rho i x).st.base.votes) :
    GridCO.stampVote (actView (clockPre p (V2.Run.stateBefore E rho i x).st
      readTime)) o =
      GridCO.stampVote (V2.Run.stateBefore E rho i x).st.base o := by
  have hk := fgsa_vote_stamp_keys E rho i x
  rw [← hk] at hm
  obtain ⟨⟨v, t⟩, hv, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst v
  change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
  rw [(clockPre_stamps p _ _).2]
  unfold GridCO.stampVote
  cases hf : (V2.Run.stateBefore E rho i x).st.base.voteStamp.find?
      (fun row => row.1 == o) with
  | none =>
    have hn := List.find?_eq_none.mp hf (o, t) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

private theorem relay_gate_late (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hS : V2.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (o : GridCO.Wire p.n) (hm : o ∈ (V2.Run.stateBefore E rho i x).st.base.votes)
    (hl : GridCO.headLabel? o = some s) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s))) s := by
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [beq_iff_eq] using hl⟩
    change o ∈ (clockPre p _ _).base.votes
    rwa [(Internal.clockPre_vn _ _).1]
  · rw [relay_read_stamp E rho i x (SA.gateTime p.toParams s) o hm]
    have hpos : 0 < SA.gateTime p.toParams s := by
      change 0 < 4 * p.Δ * (s : Int) + 6 * p.Δ
      have hd := p.deltaPos
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hi hpos
    have hb := (fgsa_stateBefore_bounds E rho hS i x).2
    unfold GridCO.stampVote
    cases hf : (V2.Run.stateBefore E rho i x).st.base.voteStamp.find?
        (fun row => row.1 == o) with
    | none => exact hn
    | some row => exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

private theorem relay_read_window (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hS : V2.ScheduleWellFormed E rho) (hN : V2.NoRestart rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (d : Time) (hd : d ≤ SA.gateTime p.toParams s) :
    (V2.Run.stateBeforeTime E rho d x).st.slot p ≤ s + 1 := by
  have hm := V2.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (relay_idx_mono rho hd) x
  rw [fgsa_clock_now p c (V2.Run.stateBefore E rho (V2.Run.idxBefore rho d) x),
    fgsa_clock_now p c (V2.Run.stateBefore E rho
      (V2.Run.idxBefore rho (SA.gateTime p.toParams s)) x)] at hm
  rw [Gen.V2.stateBefore_idxBefore E rho d hS,
    Gen.V2.stateBefore_idxBefore E rho _ hS,
    ← fgsa_preTick_eq_timeRead E rho hS hN hi] at hm
  have hb := V2.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
    E rho hS hi x
  rw [fgsa_clock_now p c (V2.Run.stateBefore E rho i x)] at hb
  have hs := Internal.slotOf_mono (p := p) (hm.trans hb)
  have he : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
    exact (fgsa_postClock_slot (c := c) (V2.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  exact hs.trans_eq he

/-- P3 F2.3 (C5/C6), §4.4.3; blueprint 02 §4.2 backward receipt.
Class (ii), FG-SA run receipt instance. DC: Schedule/AdoptionTransport.lean:346
`gfVote_delivery_settled_at_confStore`; Handlers/GoldfishVotePool.lean:791
`block_carried_beforeCutoff_or_equivocates`. Same vote-or-cap conclusion.
INTENTIONAL specialization: U is the other reader's cleanSupport, not the
merged next-vote raw pool of blueprint 02 §4.2. Its early stamp supplies the
relay deadline. The clean pool uses its actual read time; the late pool uses the gate cutoff.
Both stores include clockPre then actView.
This supplies Gen.AC.transfer.hbackward for that U; it does not supply
hforward, block-path coverage, or transport of every source late vote. -/
theorem fgsa_cleanSupport_backward_relay (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hE : V2.ExecutionValid E rho) (hN : V2.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.LabelSync E rho (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    (readTime : Time) {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (_hix : rho.events[ix]? = some (.tick x readTime))
    (hiy : rho.events[iy]? = some (.tick y (SA.gateTime p.toParams s)))
    (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.Run.stateBefore E rho ix x).st readTime)) s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late k = true := by
  dsimp only
  have hc := relay_clean_mem p _ s o ho
  obtain ⟨B, rfl⟩ := relay_vote_shape o s k hc.2.1 hk
  have hmem : (⟨.seat s k, .head B⟩ : GridCO.Wire p.n) ∈
      (V2.Run.stateBefore E rho ix x).st.base.votes := by
    have hm := hc.1
    change _ ∈ (clockPre p _ _).base.votes at hm
    rwa [(Internal.clockPre_vn _ _).1] at hm
  have ht := hc.2.2.1
  rw [relay_read_stamp E rho ix x readTime _ hmem] at ht
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity
  obtain ⟨j, _, t, ha, ht⟩ := fgsa_vote_accepted_before E rho hE.toScheduleWellFormed hN
    ix x s k B _ hpub hz hmem ht
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hd : dl t ≤ SA.gateTime p.toParams s := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) ≤
        4 * p.Δ * (s : Int) + 2 * p.Δ := max_le (le_of_lt ht) (by linarith)
    linarith
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s k B t y hD
    (Or.inr ⟨x, hx, j, ha⟩) hy (hd.trans hcut) (hlt t)
    (relay_read_window E rho hE.toScheduleWellFormed hN hiy (dl t) hd)
  have hkeep : (V2.Run.stateBeforeTime E rho (dl t) y).st.base.votes ⊆
      (V2.Run.stateBefore E rho iy y).st.base.votes := by
    rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hiy,
      ← Gen.V2.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact relay_votes_mono E rho hN y (relay_idx_mono rho hd)
  rcases hr with hr | ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩
  · exact Or.inl (relay_gate_late E rho hE.toScheduleWellFormed hiy _ (hkeep hr.1) rfl)
  · exact Or.inr ((cap_pair _ k).mpr ⟨u,
      relay_gate_late E rho hE.toScheduleWellFormed hiy u (hkeep hu) hlu, v,
      relay_gate_late E rho hE.toScheduleWellFormed hiy v (hkeep hv) hlv, hne, hku, hkv⟩)

end AvailableChain.FGSA.Run
end
