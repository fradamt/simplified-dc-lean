module
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainFGSAClaims.Statements.Reads

public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

private theorem sl_vote_shape {n : Nat} (o : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

private theorem sl_clean_mem (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (o : GridCO.Wire p.n .root) (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s) :
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
    cases ht : GridCO.resolvedHead? v o with
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

private theorem sl_clean_late (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    GridCO.cleanSupport p.toParams.engine v s ⊆ GridCO.lateVotes p.toParams.engine v s := by
  intro o ho
  have h := sl_clean_mem p v s o ho
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨h.1, by simpa only [beq_iff_eq] using h.2.1⟩, ?_⟩
  apply decide_eq_true
  have hd := p.deltaPos
  change GridCO.stampVote v o < 4 * p.Δ * (s : Int) + 6 * p.Δ
  have ht := h.2.2.1
  change GridCO.stampVote v o < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
  linarith

private theorem sl_same_seat {n : Nat} (u v : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hu : GridCO.headLabel? u = some s) (hv : GridCO.headLabel? v = some s)
    (hku : GridCO.headSeat? u = some k) (hkv : GridCO.headSeat? v = some k) :
    GridCO.sameSeat u v = true := by
  obtain ⟨B, rfl⟩ := sl_vote_shape u s k hu hku
  obtain ⟨C, rfl⟩ := sl_vote_shape v s k hv hkv
  change (s == s && k == k) = true
  simp only [BEq.rfl, Bool.and_self]

private theorem sl_clean_no_equiv (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (o : GridCO.Wire p.n .root) (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) k = false := by
  cases he : GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) k with
  | false => rfl
  | true =>
    obtain ⟨u, hu, w, hw, hn, hku, hkw⟩ := (cap_pair _ k).mp he
    have h := sl_clean_mem p v s o ho
    have hl (a : GridCO.Wire p.n .root) (ha : a ∈ GridCO.lateVotes p.toParams.engine v s) :
        GridCO.headLabel? a = some s := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp (List.mem_filter.mp ha).1).2
    have eu := h.2.2.2 u hu (sl_same_seat u o s k (hl u hu) h.2.1 hku hk)
    have ew := h.2.2.2 w hw (sl_same_seat w o s k (hl w hw) h.2.1 hkw hk)
    exact (hn (eu.trans ew.symm)).elim

private theorem sl_clean_pool (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    ∀ k, GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) k = false := by
  intro k
  cases he : GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) k with
  | false => rfl
  | true =>
    obtain ⟨u, hu, _, _, _, hk, _⟩ := (cap_pair _ k).mp he
    have hf := sl_clean_no_equiv p v s u hu k hk
    have ht := vote_pool_equivocates_mono _ _ k (sl_clean_late p v s) he
    rw [hf] at ht
    contradiction

private def sl_support (p : Params) (v : GridCO.State p.n .root) (s : Slot) (B : Block) :
    Finset (Fin p.n) :=
  (GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset.filter
    (fun k => poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) k B = true)

private theorem sl_support_mem (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (B : Block) (k : Fin p.n) : k ∈ sl_support p v s B ↔
      ∃ o ∈ GridCO.cleanSupport p.toParams.engine v s,
        GridCO.headSeat? o = some k ∧ voteSupports v.blocks B o = true := by
  change k ∈ ((GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset.filter
    (fun j => poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) j B = true)) ↔ _
  rw [Finset.mem_filter, vote_pool_support_witness]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(vote_pool_mem_seats _ k).mpr (by obtain ⟨o, ho, hk, _⟩ := h; exact ⟨o, ho, hk⟩), h⟩

private theorem sl_score (p : Params) (v : GridCO.State p.n .root) (s : Slot) (B : Block)
    (hscore : SA.Root.prefixSupport p.toParams v s B =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) B) :
    SA.Root.prefixSupport p.toParams v s B = (sl_support p v s B).card := by
  rw [hscore]
  rw [vote_pool_score_card]
  simp only [sl_clean_pool p v s, Bool.false_or]
  rfl

private theorem sl_result_majority (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (a B : Block) (h : SA.Root.confirmationFrom p.toParams a v s = some B)
    (hscore : ∀ C, SA.Root.prefixSupport p.toParams v s C =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) C) :
    (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset.card <
      2 * (sl_support p v s B).card := by
  have hex : ∃ C, GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s C ∧ some C = some B := by
    change (if _ then some _ else none) = some B at h
    split at h
    · exact ⟨_, ‹_›, h⟩
    · contradiction
  obtain ⟨C, hc, he⟩ := hex
  have := Option.some.inj he
  subst C
  rwa [sl_score p v s B (hscore B), vote_pool_voterCount_card] at hc

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem sl_idx_mono (rho : V2.D.Run V (fgsa p c)) : Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

private theorem sl_votes_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho j x).st.base.votes := by
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => (V2.D.Run.stateBefore E rho i x).st.base.votes ⊆ nd.st.base.votes)
    ?_ ?_ (fun _ _ h => h) E rho hij x (hN.restartFree x i j) (List.Subset.refl _)
  · intro nd t h
    change _ ⊆ (clock p nd.st t).base.votes
    rwa [(clock_vn nd.st t).1]
  · intro nd o h
    exact List.Subset.trans h (process_votes_subset nd.st (toWire p o))

private theorem sl_gate_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes) :
    GridCO.stampVote (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
      (SA.gateTime p.toParams s))) o =
      GridCO.stampVote (V2.D.Run.stateBefore E rho i x).st.base o := by
  have hk := fgsa_vote_stamp_keys E rho i x
  rw [← hk] at hm
  obtain ⟨⟨v, t⟩, hv, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst v
  change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
  rw [(clockPre_stamps p _ _).2]
  unfold GridCO.stampVote
  cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
      (fun row => row.1 == o) with
  | none =>
    have hn := List.find?_eq_none.mp hf (o, t) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

private theorem sl_gate_late (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hEpoch : ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w < SA.gateTime p.toParams s)
    (o : GridCO.Wire p.n .root) (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hl : GridCO.headLabel? o = some s) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s))) s := by
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [beq_iff_eq] using hl⟩
    change o ∈ (clockPre p _ _).base.votes
    rwa [(Internal.clockPre_vn _ _).1]
  · rw [sl_gate_stamp E rho i x s o hm]
    have hpos : 0 < SA.gateTime p.toParams s := by
      change 0 < 4 * p.Δ * (s : Int) + 6 * p.Δ
      have hd := p.deltaPos
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hi hpos hEpoch
    have hb := (fgsa_stateBefore_bounds E rho hS i x).2
    unfold GridCO.stampVote
    cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
        (fun row => row.1 == o) with
    | none => exact hn
    | some row => exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

private theorem sl_read_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (d : Time) (hd : d ≤ SA.gateTime p.toParams s) :
    (V2.D.Run.stateBeforeTime E rho d x).st.slot p ≤ s + 1 := by
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (sl_idx_mono rho hd) x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) x),
    fgsa_clock_now p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)) x)] at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hS,
    Gen.V2.Duty.stateBefore_idxBefore E rho _ hS,
    ← fgsa_preTick_eq_timeRead E rho hS hN hi] at hm
  have hb := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
    E rho hS hi x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x)] at hb
  have hs := Internal.slotOf_mono (p := p) (hm.trans hb)
  have he : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
    exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  exact hs.trans_eq he

private theorem sl_relay (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.gateTime p.toParams s)))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late k = true := by
  dsimp only
  have hc := sl_clean_mem p _ s o ho
  obtain ⟨B, rfl⟩ := sl_vote_shape o s k hc.2.1 hk
  have hmem : (⟨.seat s k, .head B⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho ix x).st.base.votes := by
    have hm := hc.1
    change _ ∈ (clockPre p _ _).base.votes at hm
    rwa [(Internal.clockPre_vn _ _).1] at hm
  have ht := hc.2.2.1
  rw [sl_gate_stamp E rho ix x s _ hmem] at ht
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
  obtain ⟨j, _, t, ha, ht⟩ := fgsa_vote_accepted_before E rho hE hN
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
  have hT : Gen.V2.Duty.Trigger E rho
      (ofHead p ⟨.seat (.head s) k, B⟩) t :=
    Or.inr ⟨x, hx, j, ha⟩
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s k B t y hD
    hT hy (hd.trans hcut) (hlt t)
    (sl_read_window E rho hE.toScheduleWellFormed hN hiy (dl t) hd)
    (hd.trans (hE.in_horizon _ (List.mem_of_getElem? hiy)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hiy hy
      (fgsa_trigger_nonneg E rho hE.toScheduleWellFormed hT) hd)
  have hkeep : (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho iy y).st.base.votes := by
    rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hiy,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact sl_votes_mono E rho hN y (sl_idx_mono rho hd)
  rcases hr with hr | ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩
  · exact Or.inl (sl_gate_late E rho hE.toScheduleWellFormed hiy
        (fun j w _ he => False.elim (hN j _ w he)) _ (hkeep hr.1) rfl)
  · exact Or.inr ((cap_pair _ k).mpr ⟨u,
      sl_gate_late E rho hE.toScheduleWellFormed hiy
        (fun j w _ he => False.elim (hN j _ w he)) u (hkeep hu) hlu, v,
      sl_gate_late E rho hE.toScheduleWellFormed hiy
        (fun j w _ he => False.elim (hN j _ w he)) v (hkeep hv) hlv, hne, hku, hkv⟩)

private theorem sl_gate_input (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) (B : Block) (h : gateResult p c E rho x s = some (some B)) :
    ∃ i, rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p (V2.D.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s)).fg.F)
        (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
          (SA.gateTime p.toParams s))) s = some B := by
  rw [gateResult_def, gateIn_def, preTick_def] at h
  cases hi : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => simp only [hi, Option.map_none] at h; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at h
    exact ⟨i, V2.D.Run.tickIdx?_spec hi, h⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.2, blueprint 02 §2.2 and 21 IF.6: two honest raw gate results
at one synchronized label are compatible. Class (ii), T7.8 receipt instance
and Gen A2/A3 count assembly. DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405
`eligible_compatible`. INTENTIONAL: use the optional F-anchored active-view
result (spec/fgsa-protocol.tex:2496–2513), with label-local synchronization.
No participation or honest-majority premise is needed for compatibility.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_sameLabel (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ x y B C, x ∈ rho.honest → y ∈ rho.honest →
      gateResult p c E rho x s = some (some B) →
      gateResult p c E rho y s = some (some C) → Block.Compatible B C := by
  intro x y B C hx hy hB hC
  obtain ⟨ix, hix, hB⟩ := sl_gate_input E rho x s B hB
  obtain ⟨iy, hiy, hC⟩ := sl_gate_input E rho y s C hC
  let vx := actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))
  let vy := actView (clockPre p (V2.D.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))
  let Lx := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine vx s)).toFinset
  let Ly := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine vy s)).toFinset
  have own (v : GridCO.State p.n .root) (D : Block) : sl_support p v s D ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset := by
    intro k hk
    obtain ⟨o, ho, hko, _⟩ := (sl_support_mem p v s D k).mp hk
    exact (vote_pool_mem_seats _ k).mpr ⟨o, sl_clean_late p v s ho, hko⟩
  have cross {ia ib : Nat} {a b : V} (ha : a ∈ rho.honest) (hb : b ∈ rho.honest)
      (hib : rho.events[ib]? = some (.tick b (SA.gateTime p.toParams s))) (D : Block) :
      sl_support p (actView (clockPre p (V2.D.Run.stateBefore E rho ia a).st
        (SA.gateTime p.toParams s))) s D ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
        (actView (clockPre p (V2.D.Run.stateBefore E rho ib b).st
          (SA.gateTime p.toParams s))) s)).toFinset := by
    intro k hk
    obtain ⟨o, ho, hko, _⟩ := (sl_support_mem p _ s D k).mp hk
    rcases sl_relay E rho hE hN hDelta s hSync ha hb hib o ho k hko with hm | he
    · exact (vote_pool_mem_seats _ k).mpr ⟨o, hm, hko⟩
    · exact vote_pool_equivocates_participant _ k he
  have hLx : sl_support p vx s B ∪ sl_support p vy s C ⊆ Lx :=
    Finset.union_subset (own vx B) (cross hy hx hix C)
  have hLy : sl_support p vx s B ∪ sl_support p vy s C ⊆ Ly :=
    Finset.union_subset (cross hx hy hiy B) (own vy C)
  have score (i : Nat) (z : V) (D : Block) :
      let pre := clockPre p (rho.stateBefore E i z).st (SA.gateTime p.toParams s)
      let v := actView pre
      SA.Root.prefixSupport p.toParams v s D =
        GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
          (GridCO.cleanSupport p.toParams.engine v s) D := by
    intro pre v
    exact actView_score p pre (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i z) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i z))
      _ _ D
  obtain ⟨k, hk⟩ := Gen.Pure.two_majorities_intersect hLx hLy
    (sl_result_majority p _ s _ B hB (score ix x))
    (sl_result_majority p _ s _ C hC (score iy y))
  obtain ⟨hkB, hkC⟩ := Finset.mem_inter.mp hk
  obtain ⟨u, hu, hku, hBu⟩ := (sl_support_mem p vx s B k).mp hkB
  obtain ⟨v, hv, hkv, hCv⟩ := (sl_support_mem p vy s C k).mp hkC
  have hn := sl_clean_no_equiv p vx s u hu k hku
  have hrelay := sl_relay E rho hE hN hDelta s hSync hy hx hix v hv k hkv
  have hvx : v ∈ GridCO.lateVotes p.toParams.engine vx s := by
    rcases hrelay with h | h
    · exact h
    · rw [hn] at h
      contradiction
  have hu' := sl_clean_mem p vx s u hu
  have hv' := sl_clean_mem p vy s v hv
  have he : v = u := hu'.2.2.2 v hvx
    (sl_same_seat v u s k hv'.2.1 hu'.2.1 hkv hku)
  subst v
  obtain ⟨K, hK, hmK, _, hBK⟩ := (vote_support_body _ _ _).mp hBu
  obtain ⟨L, hL, hmL, _, hCL⟩ := (vote_support_body _ _ _).mp hCv
  have hxK : K ∈ (rho.stateBefore E ix x).st.base.blocks := by
    have hm := (List.mem_filter.mp hmK).1
    change K ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hyL : L ∈ (rho.stateBefore E iy y).st.base.blocks := by
    have hm := (List.mem_filter.mp hmL).1
    change L ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hKL := stored_block_eq_of_root_eq E rho hroots ix iy x y hxK hyL
    (Option.some.inj ((resolvedTarget_root _ u hK).symm.trans (resolvedTarget_root _ u hL)))
  exact Gen.Pure.block_compatible_of_common hBK (hKL.symm ▸ hCL)

end AvailableChain.FGSA.Run
end
