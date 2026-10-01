module
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainGeneric.Proofs.AC.Votes
public import AvailableChainGeneric.Statements.V2.Duty.Regimes

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

/-- P3 §4.4.3 C5/C6; bp02 §4.2, G24 item 3. Class (iii), pool instance.
DC b241081: Goldfish/Confirmation.lean:95 Numerator (`filtered`). SAME:
the early pool excludes each seat with a second vote in the late pool;
the proof uses the late filter, not reverse equivocation monotonicity. -/
theorem fgsa_cleanSupport_seat_clean_late (p : Params) (v : GridCO.State p.n)
    (s : Slot) (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) k = false := by
  have hc := relay_clean_mem p v s o ho
  obtain ⟨B, rfl⟩ := relay_vote_shape o s k hc.2.1 hk
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨u, hu, w, hw, hn, hku, hkw⟩ := (cap_pair _ k).mp he
  have same (a : GridCO.Wire p.n) (ha : a ∈ GridCO.lateVotes p.toParams.engine v s)
      (hka : GridCO.headSeat? a = some k) :
      GridCO.sameSeat a ⟨.seat s k, .head B⟩ = true := by
    have hl : GridCO.headLabel? a = some s := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp (List.mem_filter.mp ha).1).2
    obtain ⟨C, rfl⟩ := relay_vote_shape a s k hl hka
    change (s == s && k == k) = true
    simp only [beq_self_eq_true, Bool.and_self]
  exact hn ((hc.2.2.2 u hu (same u hu hku)).trans
    (hc.2.2.2 w hw (same w hw hkw)).symm)

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem relay_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

private theorem relay_votes_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
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

private theorem relay_read_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (readTime : Time) (o : GridCO.Wire p.n)
    (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes) :
    GridCO.stampVote (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
      readTime)) o =
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

private theorem relay_gate_late (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (o : GridCO.Wire p.n) (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hl : GridCO.headLabel? o = some s) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s))) s := by
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
    cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
        (fun row => row.1 == o) with
    | none => exact hn
    | some row => exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

private theorem relay_read_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (d : Time) (hd : d ≤ SA.gateTime p.toParams s) :
    (V2.D.Run.stateBeforeTime E rho d x).st.slot p ≤ s + 1 := by
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (relay_idx_mono rho hd) x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) x),
    fgsa_clock_now p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)) x)] at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hS,
    Gen.V2.Duty.stateBefore_idxBefore E rho _ hS,
    ← fgsa_preTick_eq_timeRead E rho hS hN hi] at hm
  have hb := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
    E rho hS hi x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x)] at hb
  have hs := Internal.slotOf_mono (p := p) (hm.trans hb)
  have he : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
    exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  exact hs.trans_eq he

private theorem relay_proposals_process (st : State p.n) (o : Obj p)
    (h : ∀ w ∈ st.proposals, FGSA.wellFormed p w = true)
    (hw : FGSA.wellFormed p (toWire p o) = true) :
    ∀ w ∈ (FGSA.process p st (toWire p o)).proposals, FGSA.wellFormed p w = true := by
  change ∀ w ∈ (match (toWire p o).decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨(toWire p o).auth, body⟩
    | some (.block s b raw sup rows) => admitBlock p st s b raw sup rows
    | none => st).proposals, _
  cases hd : (toWire p o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b => exact h
    | row i body =>
      dsimp only
      rcases admitRow_eq p st ⟨(toWire p o).auth, body⟩ with he | he <;> rw [he] <;> exact h
    | block s b raw sup rows =>
      dsimp only
      cases hp : parentFG st b with
      | none => rw [admitBlock_refused p st s b raw sup rows (Or.inl hp)]; exact h
      | some P =>
        cases ha : blockAccepted p st s b P rows with
        | false =>
          rw [admitBlock_refused p st s b raw sup rows (Or.inr ⟨P, hp, ha⟩)]
          exact h
        | true =>
          obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s b raw sup P rows hp ha
          rw [he]
          have hs : ∀ w ∈ st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩],
              FGSA.wellFormed p w = true := by
            intro w hm
            rcases List.mem_append.mp hm with hm | hm
            · exact h w hm
            · rw [List.mem_singleton.mp hm, ← decode_eq_block.mp hd]
              exact hw
          dsimp only
          split
          · exact hs
          · rw [(reconcile_frame _).2.1]
            exact hs

private theorem relay_proposals_wf (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) :
    ∀ o ∈ (V2.D.Run.stateBefore E rho i x).st.proposals, FGSA.wellFormed p o = true := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd => ∀ o ∈ nd.st.proposals, FGSA.wellFormed p o = true) (Nat.zero_le i) x ?_ ?_
  · intro j e _ _ he hx hj
    cases e with
    | restart v t =>
      change v = x at hx; subst v
      simp only [V2.D.World.step, Function.update_self]
      exact fun _ h => (List.not_mem_nil h).elim
    | tick v t =>
      change v = x at hx; subst v
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st E rho (V2.D.Run.stateBefore E rho j x) x t, clock_proposals]
      exact hj
    | deliver v o t =>
      change v = x at hx; subst v
      simp only [V2.D.World.step, Function.update_self]
      exact relay_proposals_process _ o hj (hE.wire j x o t he)
  · exact fun _ h => (List.not_mem_nil h).elim

private theorem relay_support_subset (st : State p.n) (s : Slot)
    (h : ∀ w ∈ st.proposals, FGSA.wellFormed p w = true) :
    headSupport p st s ⊆ headVotes p st s := by
  intro o ho
  change o ∈ List.eraseDups (_ ++ _) at ho ⊢
  rw [List.mem_eraseDups, List.mem_append] at ho ⊢
  rcases ho with ho | ho
  · left
    obtain ⟨hv, hr⟩ := List.mem_filter.mp ho
    apply List.mem_filter.mpr
    refine ⟨hv, ?_⟩
    change (match GridCO.headTarget? o with | none => false | some _ => _) = true at hr
    cases ht : GridCO.headTarget? o with
    | none => simp only [ht, Bool.false_eq_true] at hr
    | some B =>
      rw [ht] at hr
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).2
  · right
    obtain ⟨hm, hf⟩ := List.mem_filter.mp ho
    apply List.mem_filter.mpr
    refine ⟨?_, (Bool.and_eq_true_iff.mp hf).1⟩
    obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    have hrow := hr
    obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp hr
    cases hdw : w.decode with
    | none => rw [hdw] at hd; cases hd
    | some m =>
      cases m with
      | vote r k B => rw [hdw] at hd; cases hd
      | row k body => rw [hdw] at hd; cases hd
      | block r B raw sup rows =>
        rw [hdw] at hd
        dsimp only at hd
        split at hd
        · cases hd
          have hwf := h w hw
          change (match w.decode with
            | some (.vote _ _ _) => true
            | some (.row _ body) => body.valid
            | some (.block r B raw sup rows) =>
              B != .genesis && r == B.slot && decide (B.parent.slot < B.slot) &&
                raw.all (fun v => match v.decode? with
                  | some (r, _, _) => r + 1 == B.slot | none => false) &&
                sup.all (fun v => decide (v ∈ raw)) &&
                rows.all RowWire.valid && rowsOk B rows
            | none => false) = true at hwf
          rw [hdw] at hwf
          have hsub := (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hwf).1).1).2
          apply List.mem_flatMap.mpr
          refine ⟨(raw, sup), hrow, ?_⟩
          exact List.mem_map.mpr ⟨a, of_decide_eq_true (List.all_eq_true.mp hsub a ha), he⟩
        · cases hd

/-- P3 §4.4.3 C5/C6; bp02 §4.2, G24 support inclusion. Class (ii), run instance.
DC: Handlers/GoldfishVotePool.lean:355–405. Same carried support subset;
INTENTIONAL: use admitted wire metadata and the actual post-clock HEAD store
(Model/Frame.lean:67–85), including inactive admitted proposals. -/
theorem fgsa_headSupport_subset_headVotes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot) :
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (SA.voteTime p.toParams (s + 1))).st
    headSupport p dst (s + 1) ⊆ headVotes p dst (s + 1) := by
  apply relay_support_subset
  change ∀ o ∈ (clock p _ _).proposals, _
  rw [clock_proposals]
  exact relay_proposals_wf E rho hE i x

private def RelayCarried (st : State p.n) (s : Slot) : Prop :=
  ∀ w ∈ st.proposals, ∀ r b raw sup rows,
    w.decode = some (.block r b raw sup rows) → b.slot = s + 1 →
    ∀ o ∈ raw.map baseVote, ∀ seat,
      GridCO.headLabel? o = some s → GridCO.headSeat? o = some seat →
      o ∈ GridCO.votesAt st.base s ∨
        GridCO.equivocates (GridCO.votesAt st.base s) seat = true

private theorem relay_settled_mono {v v' : GridCO.State p.n} (s : Slot)
    (h : v.votes ⊆ v'.votes) (o : GridCO.Wire p.n) (seat : Fin p.n)
    (hr : o ∈ GridCO.votesAt v s ∨ GridCO.equivocates (GridCO.votesAt v s) seat = true) :
    o ∈ GridCO.votesAt v' s ∨ GridCO.equivocates (GridCO.votesAt v' s) seat = true := by
  have hs : GridCO.votesAt v s ⊆ GridCO.votesAt v' s := by
    intro a ha
    obtain ⟨ha, hl⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr ⟨h ha, hl⟩
  exact hr.elim (fun hm => Or.inl (hs hm))
    (fun he => Or.inr (Gen.AC.vote_pool_equivocates_mono _ _ seat hs he))

private theorem relay_carried_mono {st st' : State p.n} (s : Slot)
    (hp : st'.proposals = st.proposals) (hv : st.base.votes ⊆ st'.base.votes)
    (h : RelayCarried st s) : RelayCarried st' s := by
  intro w hw r b raw sup rows hd hb o ho seat hl hk
  rw [hp] at hw
  exact relay_settled_mono s hv o seat (h w hw r b raw sup rows hd hb o ho seat hl hk)

private theorem relay_fold_heads (raw : List (GridCO.HeadWire p.n))
    (st : GridCO.State p.n) (s : Slot) (seat : Fin p.n) (B : Block)
    (hlo : (st.now / (4 * p.toParams.engine.Δ)).toNat - 1 ≤ s)
    (hhi : s ≤ (st.now / (4 * p.toParams.engine.Δ)).toNat)
    (hraw : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n) ∈ raw.map GridCO.fromHead) :
    let post := raw.foldl
      (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row)) st
    (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n) ∈ post.votes ∨
      GridCO.equivocates (GridCO.votesAt post s) seat = true := by
  induction raw generalizing st with
  | nil => exact (List.not_mem_nil hraw).elim
  | cons row raw ih =>
    dsimp only
    have hf (v : GridCO.State p.n) : v.votes ⊆
        (raw.foldl (fun acc row => GridCO.admitVote p.toParams.engine acc
          (GridCO.fromHead row)) v).votes := by
      clear ih hraw
      induction raw generalizing v with
      | nil => exact List.Subset.refl _
      | cons a raw ih =>
          exact List.Subset.trans (Internal.grid_admitVote_votes_subset _ _) (ih _)
    rcases List.mem_cons.mp hraw with he | hm
    · have hh : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n) ∈
          (GridCO.admitVote p.toParams.engine st ⟨.seat s seat, .head B⟩).votes ∨
          GridCO.equivocates (GridCO.votesAt
            (GridCO.admitVote p.toParams.engine st ⟨.seat s seat, .head B⟩) s) seat = true := by
        by_cases hc : GridCO.equivocates (GridCO.votesAt st s) seat = true
        · right; simp only [GridCO.admitVote, hc, Bool.or_true, ite_true]
        · left
          by_cases hm : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n) ∈ st.votes
          · simp [GridCO.admitVote, hm]
          · simp [GridCO.admitVote, not_lt.mpr hlo, not_lt.mpr hhi, hm, hc]
      rw [he] at hh
      rcases hh with hm | hc
      · left; rw [he]; exact hf _ hm
      · exact Or.inr (vote_pool_equivocates_mono _ _ seat
          (Internal.grid_votesAt_subset _ _ s (hf _)) hc)
    · exact ih _ (by simpa only [Internal.grid_admitVote_now] using hlo)
        (by simpa only [Internal.grid_admitVote_now] using hhi) hm

private theorem relay_carried_process (st : State p.n) (hInv : CStoreInv p st)
    (s : Slot) (hslot : st.slot p ≤ s + 1) (parent : Wire p.n)
    (h : RelayCarried st s) : RelayCarried (FGSA.process p st parent) s := by
  have hv := process_votes_subset st parent
  change RelayCarried (match parent.decode with
    | some (.vote r i b) => admitHead p st r i b
    | some (.row _ body) => admitRow p st ⟨parent.auth, body⟩
    | some (.block r b raw sup rows) => admitBlock p st r b raw sup rows
    | none => st) s
  cases hd : parent.decode with
  | none => exact h
  | some m =>
    cases m with
    | vote r i b =>
      exact relay_carried_mono (st := st) s rfl (Internal.grid_admitVote_votes_subset _ _) h
    | row i body =>
      dsimp only
      rcases admitRow_eq p st ⟨parent.auth, body⟩ with he | he <;> rw [he]
      · exact h
      · exact h
    | block r b raw sup rows =>
      dsimp only
      cases hp : parentFG st b with
      | none => rw [admitBlock_refused p st r b raw sup rows (Or.inl hp)]; exact h
      | some P =>
        cases ha : blockAccepted p st r b P rows with
        | false =>
          rw [admitBlock_refused p st r b raw sup rows (Or.inr ⟨P, hp, ha⟩)]
          exact h
        | true =>
          have hprops : (admitBlock p st r b raw sup rows).proposals =
              st.proposals ++ [⟨.proposer r, .proposal b raw sup rows⟩] := by
            obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st r b raw sup P rows hp ha
            rw [he]
            exact (accepted_st2 p st hInv r b raw sup P rows hp ha).1
          have hvotes : (admitBlock p st r b raw sup rows).base.votes =
              ((raw.map baseHead).foldl
                (fun acc row => GridCO.admitVote p.toParams.engine acc (GridCO.fromHead row))
                { st.base with
                  blocks := st.base.blocks ++ [b]
                  blockStamp := st.base.blockStamp ++ [(b, st.base.now)],
                  proposals := st.base.proposals ++ [baseProposal r b raw sup] }).votes := by
            obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st r b raw sup P rows hp ha
            rw [he]
            dsimp only
            have hb := congrArg GridCO.State.votes
              (admitProposal_base_view p st hInv.toInv0 r b raw sup P rows hp ha).1
            split
            · exact hb
            · exact (reconcile_frame _).2.2.2.2.2.1.trans hb
          intro w hw r' b' raw' sup' rows' hd' hb o ho seat hl hk
          rw [hprops] at hw
          rcases List.mem_append.mp hw with hw | hw
          · have hv' : st.base.votes ⊆ (admitBlock p st r b raw sup rows).base.votes := by
              change st.base.votes ⊆ (match parent.decode with
                | some (.vote r i b) => admitHead p st r i b
                | some (.row _ body) => admitRow p st ⟨parent.auth, body⟩
                | some (.block r b raw sup rows) => admitBlock p st r b raw sup rows
                | none => st).base.votes at hv
              rw [hd] at hv
              exact hv
            exact relay_settled_mono s hv' o seat
              (h w hw r' b' raw' sup' rows' hd' hb o ho seat hl hk)
          · have he := List.mem_singleton.mp hw
            subst w
            change some (Input.block r b raw sup rows) =
              some (Input.block r' b' raw' sup' rows') at hd'
            cases hd'
            have hwindow : st.slot p = s + 1 :=
              le_antisymm hslot (hb ▸ (blockAccepted_facts ha).2.1)
            obtain ⟨B, rfl⟩ := relay_vote_shape o s seat hl hk
            have hh := relay_fold_heads
              (raw.map baseHead)
              { st.base with
                blocks := st.base.blocks ++ [b]
                blockStamp := st.base.blockStamp ++ [(b, st.base.now)],
                proposals := st.base.proposals ++ [baseProposal r b raw sup] }
              s seat B (by change st.slot p - 1 ≤ s; rw [hwindow, Nat.add_sub_cancel])
              (by change s ≤ st.slot p; rw [hwindow]; exact Nat.le_succ s)
              (by rw [List.map_map]; change _ ∈ raw.map baseVote; exact ho)
            change _ ∈ (GridCO.votesAt _ s) ∨ _
            unfold GridCO.votesAt at hh ⊢
            rw [hvotes]
            exact hh.elim
              (fun hm => Or.inl (List.mem_filter.mpr
                ⟨hm, by change (some s == some s) = true; exact beq_self_eq_true _⟩))
              Or.inr

private theorem relay_carried_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    (k : Nat) (y : V) (s : Slot)
    (htick : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    RelayCarried (V2.D.Run.stateBefore E rho k y).st s := by
  have hu (j : Nat) (hj : j ≤ k) : (V2.D.Run.stateBefore E rho j y).st.slot p ≤ s + 1 := by
    have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN hj y
    have hb := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hS htick y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j y),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hm
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hb
    have he : p.slotOf (SA.voteTime p.toParams (s + 1)) = s + 1 := by
      exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho k y) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ (s + 1))
    exact (Internal.slotOf_mono (p := p) (hm.trans hb)).trans_eq he
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd => RelayCarried nd.st s) (Nat.zero_le k) y ?_ ?_
  · intro j e hj hk he hy ih
    cases e with
    | restart v t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      exact fun _ h => (List.not_mem_nil h).elim
    | tick v t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st E rho (V2.D.Run.stateBefore E rho j y) y t]
      exact relay_carried_mono s (clock_proposals p _ t)
        (by rw [(clock_vn _ t).1]) ih
    | deliver v o t =>
      change v = y at hy; subst v
      simp only [V2.D.World.step, Function.update_self]
      exact relay_carried_process _ (cstoreInv_stateBefore E rho j y) s (hu j (by omega))
        (toWire p o) ih
  · exact fun _ h => (List.not_mem_nil h).elim

/-- P3 §4.4.3 C6; bp02 §4.2 backward receipt. Class (ii), FG-SA run instance.
DC: Handlers/GoldfishVotePool.lean:755,791 (carried settlement).
Same vote-or-cap conclusion. The actual post-clock HEAD merge reads cumulative
FG-SA proposal metadata; the admission guard supplies the inner vote window. -/
theorem fgsa_headVotes_provenance (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (k : Nat) (y : V) (s : Slot)
    (htick : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    let pre := (V2.D.Run.stateBefore E rho k y).st
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    ∀ o ∈ headVotes p dst (s + 1), ∀ seat, GridCO.headSeat? o = some seat →
      o ∈ GridCO.votesAt pre.base s ∨
        GridCO.equivocates (GridCO.votesAt pre.base s) seat = true := by
  intro pre dst o ho seat hk
  change o ∈ List.eraseDups (_ ++ _) at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with ho | ho
  · left
    have hm := (List.mem_filter.mp ho).1
    change o ∈ GridCO.votesAt (clock p pre _).base (s + 1 - 1) at hm
    simpa only [GridCO.votesAt, Nat.add_sub_cancel, (clock_vn pre _).1] using hm
  · obtain ⟨ho, hl⟩ := List.mem_filter.mp ho
    have hl' : GridCO.headLabel? o = some s := by
      simpa only [Nat.add_sub_cancel, beq_iff_eq] using hl
    obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp ho
    obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp hr
    have hw' : w ∈ pre.proposals := by
      change w ∈ (clock p pre _).proposals at hw
      rwa [clock_proposals] at hw
    cases hdw : w.decode with
    | none => rw [hdw] at hd; cases hd
    | some m =>
      cases m with
      | vote r i B => rw [hdw] at hd; cases hd
      | row i body => rw [hdw] at hd; cases hd
      | block r B raw sup rows =>
        rw [hdw] at hd
        dsimp only at hd
        split at hd
        · rename_i hb
          cases hd
          exact relay_carried_run E rho hE.toScheduleWellFormed hN k y s htick
            w hw' r B raw sup rows hdw hb o hm seat hl' hk
        · cases hd

/-- P3 §4.4.3 C6; bp02 §4.2 backward receipt. Class (ii), run provenance.
DC: Handlers/GoldfishVotePool.lean:755,791, strict stored witness stamps.
The actual q_s tick bounds each retained witness stamp; T7.8 recovers its
own earlier acceptance, including witnesses that capped a carried vote. -/
theorem fgsa_vote_accepted_before_head_read (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (k : Nat) (y : V) (s : Slot)
    (htick : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (seat : Fin p.n) (B : Block)
    (hm : (⟨.seat s seat, .head B⟩ : GridCO.Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.base.votes) :
    ∃ j < k, ∃ t, V2.D.Run.acceptsAt E rho j y (ofHead p ⟨.seat (.head s) seat, B⟩) t ∧
      t < SA.voteTime p.toParams (s + 1) := by
  have hpos : 0 < SA.voteTime p.toParams (s + 1) := by
    change 0 < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    have hd := p.deltaPos
    positivity
  refine fgsa_vote_accepted_before E rho hS hN k y s seat B
    (SA.voteTime p.toParams (s + 1)) ?_ (le_of_lt hpos) hm ?_
  · refine ⟨4 * (s + 1) + 1, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = _
    push_cast
    ring
  · have hn := fgsa_preTick_now_lt E rho hS htick hpos
    have hb := (fgsa_stateBefore_bounds E rho hS k y).2
    unfold GridCO.stampVote
    cases hf : (V2.D.Run.stateBefore E rho k y).st.base.voteStamp.find?
        (fun row => row.1 == ⟨.seat s seat, .head B⟩) with
    | none => exact hn
    | some row => exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

private theorem relay_head_witness (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSync E rho (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (o : GridCO.Wire p.n) (ho : o ∈ GridCO.votesAt (V2.D.Run.stateBefore E rho iy y).st.base s)
    (seat : Fin p.n) (hk : GridCO.headSeat? o = some seat) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late seat = true := by
  dsimp only
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  have hl' : GridCO.headLabel? o = some s := by simpa only [beq_iff_eq] using hl
  obtain ⟨B, rfl⟩ := relay_vote_shape o s seat hl' hk
  obtain ⟨j, _, t, ha, ht⟩ :=
    fgsa_vote_accepted_before_head_read E rho hE.toScheduleWellFormed hN hDelta iy y s hiy seat B hm
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hd : dl t < SA.gateTime p.toParams s := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
    push_cast at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t < 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) <
        4 * p.Δ * (s : Int) + 5 * p.Δ := max_lt (by linarith) (by linarith)
    linarith
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s seat B t x hD
    (Or.inr ⟨y, hy, j, ha⟩) hx ((le_of_lt hd).trans hcut) (hlt t)
    (relay_read_window E rho hE.toScheduleWellFormed hN hix (dl t) (le_of_lt hd))
  have hkeep : (V2.D.Run.stateBeforeTime E rho (dl t) x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho ix x).st.base.votes := by
    rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hix,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact relay_votes_mono E rho hN x (relay_idx_mono rho (le_of_lt hd))
  rcases hr with hr | ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩
  · exact Or.inl (relay_gate_late E rho hE.toScheduleWellFormed hix _ (hkeep hr.1) rfl)
  · exact Or.inr ((cap_pair _ seat).mpr ⟨u,
      relay_gate_late E rho hE.toScheduleWellFormed hix u (hkeep hu) hlu, v,
      relay_gate_late E rho hE.toScheduleWellFormed hix v (hkeep hv) hlv, hne, hku, hkv⟩)

/-- P3 §4.4.3 C6; bp02 §4.2 backward receipt, Gen.AC.transfer item 5.
Class (ii), FG-SA run receipt instance. DC: Handlers/GoldfishVotePool.lean:755,791;
Schedule/AdoptionTransport.lean:346. Same vote-or-cap transport into the source
late pool. U is the full post-clock HEAD raw merge at the actual q_s tick;
L is the source gate clockPre/actView pool at d_s. Each stored witness has
an acceptance t < q_s and LabelSync deadline dl(t) < q_s + Δ = d_s. -/
theorem fgsa_headVotes_backward_relay (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSync E rho (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    let U := headVotes p dst (s + 1)
    let L := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s
    ∀ o ∈ U, ∀ seat, GridCO.headSeat? o = some seat →
      o ∈ L ∨ GridCO.equivocates L seat = true := by
  intro dst U L o ho seat hk
  rcases fgsa_headVotes_provenance E rho hE hN iy y s hiy o ho seat hk with hm | he
  · exact relay_head_witness E rho hE hN hDelta s hSync hx hy hix hiy o hm seat hk
  · obtain ⟨u, hu, v, hv, hne, hku, hkv⟩ := (cap_pair _ seat).mp he
    rcases relay_head_witness E rho hE hN hDelta s hSync hx hy hix hiy u hu seat hku with hu | he
    · rcases relay_head_witness E rho hE hN hDelta s hSync hx hy hix hiy v hv seat hkv with hv | he
      · exact Or.inr ((cap_pair L seat).mpr ⟨u, hu, v, hv, hne, hku, hkv⟩)
      · exact Or.inr he
    · exact Or.inr he

private theorem relay_stamp_prefix (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.base.voteStamp <+:
      (V2.D.Run.stateBefore E rho j x).st.base.voteStamp := by
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => (V2.D.Run.stateBefore E rho i x).st.base.voteStamp <+: nd.st.base.voteStamp)
    ?_ ?_ (fun _ _ h => h) E rho hij x (hN.restartFree x i j) (List.prefix_refl _)
  · intro nd t h
    change _ <+: (clock p nd.st t).base.voteStamp
    rwa [(clock_cumulative p nd.st t).2.2.2.1]
  · intro nd o h
    exact h.trans (process_cumulative p nd.st (toWire p o)).2.2.2.1

private theorem relay_stamp_of_prefix (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (v : GridCO.State p.n) (o : GridCO.Wire p.n)
    (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hp : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp <+: v.voteStamp) :
    GridCO.stampVote v o = GridCO.stampVote (V2.D.Run.stateBefore E rho i x).st.base o := by
  rw [← fgsa_vote_stamp_keys E rho i x] at hm
  obtain ⟨⟨w, t⟩, ht, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst w
  obtain ⟨tail, htail⟩ := hp
  unfold GridCO.stampVote
  rw [← htail, List.find?_append]
  cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
      (fun row => row.1 == o) with
  | none =>
    have hn := List.find?_eq_none.mp hf (o, t) ht
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

private theorem relay_frozen_raw (st : State p.n) (s : Slot) (o : GridCO.Wire p.n)
    (hm : o ∈ st.base.votes) (hl : GridCO.headLabel? o = some s)
    (ht : GridCO.stampVote st.base o < SA.freezeTime p.toParams s) :
    o ∈ headVotes p st (s + 1) := by
  change o ∈ List.eraseDups (_ ++ _)
  rw [List.mem_eraseDups, List.mem_append]
  left
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨hm, ?_⟩, ?_⟩
  · simpa only [Nat.add_sub_cancel, hl] using beq_self_eq_true (some s)
  · simpa only [Nat.add_sub_cancel] using decide_eq_true ht

/-- P3 §4.4.3 C5; bp02 §4.2 forward receipt. Class (ii), run receipt instance.
DC: Schedule/AdoptionTransport.lean:309, settled-before-freeze raw arm.
The source gate's early stamp gives dl(t) < z_s. NoRestart keeps the vote
and its stamp, or both cap witnesses, through the actual post-clock q_s read.
This is vote settlement only; active HEAD support also needs the path. -/
theorem fgsa_cleanSupport_vote_forward (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSync E rho (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (_hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s)
    (seat : Fin p.n) (hk : GridCO.headSeat? o = some seat) :
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    (o ∈ dst.base.votes ∧ GridCO.stampVote dst.base o < SA.freezeTime p.toParams s) ∨
      GridCO.equivocates (headVotes p dst (s + 1)) seat = true := by
  intro dst
  have hc := relay_clean_mem p _ s o ho
  obtain ⟨K, rfl⟩ := relay_vote_shape o s seat hc.2.1 hk
  have hmem : (⟨.seat s seat, .head K⟩ : GridCO.Wire p.n) ∈
      (V2.D.Run.stateBefore E rho ix x).st.base.votes := by
    have hm := hc.1
    change _ ∈ (clockPre p _ _).base.votes at hm
    rwa [(Internal.clockPre_vn _ _).1] at hm
  have ht := hc.2.2.1
  rw [relay_read_stamp E rho ix x (SA.gateTime p.toParams s) _ hmem] at ht
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
    ix x s seat K _ hpub hz hmem ht
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hd : dl t < SA.freezeTime p.toParams s := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) <
        4 * p.Δ * (s : Int) + 2 * p.Δ := max_lt ht (by linarith)
    linarith
  have hzq : SA.freezeTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    have hp := p.deltaPos
    linarith
  have hqd : SA.voteTime p.toParams (s + 1) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    linarith
  have hdq := le_of_lt (hd.trans hzq)
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl t) y).st.slot p ≤ s + 1 := by
    have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho
      hE.toScheduleWellFormed hN (relay_idx_mono rho hdq) y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (dl t)) y),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho
        (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) y),
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed,
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed,
      ← fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hiy] at hm
    have hb := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hE.toScheduleWellFormed hiy y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho iy y)] at hb
    have he : p.slotOf (SA.voteTime p.toParams (s + 1)) = s + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho iy y) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ (s + 1))
    exact (Internal.slotOf_mono (p := p) (hm.trans hb)).trans_eq he
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s seat K t y hD
    (Or.inr ⟨x, hx, j, ha⟩) hy (hdq.trans (hqd.trans hcut)) (hlt t) hwindow
  have hkeep : (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base.votes ⊆ dst.base.votes ∧
      (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base.voteStamp <+: dst.base.voteStamp := by
    change _ ⊆ (clock p _ _).base.votes ∧ _ <+: (clock p _ _).base.voteStamp
    rw [(clock_vn _ _).1, (clock_cumulative p _ _).2.2.2.1,
      fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hiy,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact ⟨relay_votes_mono E rho hN y (relay_idx_mono rho hdq),
      relay_stamp_prefix E rho hN y (relay_idx_mono rho hdq)⟩
  have hs (v : GridCO.Wire p.n)
      (hm : v ∈ (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base.votes)
      (ht : GridCO.stampVote (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base v < dl t) :
      GridCO.stampVote dst.base v < SA.freezeTime p.toParams s := by
    have hp := hkeep.2
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed] at hm hp ht
    rw [relay_stamp_of_prefix E rho _ y dst.base v hm hp]
    exact ht.trans hd
  rcases hr with ⟨hm, ht⟩ | ⟨u, hu, v, hv, hn, hlu, hlv, hku, hkv, htu, htv⟩
  · exact Or.inl ⟨hkeep.1 hm, hs _ hm ht⟩
  · exact Or.inr ((cap_pair _ seat).mpr ⟨u,
      relay_frozen_raw dst s u (hkeep.1 hu) hlu (hs u hu htu), v,
      relay_frozen_raw dst s v (hkeep.1 hv) hlv (hs v hv htv), hn, hku, hkv⟩)

/-- P3 §4.4.3 C5; bp02 §4.2 forward support incidence. Class (ii), run instance.
DC: Handlers/GoldfishVotePool.lean:810, ancestor membership; generic support
uses the cumulative block tree. INTENTIONAL: path receipt form (b) is explicit
at the post-clock q_s read. It supplies membership without an active-view claim. -/
theorem fgsa_voteSupports_of_path (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (ix iy : Nat) (x y : V) (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s)
    (K : FGBlock (Fin p.n)) (hK : GridCO.headTarget? o = some (eraseFG K))
    (B : Block) (hBK : Block.Preceq B (eraseFG K))
    (hpath : ∀ A, FGBlock.Preceq A K →
      A ∈ (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))).st).fg.TF ∧
      GridCO.stampBlock (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))).st).base (eraseFG A) < SA.freezeTime p.toParams s) :
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    Gen.AC.voteSupports dst.base.blocks B o = true := by
  intro dst
  have hmem := (hpath K (KitFG.preceq_refl K)).1
  have hInv : CStoreInv p dst :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hstored := (hInv.baseTree (eraseFG K)).mpr ⟨K, hmem, rfl⟩
  have hr := (List.mem_filter.mp (List.mem_filter.mp ho).1).2
  change GridCO.resolvedBefore _ o _ = true at hr
  unfold GridCO.resolvedBefore at hr
  rw [hK] at hr
  have hslot := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp hr).1).1).2
  rw [Gen.AC.voteSupports_def, hK]
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true hstored, hslot⟩, hBK⟩

/-- P3 §4.4.3 C5; bp02 §4.2, K9 then K8 forward support transport.
Class (ii), FG-SA run instance. DC: Schedule/AdoptionTransport.lean:346,
`gfVote_delivery_settled_at_confStore`, vote-or-cap settlement counterpart.
INTENTIONAL: the current actView needs an explicit target frame bound.
Clean supplies hframe by erasing clean_transfer_frame's F ⪯ Bfg conjunct
with eraseFG Bfg = B, at k = iy and exactly st = dst (post-clock q_s).
Path receipt form (b) supplies cumulative membership and strict head stamps. -/
theorem fgsa_cleanSupport_forward_relay (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSync E rho (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s)
    (seat : Fin p.n) (hk : GridCO.headSeat? o = some seat)
    (K : FGBlock (Fin p.n)) (hK : GridCO.headTarget? o = some (eraseFG K))
    (B : Block) (hBK : Block.Preceq B (eraseFG K))
    (hpath : ∀ A, FGBlock.Preceq A K →
      A ∈ (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))).st).fg.TF ∧
      GridCO.stampBlock (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))).st).base (eraseFG A) < SA.freezeTime p.toParams s)
    (hframe : Block.Preceq
      (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))).st).fg.F) B) :
    let dst := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    (o ∈ FGSA.headSupport p dst (s + 1) ∧ Gen.AC.voteSupports dst.base.blocks B o = true) ∨
      GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
  intro dst
  rcases fgsa_cleanSupport_vote_forward E rho hE hN hDelta s hSync hx hy hix hiy
    o ho seat hk with ⟨hm, ht⟩ | he
  · have hs : Gen.AC.voteSupports dst.base.blocks B o = true :=
      fgsa_voteSupports_of_path E rho s ix iy x y o ho K hK B hBK hpath
    have hparts := hs
    rw [Gen.AC.voteSupports_def, hK] at hparts
    obtain ⟨hknown, hslot⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hparts).1
    have hactive : eraseFG K ∈ (actView dst).blocks := by
      apply (actView_blocks dst _).mpr
      exact ⟨of_decide_eq_true hknown,
        Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _)
          (Gen.Pure.block_preceq_trans hframe hBK)⟩
    refine Or.inl ⟨?_, hs⟩
    change o ∈ List.eraseDups (_ ++ _)
    rw [List.mem_eraseDups, List.mem_append]
    left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hm, ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_cancel, (relay_clean_mem p _ s o ho).2.1]
        using beq_self_eq_true (some s)
    · unfold GridCO.resolvedBefore
      rw [hK]
      apply Bool.and_eq_true_iff.mpr
      refine ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_, hslot⟩, ?_⟩, ?_⟩
      · exact decide_eq_true hactive
      · change decide (GridCO.stampVote dst.base o < SA.freezeTime p.toParams (s + 1 - 1)) = true
        simpa only [Nat.add_sub_cancel] using decide_eq_true ht
      · change decide (GridCO.stampBlock dst.base (eraseFG K) <
          SA.freezeTime p.toParams (s + 1 - 1)) = true
        simpa only [Nat.add_sub_cancel] using
          decide_eq_true (hpath K (KitFG.preceq_refl K)).2
  · exact Or.inr he

end AvailableChain.FGSA.Run
end
