module
public import AvailableChainGridCO.Proofs.Receipts

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem fold_votes_blocks (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih => rw [List.foldl_cons, ih, admitVote_blocks]

/-- A new stored block is the block of the directly delivered proposal. -/
theorem process_new_block (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (hn : B ∉ st.blocks) (hm : B ∈ (process p st o).blocks) :
    ∃ raw support, o.payload = .proposal B raw support := by
  unfold process at hm
  split at hm
  · exact (hn (by simpa [admitVote_blocks] using hm)).elim
  · rename_i slot target raw support ha hp
    unfold admitProposal at hm
    dsimp only at hm
    split at hm <;> split at hm
    all_goals first
      | exact (hn hm).elim
      | rw [fold_votes_blocks] at hm
        have he : B = target := by simpa [hn] using hm
        exact ⟨raw, support, by simpa [he] using hp⟩
  · exact (hn hm).elim

/-- Admission rejects a new block whose slot is ahead of the local clock. -/
theorem process_new_block_slot (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (hn : B ∉ st.blocks) (hm : B ∈ (process p st o).blocks) :
    B.slot ≤ (st.now / (4 * p.Δ)).toNat := by
  unfold process at hm
  split at hm
  · exact (hn (by simpa [admitVote_blocks] using hm)).elim
  · rename_i slot target raw support ha hp
    unfold admitProposal at hm
    dsimp only at hm
    split at hm <;> split at hm
    all_goals first
      | exact (hn hm).elim
      | rename_i hgood
        rw [fold_votes_blocks] at hm
        have he : B = target := by simpa [hn] using hm
        rw [he]
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or,
          Bool.not_eq_false, decide_eq_false_iff_not] at hgood
        have hb : ¬ target.slot > (st.now / (4 * p.Δ)).toNat := by tauto
        exact le_of_not_gt hb
  · exact (hn hm).elim

/-- Every non-genesis stored block has an earlier accepted proposal at
that reader. This is the path source needed by accepted-object relay. -/
theorem stored_block_accepted {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) (B : Block)
    (hn : B ≠ .genesis)
    (hm : B ∈ (Run.stateBefore (gridCO p) rho index reader).blocks) :
    ∃ j < index, ∃ t o raw support,
      rho.events[j]? = some (.deliver reader o t) ∧
      o.payload = .proposal B raw support ∧
      Run.acceptsAt (gridCO p) rho j reader o t := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial, hn] at hm
  | succ index ih =>
      by_cases hold : B ∈ (Run.stateBefore (gridCO p) rho index reader).blocks
      · obtain ⟨j, hj, rest⟩ := ih hold
        exact ⟨j, by omega, rest⟩
      · cases hi : rho.events[index]? with
        | none => simp [Run.stateBefore, List.take_add_one, hi] at hm; exact (hold hm).elim
        | some e =>
            have hpost := stateBefore_succ_event hi
            rw [hpost] at hm
            cases e with
            | tick v t =>
                by_cases hv : reader = v
                · subst v
                  have he := congrArg Prod.fst
                    (clock_receiptData p (Run.stateBefore (gridCO p) rho index reader) t)
                  have hm' : B ∈
                      (clock p (Run.stateBefore (gridCO p) rho index reader) t).blocks := by
                    simpa only [World.step, Function.update_self] using hm
                  simp only [receiptData] at he
                  rw [he] at hm'
                  exact (hold hm').elim
                · exact (hold (by simpa [World.step, hv] using hm)).elim
            | deliver v o t =>
                by_cases hv : reader = v
                · subst v
                  have hnew : B ∈
                      (process p (Run.stateBefore (gridCO p) rho index reader) o).blocks := by
                    simpa [World.step] using hm
                  obtain ⟨raw, support, hp⟩ := process_new_block p _ o B hold hnew
                  refine ⟨index, by omega, t, o, raw, support, hi, hp, ?_⟩
                  refine ⟨⟨o, hi, Or.inl rfl⟩, ?_, ?_⟩
                  · simpa [gridCO, processed, hp, blockKnown] using hold
                  · rw [hpost]
                    simpa [World.step, gridCO, processed, hp, blockKnown] using hnew
                · exact (hold (by simpa [World.step, hv] using hm)).elim

/-- The stored path before a HEAD cannot contain a future-slot block. -/
theorem stored_before_head_slot_le {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) (B : Block)
    (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) reader).blocks) :
    B.slot ≤ r := by
  by_cases hg : B = .genesis
  · simp [hg, Block.slot]
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨i, hil, t, o, raw, support, hi, hp, ha⟩ :=
    stored_block_accepted p rho _ reader B hg hm
  have ht : t < voteTime p r :=
    Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (voteTime p r - 1) hi).mp hil)
  have hn : B ∉ (Run.stateBefore (gridCO p) rho i reader).blocks := by
    simpa [gridCO, processed, hp, blockKnown] using ha.2.1
  have hb : B ∈ (process p (Run.stateBefore (gridCO p) rho i reader) o).blocks := by
    have h := ha.2.2
    rw [stateBefore_succ_event hi] at h
    simpa [World.step, gridCO, processed, hp, blockKnown] using h
  apply (process_new_block_slot p _ o B hn hb).trans
  apply Int.toNat_le.mpr
  apply (Int.ediv_le_iff_le_mul (by linarith [p.deltaPos])).mpr
  have hnow := (stateBefore_now_le_event p E rho hs hi reader).trans_lt ht
  dsimp [voteTime, proposalTime] at hnow
  nlinarith [p.deltaPos]

/-- Every reader's clock is at most the time of a completed event. -/
theorem stateAfter_now_le_event {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V (gridCO p).Object}
    (hi : rho.events[i]? = some e) (reader : V) :
    (Run.stateBefore (gridCO p) rho (i + 1) reader).now ≤ e.time := by
  have h := stateBefore_now_le_event p E rho hs hi reader
  rw [stateBefore_succ_event hi]
  cases e with
  | tick v t =>
      by_cases hv : reader = v
      · subst v; simp [World.step, gridCO, clock_now, Event.time]
      · simpa [World.step, hv] using h
  | deliver v o t =>
      by_cases hv : reader = v
      · subst v; simpa [World.step, gridCO, process_now] using h
      · simpa [World.step, hv] using h

/-- A block already stored after an event before the cutoff retains an
early block stamp at each later strict read. The event can be at any node. -/
theorem stored_block_stamp_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V (gridCO p).Object} {reader : V} {B : Block}
    {early cut : Time} (hi : rho.events[i]? = some e)
    (hm : B ∈ (Run.stateBefore (gridCO p) rho (i + 1) reader).blocks)
    (ht : e.time < early) (hcut : early ≤ cut) :
    B ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).blocks ∧
      stampBlock (Run.stateBeforeTime (gridCO p) rho cut reader) B < early := by
  have hp : ReceiptPrefix (Run.stateBefore (gridCO p) rho (i + 1) reader)
      (Run.stateBeforeTime (gridCO p) rho cut reader) := by
    rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_receiptPrefix
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
      (Int.le_sub_one_iff.mpr (ht.trans_le hcut)))
  refine ⟨hp.blocks.subset hm, ?_⟩
  rw [hp.stampBlock (run_receiptStamped p rho (i + 1) reader) B hm]
  exact ((run_stampsBounded p E rho hs (i + 1) reader).stampBlock_le B).trans_lt
    ((stateAfter_now_le_event p E rho hs hi reader).trans_lt ht)

/-- Genesis is always stored with its original zero stamp. -/
theorem genesis_stored_at_time {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) :
    Block.genesis ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).blocks ∧
      stampBlock (Run.stateBeforeTime (gridCO p) rho cut reader) .genesis = 0 := by
  rw [time_input_eq_event_prefix p E rho hs]
  have hp := stateBefore_receiptPrefix p rho (Nat.zero_le
    (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length) reader
  have hm : Block.genesis ∈ (Run.stateBefore (gridCO p) rho 0 reader).blocks := by
    simp [Run.stateBefore, World.init, gridCO, initial]
  exact ⟨hp.blocks.subset hm, (hp.stampBlock (run_receiptStamped p rho 0 reader) _ hm)⟩

/-- Any path block stored before the HEAD time relays before the early
cutoff of a synchronous label. Both delivery regimes use accepted relay. -/
theorem synchronous_block_path_at_gate {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B : Block) (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) source).blocks) :
    B ∈ (gateInput p rho r reader).blocks ∧
      stampBlock (gateInput p rho r reader) B < earlyTime p r := by
  have hsched := hsync.execution.toScheduleWellFormed
  have hearly : earlyTime p r ≤ gateTime p r := by
    dsimp [earlyTime, gateTime]; linarith [p.deltaPos]
  by_cases hg : B = .genesis
  · subst B
    obtain ⟨hm, ht⟩ := genesis_stored_at_time p E rho hsched (gateTime p r) reader
    refine ⟨hm, ?_⟩
    change stampBlock (Run.stateBeforeTime (gridCO p) rho (gateTime p r) reader) .genesis < _
    rw [ht]
    have hnat := Int.natCast_nonneg r
    dsimp [earlyTime, proposalTime]
    nlinarith [p.deltaPos]
  rw [time_input_eq_event_prefix p E rho hsched] at hm
  obtain ⟨index, hindex, t, o, raw, support, hi, hp, ha⟩ :=
    stored_block_accepted p rho _ source B hg hm
  have ht : t < voteTime p r := by
    have h := (index_lt_read_length_iff hsched (voteTime p r - 1) hi).mp hindex
    exact Int.le_sub_one_iff.mp h
  by_cases hknown : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = true
  · have hm : B ∈ (Run.stateBefore (gridCO p) rho (index + 1) reader).blocks := by
      simpa [processed, hp, blockKnown] using hknown
    exact stored_block_stamp_before_cut p E rho hsched hi hm
      (ht.trans (by dsimp [voteTime, earlyTime]; linarith [p.deltaPos])) hearly
  have hmissing : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = false :=
    Bool.eq_false_iff.mpr hknown
  have hdeadline : t + E.Δ ≤ earlyTime p r := by
    rw [hΔ]
    dsimp [voteTime, earlyTime] at ht ⊢
    linarith
  have hrelay : ∃ j t', Run.acceptsAt (gridCO p) rho j reader o t' ∧ t' < earlyTime p r := by
    rcases hsync.delivery with ⟨hgst, _, relay⟩ | ⟨cut, hcut, _, relay⟩
    · have hd : max t E.t_GST + E.Δ ≤ earlyTime p r := by
        rw [← max_add_add_right]
        refine max_le hdeadline ?_
        rw [hΔ]
        dsimp [earlyTime]
        linarith [p.deltaPos]
      obtain ⟨t', _, ht', j, hj⟩ := relay source hs index o t ha reader hr hmissing
        (hd.trans hsync.horizon)
      exact ⟨j, t', hj, ht'.trans_le hd⟩
    · obtain ⟨t', _, ht', j, hj⟩ := relay source hs index o t ha reader hr hmissing
        (hdeadline.trans hcut)
      exact ⟨j, t', hj, ht'.trans_le hdeadline⟩
  obtain ⟨j, t', ⟨⟨parent, hj, _⟩, _, hstored⟩, ht'⟩ := hrelay
  have hm : B ∈ (Run.stateBefore (gridCO p) rho (j + 1) reader).blocks := by
    simpa [gridCO, processed, hp, blockKnown] using hstored
  exact stored_block_stamp_before_cut p E rho hsched hj hm ht' hearly

/-- Early HEAD receipt and early target-path relay together give a resolved
honest HEAD at the gate. The caller supplies the target of the honest walk. -/
theorem synchronous_honest_head_resolved {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (i : Fin p.n) (B : Block) (hh : rho.seatOf r i ∈ rho.honest)
    (he : Run.emits (gridCO p) E rho (rho.seatOf r i)
      ⟨.seat r i, .head B⟩ (voteTime p r))
    (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) (rho.seatOf r i)).blocks)
    (hslot : B.slot ≤ r) (reader : V) (hr : reader ∈ rho.honest) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈ earlyVotes p (gateInput p rho r reader) r := by
  obtain ⟨hv, hstamp⟩ := synchronous_honest_head_at_gate p E rho hΔ r hsync i B hh he reader hr
  obtain ⟨hb, hbstamp⟩ := synchronous_block_path_at_gate p E rho hΔ r hsync
    (rho.seatOf r i) reader hh hr B hm
  simp [earlyVotes, votesAt, hv, headLabel?, resolvedBefore, headTarget?, blockKnown,
    hb, hslot, hstamp, hbstamp]

end AvailableChain.GridCO
end
