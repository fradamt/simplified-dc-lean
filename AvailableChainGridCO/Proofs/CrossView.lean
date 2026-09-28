module
public import AvailableChainGridCO.Proofs.ReceiptRelay
public import AvailableChainGridCO.Proofs.Support

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- An accepted object reaches every honest reader before its relay cutoff,
or is already stored there after the source event. -/
theorem synchronous_accepted_object_before {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot)
    (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (index : Nat) (o : Wire p.n) (t cut : Time)
    (ha : Run.acceptsAt (gridCO p) rho index source o t)
    (hd : t + E.Δ ≤ cut) (hg : proposalTime p r + E.Δ ≤ cut)
    (hc : cut ≤ gateTime p r) :
    ∃ j e, rho.events[j]? = some e ∧ e.time < cut ∧
      processed (Run.stateBefore (gridCO p) rho (j + 1) reader) o = true := by
  have ht : t < cut := by linarith [E.Δ_pos]
  obtain ⟨parent, hi, _⟩ := ha.1
  by_cases hknown : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = true
  · exact ⟨index, .deliver source parent t, hi, ht, hknown⟩
  have hmissing : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = false :=
    Bool.eq_false_iff.mpr hknown
  have hrelay : ∃ j t', Run.acceptsAt (gridCO p) rho j reader o t' ∧ t' < cut := by
    rcases hsync.2.2.2 with ⟨hgst, _, relay⟩ | ⟨endTime, hend, _, relay⟩
    · have hbound : max t E.t_GST + E.Δ ≤ cut := by
        rw [← max_add_add_right]
        exact max_le hd (by linarith)
      obtain ⟨t', _, ht', j, hj⟩ := relay source hs index o t ha reader hr hmissing
        (hbound.trans (hc.trans hsync.2.2.1))
      exact ⟨j, t', hj, ht'.trans_le hbound⟩
    · obtain ⟨t', _, ht', j, hj⟩ := relay source hs index o t ha reader hr hmissing
        (hd.trans (hc.trans hend))
      exact ⟨j, t', hj, ht'.trans_le hd⟩
  obtain ⟨j, t', ⟨⟨parent', hj, _⟩, _, hstored⟩, ht'⟩ := hrelay
  exact ⟨j, .deliver reader parent' t', hj, ht', hstored⟩

/-- Accepted HEAD relay also gives the receiver's strict first stamp. -/
theorem synchronous_accepted_head_before {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot)
    (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (index : Nat) (o : Wire p.n) (B : Block) (t cut read : Time)
    (hb : o.payload = .head B) (ha : Run.acceptsAt (gridCO p) rho index source o t)
    (hd : t + E.Δ ≤ cut) (hg : proposalTime p r + E.Δ ≤ cut)
    (hc : cut ≤ gateTime p r) (hread : cut ≤ read) :
    o ∈ (Run.stateBeforeTime (gridCO p) rho read reader).votes ∧
      stampVote (Run.stateBeforeTime (gridCO p) rho read reader) o < cut := by
  obtain ⟨j, e, hj, ht, hm⟩ := synchronous_accepted_object_before p E rho r hsync
    source reader hs hr index o t cut ha hd hg hc
  exact stored_vote_stamp_before_cut p E rho hsync.1.toScheduleWellFormed hj
    (by simpa [processed, hb] using hm) ht hread

/-- Every early resolved HEAD at one honest reader is in every other
reader's late pool for the same synchronous label. Faulty seats are included. -/
theorem synchronous_early_vote_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ earlyVotes p (gateInput p rho r source) r) :
    o ∈ lateVotes p (gateInput p rho r reader) r := by
  obtain ⟨hraw, hres⟩ := List.mem_filter.mp ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hraw
  have hhead : ∃ B, o.payload = .head B := by
    cases ho : o.payload <;> simp_all [headLabel?]
  obtain ⟨B, hb⟩ := hhead
  have ht : stampVote (gateInput p rho r source) o < earlyTime p r := by
    simp only [resolvedBefore, headTarget?, hb, Bool.and_eq_true, decide_eq_true_eq] at hres
    exact hres.1.2
  have hpub : PublicTime E (earlyTime p r) := by
    refine ⟨4 * r + 2, ?_⟩
    simp only [earlyTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ earlyTime p r := by
    dsimp [earlyTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  change o ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source).votes at hm
  change stampVote (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source) o < _ at ht
  rw [time_input_eq_event_prefix p E rho hsync.1.toScheduleWellFormed] at hm ht
  obtain ⟨index, _, t, ha, ht⟩ := stored_head_accepted_before p E rho
    hsync.1.toScheduleWellFormed _ source o (earlyTime p r) hpub hz hm ht
  have hc : freezeTime p r ≤ gateTime p r := by
    dsimp [freezeTime, gateTime]; linarith [p.deltaPos]
  have hg : proposalTime p r + E.Δ ≤ freezeTime p r := by
    rw [hΔ]; dsimp [freezeTime]; linarith [p.deltaPos]
  obtain ⟨hm, hstamp⟩ := synchronous_accepted_head_before p E rho r hsync source reader hs hr
    index o B t (freezeTime p r) (gateTime p r) hb ha
    (by rw [hΔ]; dsimp [earlyTime, freezeTime] at *; linarith) hg hc hc
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hm, hl⟩,
    decide_eq_true (hstamp.trans_le hc)⟩

/-- A surviving early HEAD excludes any different late HEAD from its seat. -/
theorem cleanSupport_eq_of_late_same_seat (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (a b : Wire n)
    (ha : a ∈ cleanSupport p st r) (hb : b ∈ lateVotes p st r)
    (hia : headSeat? a = some i) (hib : headSeat? b = some i) : a = b := by
  obtain ⟨haearly, hclean⟩ := List.mem_filter.mp ha
  have halabel : headLabel? a = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp haearly).1).2
  have hblabel : headLabel? b = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp hb).1).2
  have hsame : sameSeat b a = true := by
    rcases a with ⟨aa, ap⟩
    rcases b with ⟨ba, bp⟩
    cases aa <;> cases ap <;> cases ba <;> cases bp <;>
      simp_all [headLabel?, headSeat?, sameSeat]
  by_contra hne
  have hany : (lateVotes p st r).any (fun u => sameSeat u a && u != a) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp [hsame, Ne.symm hne]⟩
  simp [hany] at hclean

/-- Genuine prefix support seats appear in every honest late pool. -/
theorem synchronous_support_subset_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest) (B : Block) :
    prefixSupportSeats p (gateInput p rho r source) r B ⊆
      lateSeats p (gateInput p rho r reader) r := by
  intro i hi
  obtain ⟨o, ho, hseat, _⟩ := prefixSupportSeats_witness p _ r B i hi
  exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_filterMap.mpr
    ⟨o, synchronous_early_vote_late p E rho hΔ r hsync source reader hs hr o
      (List.mem_filter.mp ho).1, hseat⟩))

/-- Conflicting genuine prefixes at different readers have disjoint
surviving support sets. Relay makes a shared conflicting seat fail the
source reader's late equivocation test. -/
theorem synchronous_support_disjoint {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C : Block) (hc : Block.compatible B C = false) :
    Disjoint (prefixSupportSeats p (gateInput p rho r source) r B)
      (prefixSupportSeats p (gateInput p rho r reader) r C) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨o, ho, hseat, target, ht, hp⟩ := prefixSupportSeats_witness p _ r B i hi
  obtain ⟨q, hq, hseat', target', ht', hp'⟩ := prefixSupportSeats_witness p _ r C i hj
  have hlate := synchronous_early_vote_late p E rho hΔ r hsync reader source hr hs q
    (List.mem_filter.mp hq).1
  have he := cleanSupport_eq_of_late_same_seat p _ r i o q ho hlate hseat hseat'
  subst q
  have he' := Option.some.inj (ht.symm.trans ht')
  subst target'
  have hcompat := ancestors_compatible B C target hp hp'
  change Block.compatible B C = true at hcompat
  rw [hc] at hcompat
  contradiction

/-- The engine and accepted relay establish cross-view seat alignment. -/
theorem sameLabelSeatAlignment_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r) : SameLabelSeatAlignment p rho r := by
  intro u hu v hv B C _ _
  refine ⟨prefixSupportSeats p (gateInput p rho r u) r B,
    prefixSupportSeats p (gateInput p rho r v) r C,
    (prefixSupport_eq_card p _ r B).symm, (prefixSupport_eq_card p _ r C).symm, ?_, ?_, ?_⟩
  · exact Finset.union_subset (prefixSupportSeats_subset_late p _ r B)
      (synchronous_support_subset_late p E rho hΔ r hsync v u hv hu C)
  · exact Finset.union_subset (synchronous_support_subset_late p E rho hΔ r hsync u v hu hv B)
      (prefixSupportSeats_subset_late p _ r C)
  · exact synchronous_support_disjoint p E rho hΔ r hsync u v hu hv B C

/-- Same-label compatibility follows from the engine, the label's relay
premises, and matching time units. -/
theorem sameLabel_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, SynchronousLabel p E rho r → ∀ u ∈ rho.honest, ∀ v ∈ rho.honest,
      ∀ B C, confirmation p (gateInput p rho r u) r = some B →
        confirmation p (gateInput p rho r v) r = some C →
        Block.compatible B C = true := by
  intro r hsync
  exact same_label_from_alignment p rho r (sameLabelSeatAlignment_from_engine p E rho hΔ r hsync)

end AvailableChain.GridCO
end
