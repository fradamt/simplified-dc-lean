module
public import AvailableChainSAPC.Proofs.EffectiveScores
public import AvailableChainGridCO.Proofs.ProposalViews

@[expose] public section
namespace AvailableChain.SAPC

/-- Relay can replace a raw key by two-target evidence for its seat.
Such replacement preserves the participant set. -/
theorem seats_eq_of_mem_or_equivocates {n : Nat} (xs ys : List (GridCO.Wire n))
    (hsub : xs ⊆ ys)
    (hback : ∀ o ∈ ys, ∀ i, GridCO.headSeat? o = some i →
      o ∈ xs ∨ GridCO.equivocates xs i = true) :
    (GridCO.seats n xs).toFinset = (GridCO.seats n ys).toFinset := by
  ext i
  simp only [GridCO.seats, List.mem_toFinset, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, hi⟩
    exact ⟨o, hsub ho, hi⟩
  · rintro ⟨o, ho, hi⟩
    rcases hback o ho i hi with hm | he
    · exact ⟨o, hm, hi⟩
    · have hp : 0 < (GridCO.seatVotes xs i).eraseDups.length := by
        have := of_decide_eq_true he
        omega
      obtain ⟨key, hk⟩ := List.length_pos_iff_exists_mem.mp hp
      obtain ⟨hm, hs⟩ := List.mem_filter.mp (List.mem_eraseDups.mp hk)
      exact ⟨key, hm, by simpa using hs⟩

/-- Extra raw copies from a seat already known to equivocate cannot
change the equivocation test. -/
theorem equivocates_eq_of_mem_or_equivocates {n : Nat}
    (xs ys : List (GridCO.Wire n)) (hsub : xs ⊆ ys)
    (hback : ∀ o ∈ ys, ∀ i, GridCO.headSeat? o = some i →
      o ∈ xs ∨ GridCO.equivocates xs i = true) (i : Fin n) :
    GridCO.equivocates xs i = GridCO.equivocates ys i := by
  cases he : GridCO.equivocates xs i with
  | true => exact (GridCO.equivocates_mono xs ys i hsub he).symm
  | false =>
    symm
    apply GridCO.equivocates_false_of_unique
    intro a ha b hb
    have back (o : GridCO.Wire n) (ho : o ∈ GridCO.seatVotes ys i) :
        o ∈ GridCO.seatVotes xs i := by
      obtain ⟨hm, hi⟩ := List.mem_filter.mp ho
      exact List.mem_filter.mpr ⟨(hback o hm i (by simpa using hi)).resolve_right
        (by simp [he]), hi⟩
    exact non_equivocating_unique xs i he a b (back a ha) (back b hb)

theorem voterCount_eq_of_mem_or_equivocates {n : Nat}
    (xs ys : List (GridCO.Wire n)) (hsub : xs ⊆ ys)
    (hback : ∀ o ∈ ys, ∀ i, GridCO.headSeat? o = some i →
      o ∈ xs ∨ GridCO.equivocates xs i = true) :
    GridCO.voterCount xs = GridCO.voterCount ys := by
  unfold GridCO.voterCount
  rw [← List.toFinset_card_of_nodup (show (GridCO.seats n xs).Nodup from List.nodup_dedup _),
    ← List.toFinset_card_of_nodup (show (GridCO.seats n ys).Nodup from List.nodup_dedup _),
    seats_eq_of_mem_or_equivocates xs ys hsub hback]

/-- Common resolved support is needed only for non-equivocating seats.
This covers the different two-copy caches allowed by SA-PC relay. -/
theorem goldfishScore_eq_of_mem_or_equivocates {n : Nat}
    (tree₁ tree₂ : List Block) (raw₁ raw₂ support₁ support₂ : List (GridCO.Wire n))
    (hraw : raw₁ ⊆ raw₂)
    (hback : ∀ o ∈ raw₂, ∀ i, GridCO.headSeat? o = some i →
      o ∈ raw₁ ∨ GridCO.equivocates raw₁ i = true)
    (hsupport : support₁ ⊆ support₂)
    (hsback : ∀ o ∈ support₂, ∀ i, GridCO.headSeat? o = some i →
      o ∈ support₁ ∨ GridCO.equivocates raw₁ i = true)
    (htree : ∀ o ∈ support₁, ∀ target, GridCO.headTarget? o = some target →
      (target ∈ tree₁ ↔ target ∈ tree₂)) (b : Block) :
    GridCO.goldfishScore tree₁ raw₁ support₁ b =
      GridCO.goldfishScore tree₂ raw₂ support₂ b := by
  rw [GridCO.goldfishScore_eq_card, GridCO.goldfishScore_eq_card]
  congr 1
  ext i
  have he := equivocates_eq_of_mem_or_equivocates raw₁ raw₂ hraw hback i
  simp only [GridCO.scoreSeats, Finset.mem_filter,
    seats_eq_of_mem_or_equivocates raw₁ raw₂ hraw hback, ← he]
  apply and_congr Iff.rfl
  cases hi : GridCO.equivocates raw₁ i with
  | true => simp
  | false =>
    simp only [Bool.false_or, List.any_eq_true]
    constructor
    · rintro ⟨o, ho, ht⟩
      obtain ⟨hm, hs⟩ := List.mem_filter.mp ho
      refine ⟨o, List.mem_filter.mpr ⟨hsupport hm, hs⟩, ?_⟩
      cases hh : GridCO.headTarget? o with
      | none => simp [hh] at ht
      | some target => simpa only [hh, htree o hm target hh] using ht
    · rintro ⟨o, ho, ht⟩
      obtain ⟨hm, hs⟩ := List.mem_filter.mp ho
      have hm' := (hsback o hm i (by simpa using hs)).resolve_right (by simp [hi])
      refine ⟨o, List.mem_filter.mpr ⟨hm', hs⟩, ?_⟩
      cases hh : GridCO.headTarget? o with
      | none => simp [hh] at ht
      | some target => simpa only [hh, htree o hm' target hh] using ht

end AvailableChain.SAPC
end
