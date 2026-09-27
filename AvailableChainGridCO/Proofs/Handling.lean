module
public import AvailableChainGridCO.Proofs.Votes

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

instance carriesDecidable {n : Nat} (parent child : Wire n) :
    Decidable (carries parent child) := by
  unfold carries
  cases parent.payload <;> infer_instance

instance handlesDecidable (p : Params) {n : Nat} (st : State n)
    (parent child : Wire n) : Decidable (handles p st parent child) := by
  unfold handles
  cases parent.payload <;> infer_instance

/-- Adding stored HEADs cannot remove evidence of equivocation. -/
theorem equivocates_mono {n : Nat} (xs ys : List (Wire n)) (i : Fin n)
    (hsub : xs ⊆ ys) (he : equivocates xs i = true) : equivocates ys i = true := by
  have hlen : (seatVotes xs i).eraseDups.length ≤ (seatVotes ys i).eraseDups.length := by
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup (seatVotes xs i)),
      ← List.toFinset_card_of_nodup (eraseDups_nodup (seatVotes ys i))]
    apply Finset.card_le_card
    intro o ho
    obtain ⟨hm, hi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp (List.mem_toFinset.mp ho))
    exact List.mem_toFinset.mpr (List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hsub hm, hi⟩))
  simp only [equivocates, decide_eq_true_eq] at he ⊢
  omega

private theorem votesAt_subset {n : Nat} (a b : State n) (r : Slot)
    (hsub : a.votes ⊆ b.votes) : votesAt a r ⊆ votesAt b r := by
  intro o ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  exact List.mem_filter.mpr ⟨hsub hm, hl⟩

/-- HEAD admission never removes a stored copy. -/
theorem admitVote_votes_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.votes ⊆ (admitVote p st o).votes := by
  unfold admitVote
  split
  · dsimp only
    split
    · exact List.Subset.refl _
    · exact List.subset_append_left _ _
  · exact List.Subset.refl _

private theorem fold_votes_subset (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) : st.votes ⊆
      (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).votes := by
  induction raw generalizing st with
  | nil => exact List.Subset.refl _
  | cons row raw ih => exact (admitVote_votes_subset p st (fromHead row)).trans (ih _)

/-- In the admission window, a HEAD call leaves either that exact HEAD
or evidence from two distinct copies of its seat. A call need not accept
an additional copy once the seat has equivocated. -/
theorem admitVote_head_mem_or_equivocates (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (B : Block)
    (hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.now / (4 * p.Δ)).toNat) :
    let o : Wire n := ⟨.seat r i, .head B⟩
    o ∈ (admitVote p st o).votes ∨ equivocates (votesAt (admitVote p st o) r) i = true := by
  dsimp only
  by_cases he : equivocates (votesAt st r) i = true
  · right
    simp [admitVote, he]
  · left
    by_cases hm : (⟨.seat r i, .head B⟩ : Wire n) ∈ st.votes
    · simp [admitVote, hm]
    · simp [admitVote, not_lt.mpr hlo, not_lt.mpr hhi, hm, he]

private theorem fold_heads_mem_or_equivocates (p : Params) {n : Nat}
    (raw : List (HeadWire n)) (st : State n) (r : Slot) (i : Fin n) (B : Block)
    (hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.now / (4 * p.Δ)).toNat)
    (hraw : (⟨.seat r i, .head B⟩ : Wire n) ∈ raw.map fromHead) :
    let post := raw.foldl (fun acc row => admitVote p acc (fromHead row)) st
    (⟨.seat r i, .head B⟩ : Wire n) ∈ post.votes ∨
      equivocates (votesAt post r) i = true := by
  induction raw generalizing st with
  | nil => simp at hraw
  | cons row raw ih =>
      simp only [List.map_cons, List.mem_cons] at hraw
      rcases hraw with heq | hm
      · have h := admitVote_head_mem_or_equivocates p st r i B hlo hhi
        rw [heq] at h
        rcases h with hm | he
        · left
          rw [heq]
          exact fold_votes_subset p raw _ hm
        · exact Or.inr (equivocates_mono _ _ i
            (votesAt_subset _ _ r (fold_votes_subset p raw _)) he)
      · apply ih _ (by simpa [admitVote_now] using hlo)
          (by simpa [admitVote_now] using hhi) hm

/-- The repaired hook supplies the local receipt step for direct and
proposal-carried HEADs. The raw loop is reached only after block admission. -/
theorem handled_head_mem_or_equivocates (p : Params) {n : Nat} (st : State n)
    (parent : Wire n) (r : Slot) (i : Fin n) (B : Block)
    (hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.now / (4 * p.Δ)).toNat)
    (hh : handles p st parent ⟨.seat r i, .head B⟩) :
    (⟨.seat r i, .head B⟩ : Wire n) ∈ (process p st parent).votes ∨
      equivocates (votesAt (process p st parent) r) i = true := by
  rcases hh with heq | hh
  · subst parent
    exact admitVote_head_mem_or_equivocates p st r i B hlo hhi
  · cases hp : parent.payload with
    | head target => simp [hp] at hh
    | proposal target raw support =>
        simp only [hp] at hh
        obtain ⟨habsent, hpresent, hraw⟩ := hh
        cases ha : parent.auth with
        | seat label seat => simp [process, ha, hp, habsent] at hpresent
        | none => simp [process, ha, hp, habsent] at hpresent
        | proposer slot =>
            simp only [process, ha, hp] at hpresent ⊢
            unfold admitProposal at hpresent ⊢
            simp only [ha]
            split
            · simp_all
            · exact fold_heads_mem_or_equivocates p raw _ r i B hlo hhi hraw

/-- With no equivocation, handling a current or previous-label HEAD
leaves the exact signed object in the receiver's store. -/
theorem handled_head_mem_of_not_equivocating (p : Params) {n : Nat} (st : State n)
    (parent : Wire n) (r : Slot) (i : Fin n) (B : Block)
    (hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.now / (4 * p.Δ)).toNat)
    (hh : handles p st parent ⟨.seat r i, .head B⟩)
    (he : equivocates (votesAt (process p st parent) r) i = false) :
    (⟨.seat r i, .head B⟩ : Wire n) ∈ (process p st parent).votes := by
  rcases handled_head_mem_or_equivocates p st parent r i B hlo hhi hh with hm | he'
  · exact hm
  · simp [he] at he'

/-- A valid in-window handler call for an honest HEAD stores that HEAD,
including when the call comes from an admitted proposal. Signatures rule
out rejection by the two-copy cap. -/
theorem handled_honest_head_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (index : Nat) (reader : V)
    (r : Slot) (i : Fin p.n) (B : Block) (t : Time)
    (hh : rho.seatOf r i ∈ rho.honest)
    (hlo : ((Run.stateBefore (gridCO p) rho index reader).now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ ((Run.stateBefore (gridCO p) rho index reader).now / (4 * p.Δ)).toNat)
    (hhandle : Run.handlesAt (gridCO p) rho index reader ⟨.seat r i, .head B⟩ t) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈
      (Run.stateBefore (gridCO p) rho (index + 1) reader).votes := by
  obtain ⟨parent, hget, hhandle⟩ := hhandle
  have hpost : Run.stateBefore (gridCO p) rho (index + 1) reader =
      process p (Run.stateBefore (gridCO p) rho index reader) parent := by
    rw [stateBefore_succ_event hget]
    simp [World.step, gridCO]
  have he := honest_not_equivocating_at_event p E rho hx (index + 1) reader r i hh
  rw [hpost] at he ⊢
  exact handled_head_mem_of_not_equivocating p _ parent r i B hlo hhi hhandle he

end AvailableChain.GridCO
end
