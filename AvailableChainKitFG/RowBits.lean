module
public import AvailableChainKitFG.RowBitsDef
public import AvailableChainKitFG.Certificates

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem process_row_covered (kind : ChainBit) (σ : ChainState V)
    (a : Row V) (i : V)
    (hi : i ∈ chainBits kind σ ∨ a.signer = i ∧ rowMatchesBit kind σ a) :
    i ∈ chainBits kind (process_row σ a) := by
  cases kind <;> simp only [chainBits_def, rowMatchesBit_def] at hi ⊢
  all_goals
    first | rw [process_row_target] | rw [process_row_progress] | rw [process_row_finalize]
    split_ifs with hm
    · rcases hi with hi | ⟨rfl, _⟩
      · exact Finset.mem_insert_of_mem hi
      · exact Finset.mem_insert_self _ _
    · rcases hi with hi | ⟨_, h⟩
      · exact hi
      · exact False.elim (hm (by
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using h))

private theorem row_matches_process (kind : ChainBit) (σ : ChainState V) (a b : Row V) :
    rowMatchesBit kind (process_row σ a) b = rowMatchesBit kind σ b := by
  obtain ⟨_, _, hh, hT, hJ, hj, _, hF⟩ := process_row_fields σ a
  cases kind <;> simp only [rowMatchesBit_def, hh, hT, hJ, hj, hF]

/-- Existing bits and matching row occurrences are sufficient for fold coverage.
DC: ChainState/Chain.lean:125,136,149; same: carrier adapter of the step cores.
INTENTIONAL shared fold helper for G20 and the GEN-FIRST Counts.lean:25 consumer.
This implication does not select a row from a bit. -/
theorem bit_fold_covered (kind : ChainBit) (rows : List (Row V))
    (σ : ChainState V) (i : V)
    (hi : i ∈ chainBits kind σ ∨
      ∃ a ∈ rows, a.signer = i ∧ rowMatchesBit kind σ a) :
    i ∈ chainBits kind (rows.foldl process_row σ) := by
  induction rows generalizing σ with
  | nil =>
      rcases hi with hi | ⟨a, ha, _⟩
      · exact hi
      · cases ha
  | cons a rows ih =>
      apply ih
      rcases hi with hi | ⟨b, hb, hs, hm⟩
      · exact Or.inl (process_row_covered kind σ a i (Or.inl hi))
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl (process_row_covered kind σ b i (Or.inr ⟨hs, hm⟩))
        · right
          exact ⟨b, hb, hs, (row_matches_process kind σ a b).symm ▸ hm⟩

-- Only the numerical part of each key is needed to exclude a reset.
private def bitHeight (kind : ChainBit) (σ : ChainState V) : Height :=
  match kind with
  | .target | .progress => σ.h
  | .finality => σ.h_j

omit [DecidableEq V] [RowCodec V] in
private theorem bitHeight_def (kind : ChainBit) (σ : ChainState V) :
    bitHeight kind σ =
      (match kind with | .target | .progress => σ.h | .finality => σ.h_j) := rfl

variable [Fintype V]

private theorem node_h_j_mono (E : Electorate V) (cfg : FGConfig)
    (p : FGBlock V) (s : Slot) (x : Nat) (rows : List (Row V)) :
    (derive E cfg p).h_j ≤ (derive E cfg (.node p s x rows)).h_j := by
  obtain ⟨_, hh, _, _, hj, _, _⟩ :=
    foldRows_fields (derive E cfg p) (.node p s x rows) rows
  rw [derive_node]
  rcases justification_pair_cases E cfg
      (foldRows (derive E cfg p) (.node p s x rows) rows) with h | h
  · rw [h.2, hj]
  · rw [h.2.1, hh]
    exact Nat.le_of_lt (justified_below_height E cfg p)

private theorem h_j_mono (E : Electorate V) (cfg : FGConfig) {B W : FGBlock V}
    (hBW : FGBlock.Preceq B W) : (derive E cfg B).h_j ≤ (derive E cfg W).h_j := by
  induction W with
  | genesis =>
      obtain rfl := preceq_genesis.mp hBW
      exact le_refl _
  | node p s x rows ih =>
      by_cases heq : B = .node p s x rows
      · subst B
        exact le_refl _
      · exact (ih (preceq_parent_of_preceq_node hBW heq)).trans
          (node_h_j_mono E cfg p s x rows)

private theorem bit_height_mono (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) {B W : FGBlock V} (hBW : FGBlock.Preceq B W) :
    bitHeight kind (derive E cfg B) ≤ bitHeight kind (derive E cfg W) := by
  cases kind with
  | target | progress => exact h_mono E cfg hBW
  | finality => exact h_j_mono E cfg hBW

omit [Fintype V] in
private theorem bit_height_fold (kind : ChainBit) (σ : ChainState V)
    (B : FGBlock V) (rows : List (Row V)) :
    bitHeight kind (foldRows σ B rows) = bitHeight kind σ := by
  have hf := foldRows_fields σ B rows
  cases kind with
  | target | progress => exact hf.2.1
  | finality => exact hf.2.2.2.2.1

-- A justification write raises h_j strictly because h_j < h.
-- The finality branch changes F and h_F, but keeps every bit set.
omit [DecidableEq V] [RowCodec V] in
private theorem bits_height_events (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) (σ : ChainState V) (horder : σ.h_j < σ.h)
    (hk : bitHeight kind (process_height_events E cfg σ) = bitHeight kind σ) :
    chainBits kind (process_height_events E cfg σ) = chainBits kind σ := by
  cases kind <;> rw [process_height_events_eq] at hk ⊢ <;>
    split_ifs at hk ⊢ <;>
    simp only [bitHeight_def, chainBits_def, advance_height, afterFin_h, afterFin_h_j,
      afterFin_target_participation, afterFin_progress, afterFin_finalize] at hk ⊢ <;>
    (first | rfl | (simp only [Height] at *; omega))

private theorem node_bits_eq_fold (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) (p : FGBlock V) (s : Slot) (x : Nat) (rows : List (Row V))
    (hk : bitHeight kind (derive E cfg p) =
      bitHeight kind (derive E cfg (.node p s x rows))) :
    chainBits kind (derive E cfg (.node p s x rows)) =
      chainBits kind (foldRows (derive E cfg p) (.node p s x rows) rows) := by
  have hf := foldRows_fields (derive E cfg p) (.node p s x rows) rows
  rw [derive_node]
  apply bits_height_events
  · rw [hf.2.2.2.2.1, hf.2.1]
    exact justified_below_height E cfg p
  · rw [bit_height_fold, ← derive_node, hk]

private theorem node_bits_persist (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) (p : FGBlock V) (s : Slot) (x : Nat) (rows : List (Row V))
    (hk : bitHeight kind (derive E cfg p) =
      bitHeight kind (derive E cfg (.node p s x rows))) :
    chainBits kind (derive E cfg p) ⊆ chainBits kind (derive E cfg (.node p s x rows)) := by
  rw [node_bits_eq_fold E cfg kind p s x rows hk]
  intro i hi
  have hc := bit_fold_covered kind rows
    { derive E cfg p with s := (FGBlock.node p s x rows).slot } i (Or.inl hi)
  cases kind <;> exact hc

private theorem bits_persist_height (E : Electorate V) (cfg : FGConfig)
    (kind : ChainBit) {B W : FGBlock V} (hBW : FGBlock.Preceq B W)
    (hk : bitHeight kind (derive E cfg B) = bitHeight kind (derive E cfg W)) :
    chainBits kind (derive E cfg B) ⊆ chainBits kind (derive E cfg W) := by
  induction W with
  | genesis =>
      obtain rfl := preceq_genesis.mp hBW
      exact Finset.Subset.refl _
  | node p s x rows ih =>
      by_cases heq : B = .node p s x rows
      · subst B
        exact Finset.Subset.refl _
      · have hBp := preceq_parent_of_preceq_node hBW heq
        have hlow := bit_height_mono E cfg kind hBp
        have hhigh := bit_height_mono E cfg kind (preceq_parent_node p s x rows)
        have hpar : bitHeight kind (derive E cfg p) =
            bitHeight kind (derive E cfg (.node p s x rows)) := by
          simp only [Height] at *
          omega
        exact (ih hBp (hk.trans hpar.symm)).trans
          (node_bits_persist E cfg kind p s x rows hpar)

/-- Equal endpoint keys exclude every bit reset between the two chain points.
DC: none; derived carrier lemma; witnesses MatchingProgress.lean:147,
FinalityCertificates.lean:133. GLY r3.19 G20. -/
theorem bit_persist : BitPersistStatement := by
  intro V _ _ _ E cfg kind B W hBW hk
  apply bits_persist_height E cfg kind hBW
  cases kind <;> exact hk.1

/-- A matching row sets its signer bit in the carrier fold; equal endpoint
keys preserve it through the height events and the rest of the chain.
DC: none; derived carrier lemma; witnesses MatchingProgress.lean:147,
FinalityCertificates.lean:133. GLY r3.19 G20. -/
theorem bit_from_row : BitFromRowStatement := by
  intro V _ _ _ E cfg kind parent W slot body rows a ha hCW hm hs
  have hk : bitHeight kind (derive E cfg parent) = bitHeight kind (derive E cfg W) := by
    cases kind <;> exact hs.1
  have hlow := bit_height_mono E cfg kind (preceq_parent_node parent slot body rows)
  have hhigh := bit_height_mono E cfg kind hCW
  have hpc : bitHeight kind (derive E cfg parent) =
      bitHeight kind (derive E cfg (.node parent slot body rows)) := by
        simp only [Height] at *
        omega
  apply bits_persist_height E cfg kind hCW (hpc.symm.trans hk)
  rw [node_bits_eq_fold E cfg kind parent slot body rows hpc]
  have hm' : rowMatchesBit kind
      { derive E cfg parent with s := (FGBlock.node parent slot body rows).slot } a := by
    cases kind <;> exact hm
  have hc := bit_fold_covered kind rows
    { derive E cfg parent with s := (FGBlock.node parent slot body rows).slot } a.signer
    (Or.inr ⟨a, ha, rfl, hm'⟩)
  cases kind <;> exact hc

end AvailableChain.KitFG
end
