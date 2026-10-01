module
public import AvailableChainFGSAProofs.Proofs.Shared.KeepExact -- shake: keep (pivot axiom audit)

set_option linter.privateModule false

/-! R-F1b rounds 1 and 2. These private tests use the exact quantified
`hancestry` binder of `exactHead_of_pivot_ancestry` and its Gen path kernel.
The empty target fails membership; the score tie fails the root conjunct.
No store invariant, row, or extra axiom is used. -/
namespace AvailableChain.FGSA.Run.Tests.KeepExact
open AvailableChain.Gen.Pure

-- All walk premises after the proposed start-only generalization hold,
-- but neither target coverage nor exactness holds.
theorem upperStartEmptyTreeCounterexample (P : Block)
    (hstrict : Block.Prec .genesis P) (score score' : Block → Nat)
    (elig elig' : Block → Bool) :
    (Block.Preceq .genesis P ∧ Block.Preceq P P) ∧
    Block.Preceq .genesis .genesis ∧
    DominatedSuffix P .genesis [] score elig ∧
    DominatedSuffix .genesis .genesis [] score' elig' ∧
    Block.Preceq P (GridCO.ghost P [] score elig) ∧
    SuffixPersists .genesis P [] [] score elig elig' ∧
    SuffixReflects .genesis P [] [] elig elig' ∧
    SuffixScoresAgree .genesis P [] score score' elig' ∧
    P = P ∧ AnchorClosed .genesis [] ∧ NoEligibleChild [] elig' P ∧
    ¬ Block.Preceq P (GridCO.ghost .genesis [] score' elig') ∧
    GridCO.ghost .genesis [] score' elig' ≠ P := by
  have hne : P ≠ .genesis := by
    intro he
    subst P
    simp [Block.Prec, Block.prec] at hstrict
  have hnot : ¬ Block.Preceq P .genesis := by
    intro h
    have he : P = .genesis := of_decide_eq_true h
    exact hne he
  have hd (A : Block) : DominatedSuffix A .genesis [] score elig := by
    intro C hAC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec, Block.preceq] at hAC
  refine ⟨⟨?_, block_preceq_refl _⟩, block_preceq_refl _, hd P, ?_,
    block_preceq_refl _, ?_, ?_, ?_, rfl, ?_, ?_, hnot, Ne.symm hne⟩
  · exact block_genesis_preceq P
  · intro C hAC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec] at hAC
  · intro X C _ _ hs _
    cases hs
  · intro X C _ _ hm
    cases hm
  · intro X C _ _ hm
    cases hm
  · intro B hm
    cases hm
  · intro C hm
    cases hm

#print axioms upperStartEmptyTreeCounterexample

-- The proposed ancestry premise excludes the round-1 empty target.
-- Membership, before eligibility or maximality, is already impossible.
theorem emptyTargetAncestryPremiseFails (P : Block)
    (hstrict : Block.Prec .genesis P) (score : Block → Nat) (elig : Block → Bool) :
    ¬ (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧ C ∈ ([] : List Block) ∧
        elig C = true ∧ ∀ D ∈ ([] : List Block), D.parent? = some X →
          elig D = true → score D ≤ score C ∧
          (score D = score C → D.root ≤ C.root)) := by
  intro hancestry
  obtain ⟨C, _, _, hmem, _, _⟩ := hancestry .genesis (block_preceq_refl _) hstrict
  cases hmem

#print axioms emptyTargetAncestryPremiseFails

-- P and its rival have equal score. The rival has the greater root.
private def P : Block := .node .genesis 1 0
private def D : Block := .node .genesis 1 1

example : P.root < D.root := by decide
example : GridCO.ghost .genesis [P, D] (fun _ => 0) (fun _ => true) = D := by decide

-- This is the literal ancestry premise: target membership, eligibility,
-- and maximal score. It does not specify which child wins a score tie.
theorem maximalScoreAncestryCounterexample :
    (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ [P, D] ∧ (fun _ : Block => true) C = true ∧
        ∀ B ∈ [P, D], B.parent? = some X →
          (fun _ : Block => true) B = true → (0 : Nat) ≤ 0) ∧
    ¬ Block.Preceq P (GridCO.ghost .genesis [P, D] (fun _ => 0) (fun _ => true)) ∧
    GridCO.ghost .genesis [P, D] (fun _ => 0) (fun _ => true) ≠ P := by
  refine ⟨?_, by decide, by decide⟩
  intro X _ hXP
  have hX : X = .genesis := by
    by_cases he : X = P
    · subst X; simp [Block.Prec, Block.prec] at hXP
    · have hp : Block.preceq X P = true := (Bool.and_eq_true_iff.mp hXP).2
      have hh : X = P ∨ X = .genesis := by
        simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hp)
      exact hh.resolve_left he
  subst X
  exact ⟨P, rfl, block_preceq_refl _, by simp, rfl, by intros; omega⟩

#print axioms maximalScoreAncestryCounterexample

private theorem belowP (X : Block) (hXP : Block.Prec X P) : X = .genesis := by
  by_cases he : X = P
  · subst X; simp [Block.Prec, Block.prec] at hXP
  · have hp : Block.preceq X P = true := (Bool.and_eq_true_iff.mp hXP).2
    have hh : X = P ∨ X = .genesis := by
      simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hp)
    exact hh.resolve_left he

-- Both start disjunctions and all old walk premises still hold.
-- T = genesis, source start = P, target start = T, Q = P.
-- The target includes genesis so AnchorClosed also holds.
theorem maximalScoreAllWalkPremisesCounterexample :
    (Block.Preceq .genesis P ∧ Block.Preceq P P) ∧
    Block.Preceq .genesis .genesis ∧ Block.Preceq .genesis P ∧
    DominatedSuffix P .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true) ∧
    DominatedSuffix .genesis .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true) ∧
    Block.Preceq P (GridCO.ghost P [.genesis, P, D] (fun _ => 0) (fun _ => true)) ∧
    SuffixPersists .genesis P [.genesis, P, D] [.genesis, P, D]
      (fun _ => 0) (fun _ => true) (fun _ => true) ∧
    SuffixReflects .genesis P [.genesis, P, D] [.genesis, P, D]
      (fun _ => true) (fun _ => true) ∧
    SuffixScoresAgree .genesis P [.genesis, P, D] (fun _ => 0) (fun _ => 0) (fun _ => true) ∧
    (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ [.genesis, P, D] ∧ (fun _ : Block => true) C = true ∧
        ∀ B ∈ [.genesis, P, D], B.parent? = some X →
          (fun _ : Block => true) B = true → (0 : Nat) ≤ 0) ∧
    P = P ∧ AnchorClosed .genesis [.genesis, P, D] ∧
    NoEligibleChild [.genesis, P, D] (fun _ => true) P ∧
    ¬ Block.Preceq P (GridCO.ghost .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true)) ∧
    GridCO.ghost .genesis [.genesis, P, D] (fun _ => 0) (fun _ => true) ≠ P := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, ?_, ?_, by decide,
    ?_, ?_, ?_, ?_, rfl, ?_, ?_, by decide, by decide⟩
  · intro C hPC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec, Block.preceq, P] at hPC
  · intro C hTC hCT
    have he : C = .genesis := of_decide_eq_true hCT
    subst C
    simp [Block.Prec, Block.prec] at hTC
  · intro X C _ hXP hs _
    have hX := belowP X hXP
    subst X
    have hsD : GridCO.ghostStep [.genesis, P, D] (fun _ => 0) (fun _ => true)
        .genesis = some D := by decide
    rw [hsD] at hs
    have he := Option.some.inj hs
    subst C
    exact ⟨by simp, rfl⟩
  · intro X C _ _ hm _ hel
    exact ⟨hm, hel⟩
  · rw [SuffixScoresAgree_def]; intros; rfl
  · intro X _ hXP
    have hX := belowP X hXP
    subst X
    exact ⟨P, rfl, block_preceq_refl _, by simp, rfl, by intros; omega⟩
  · intro B hB _ C _ hCB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB ⊢
    rcases hB with rfl | rfl | rfl
    · exact Or.inl (of_decide_eq_true hCB)
    · have hh : C = P ∨ C = .genesis := by
        simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hCB)
      rcases hh with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · have hh : C = D ∨ C = .genesis := by
        simpa only [D, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hCB)
      rcases hh with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
  · intro C hC hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl <;> cases hp

#print axioms maximalScoreAllWalkPremisesCounterexample

-- The full ancestry premise in the new theorem excludes the round-2 witness.
-- All numerical scores are equal. D wins because its root is greater.
theorem rootTieAncestryPremiseFails :
    ¬ (∀ X, Block.Preceq .genesis X → Block.Prec X P →
      ∃ C, C.parent? = some X ∧ Block.Preceq C P ∧
        C ∈ [.genesis, P, D] ∧ (fun _ : Block => true) C = true ∧
        ∀ B ∈ [.genesis, P, D], B.parent? = some X →
          (fun _ : Block => true) B = true →
          (0 : Nat) ≤ 0 ∧ ((0 : Nat) = 0 → B.root ≤ C.root)) := by
  intro hancestry
  obtain ⟨C, hp, hCP, _, _, hbest⟩ :=
    hancestry .genesis (block_preceq_refl _) (by decide)
  have hC : C = P := by
    have hh : C = P ∨ C = .genesis := by
      simpa only [P, Block.preceq, decide_eq_true_eq] using (Bool.or_eq_true_iff.mp hCP)
    rcases hh with he | rfl
    · exact he
    · cases hp
  subst C
  have hbad := (hbest D (by simp) rfl rfl).2 rfl
  exact (by decide : ¬ D.root ≤ P.root) hbad

#print axioms rootTieAncestryPremiseFails
#print axioms AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry

end AvailableChain.FGSA.Run.Tests.KeepExact
