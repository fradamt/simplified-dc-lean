module
import all AvailableChainFGCompose.Tests.P0d5db
import all tests.POP6bMixedFixture

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bMixed
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db

private theorem core_premises_sat : FGCoreLaws core ∧ FGTreeKeepLaws core ∧
    (∀ i j, i ≤ j → ∀ x, TFAt core env run i x ⊆ TFAt core env run j x) ∧
    FGRunOrderLaws env run core ∧
    (∀ a b : Nat, a ≤ b → FGBlock.Preceq (chain a) (chain b)) ∧
    (∀ a b : Nat, a ≤ b → stored a ⊆ stored b) := by
  have ancestry {a b : Nat} (h : a ≤ b) : FGBlock.Preceq (chain a) (chain b) := by
    induction b with
    | zero =>
      have ha : a = 0 := by omega
      subst a
      exact preceq_refl _
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | h
      · exact preceq_refl _
      · exact preceq_node_of_preceq _ _ _ _ (ih (by omega))
  have stores {a b : Nat} (h : a ≤ b) : stored a ⊆ stored b := by
    intro X hX
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hX)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨s, List.mem_range.mpr (by
        have hs' := Nat.le_of_lt_succ (List.mem_range.mp hs)
        exact Nat.lt_succ_of_le (hs'.trans (min_le_min h le_rfl))), rfl⟩)
  have laws : FGCoreLaws core := by
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_,
      fun _ _ => List.prefix_rfl, fun _ _ => List.prefix_rfl, fun _ _ => rfl, ?_, v5erase_inj⟩
    · intro st o
      change stored st ⊆ stored (match o.payload with
        | .inr X => max st X.slot | .inl _ => st)
      cases hp : o.payload with
      | inl a => exact Finset.Subset.refl _
      | inr X => exact stores (Nat.le_max_left st X.slot)
    · intro st C hC
      have hC' : chain (min st 64) = C := Option.some.inj hC
      rw [← hC']
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨min st 64, List.mem_range.mpr (by omega), rfl⟩)
  have tree : FGTreeKeepLaws core := ⟨fun _ _ => Finset.Subset.refl _⟩
  refine ⟨laws, tree, fun _ _ hij x => tf_cumulative_all core env run laws tree hij x,
    ?_, fun _ _ h => ancestry h, fun _ _ h => stores h⟩
  constructor
  intro i j x _ hij
  have hi := geometry_premises_sat.2.2 (run.stateBefore env i x)
  have hj := geometry_premises_sat.2.2 (run.stateBefore env j x)
  have hkeep := tf_cumulative_all core env run laws tree hij x
  refine ⟨preceq_refl _, le_rfl, ?_⟩
  rw [hi.hmax, hj.hmax]
  exact max_le_max (Finset.sup_mono hkeep) le_rfl

#print axioms core_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end
