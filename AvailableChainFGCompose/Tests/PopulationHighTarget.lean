module
import all AvailableChainFGCompose.Tests.PopulationHighTargetFixture

set_option linter.privateModule false
noncomputable section
public section
namespace AvailableChain.FGCompose.Tests.PopulationHighTarget
open AvailableChain.SimplexFG AvailableChain.KitFG

private theorem mixed_actions_premises_sat :
    FGHonestSeats reads run = {0} ∧ ({0} : Finset (Fin 1)).Nonempty ∧
    electorate.IsQuorum {0} ∧ high core obs point.reset .genesis ∧
    (∀ r, r ≤ 1 → (∀ x ∈ run.honest,
      actionSourceFG core (env Nat) run timing x r = some (some .genesis)) ∧
      (env Nat).t_GST ≤ timing.action r ∧ timing.action r + 2 ≤ run.horizon) ∧
    (∀ x ∈ run.honest, ∀ t, (env Nat).t_GST ≤ t → t ≤ run.horizon →
      (env Nat).awake x t = true) ∧
    (∀ r, reads.enabled (timing.action r) = true) := by
  refine ⟨?_, ⟨0, by simp⟩, by change (1 : Nat) ≤ 1; decide,
    by change (1 : Nat) ≤ 1; decide, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder]
  · intro r hr
    interval_cases r <;> refine ⟨?_, by decide, by decide⟩
    all_goals
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> rfl
  · intro x _ t _ _; rfl
  · intro r
    apply decide_eq_true
    change (4 * (r * 2 : Nat) + 6 : Int) % 8 = 6
    omega

#print axioms mixed_actions_premises_sat

end AvailableChain.FGCompose.Tests.PopulationHighTarget
end
