module
public import AvailableChainEngineV2.Conditions.Schedule
public import AvailableChainEngineV2.Conditions.Committees
public import AvailableChainEngineV2.Tests.Engine

@[expose] public section

/-! Tests of the conditions without blocks (plan 2a, Task 2): a restart of
another node does not break `restartFree`; a `Linked` family is `CStar`;
a one-seat family is `SingleSeat`. -/

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-- Validator 1 restarts at time 0, then validator 0 ticks at time 0. -/
def rhoR : Run (Fin 2) specA where
  honest := ∅
  horizon := 0
  events := [.restart 1 0, .tick 0 0]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

-- The restart of validator 1 does not count for validator 0.
example : restartFree rhoR 0 0 1 := by
  by_contra h
  obtain ⟨t, ht⟩ := (not_restartFree_succ_iff rhoR 0 0).mp h
  simp [rhoR] at ht
-- It counts for validator 1 on `[0, 1)`, but not on `[1, 2)`.
example : ¬ restartFree rhoR 1 0 1 := (not_restartFree_succ_iff rhoR 1 0).mpr ⟨0, rfl⟩
example : restartFree rhoR 1 1 2 := by
  by_contra h
  obtain ⟨t, ht⟩ := (not_restartFree_succ_iff rhoR 1 1).mp h
  simp [rhoR] at ht
example : ¬ NoRestart rhoR := fun h => h 0 1 0 rfl

/-- `specM`: label `true` has two seats, label `false` one. Seat `i` of any
label is validator `i mod 2`. -/
def rhoL : Run (Fin 2) specM where
  honest := ∅
  horizon := 0
  events := []
  seatOf := fun _ i => ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  input := fun _ _ => 0

/-- The family `{true}` is linked through the identity bijection. -/
theorem rhoL_linked : Linked (fun ℓ => ℓ = true) rhoL := by
  refine ⟨2, Equiv.refl _, fun ℓ hℓ => ?_⟩
  subst hℓ
  exact ⟨rfl, fun i => Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩

example : CStar (fun ℓ => ℓ = true) rhoL := rhoL_linked.toCStar
example : SingleSeat (P := specM) (fun ℓ => ℓ = false) := by
  rintro ℓ rfl; rfl

end AvailableChain.V2.Tests

end
