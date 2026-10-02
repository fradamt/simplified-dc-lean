module
public import AvailableChainFGSAClaims.Statements.Packages.Healing -- shake: keep (package examples)

-- Concrete regime inhabitants; production modules must not import Tests.
set_option linter.privateModule false
set_option linter.defProp false

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.HealingW

-- A concrete FG-SA run. The time-zero tick is required by tick_total.
private abbrev smokeParams : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 3, 6, by decide, 2, by decide⟩
private abbrev smokeCodec : AppCodec Nat := ⟨id, some, fun _ => rfl⟩
private abbrev smokeEnv : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
private abbrev smokeRun : V2.D.Run (Fin 1) (fgsa smokeParams smokeCodec) where
  honest := Finset.univ
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun _ _ => 0
  input := fun _ _ => 0

private def smokeSchedule : V2.D.ScheduleWellFormed smokeEnv smokeRun where
  horizon_nonneg := le_rfl
  sorted := List.pairwise_singleton _ _
  nodup := List.nodup_singleton _
  in_horizon := by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨le_rfl, le_rfl⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t ht
    have he : V2.Event.tick v t = .tick 0 0 := List.mem_singleton.mp ht
    cases he
    exact ⟨0, rfl⟩
  tick_total := by
    intro v _ t _ ht hh
    have he : t = 0 := le_antisymm hh ht
    subst t
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    exact List.mem_singleton_self _

private def smokeNoDelivery (i : Nat) (v : Fin 1) (o : (fgsa smokeParams smokeCodec).Object)
    (t : Time) : smokeRun.events[i]? ≠ some (.deliver v o t) := by
  cases i <;> simp

/-- Horizon zero with no faulty validator and GST zero. This is only a smoke test. -/
private def smoke_base : Base₂ smokeParams smokeCodec smokeEnv smokeRun where
  valid := {
    toScheduleWellFormed := smokeSchedule
    wire := by intro i v o t h; exact (smokeNoDelivery i v o t h).elim
    deps := by intro i v o t h; exact (smokeNoDelivery i v o t h).elim
    fresh := by intro i v o t h; exact (smokeNoDelivery i v o t h).elim
    unforgeable := by rintro v o t ⟨i, hi⟩; exact (smokeNoDelivery i v o t hi).elim
    carried := by rintro v o t ⟨i, hi⟩; exact (smokeNoDelivery i v o t hi).elim }
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · exact hℓ.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hℓ.elim
  cstar := by
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hℓ.elim
    · exact hℓ.elim
  noRestart := by intro i v t; cases i <;> simp
  delta := rfl

/-- A concrete finite run, with all validators honest and awake.
This checks package consistency, not completion of a healing search. -/
private def healingSet (ΔF : Time) (hF : 1 ≤ ΔF) :
    HealingSet smokeParams smokeCodec smokeEnv smokeRun 4 ΔF where
  deltaF := hF
  sync := by
    refine { broadcast_emitted := ?_, relay_accepted := ?_ }
    · rintro v _ o t _ w _ hd _
      have hdelay : 0 < fgsaDelay (p := smokeParams) smokeEnv.Δ ΔF o := by
        cases o with
        | mk a m =>
          cases m <;> simp only [fgsaDelay]
          all_goals first | exact (by decide) | exact lt_of_lt_of_le (by decide) hF
      change max t 0 + fgsaDelay smokeEnv.Δ ΔF o ≤ 0 at hd
      exact (not_le_of_gt
        (lt_add_of_le_of_pos (le_max_right t (0 : Time)) hdelay) hd).elim
    · rintro v _ i o t ⟨⟨o', hi, _⟩, _⟩
      exact (smokeNoDelivery i v o' t hi).elim
  gap := by
    intro t ht hh
    change 0 ≤ t at ht
    change t + 4 ≤ 0 at hh
    exact (not_le_of_gt (lt_add_of_le_of_pos ht (by decide)) hh).elim
  base := smoke_base
  fault := by rw [Gen.V2.Duty.faulty_def]; decide
  awake := by intros; rfl
  gapPos := le_rfl

example : 2 * smokeParams.Δ < (6 : Time) ∧ kappaF smokeParams 6 = 3 := by decide
example : kappaF smokeParams smokeEnv.Δ = 2 := by decide
example : LivenessBoundW smokeParams 6 := ⟨by decide⟩
example : LivenessBoundW smokeParams smokeEnv.Δ := ⟨by decide⟩
example : HealingSet smokeParams smokeCodec smokeEnv smokeRun 4 6 :=
  healingSet 6 (by decide)
example : HealingSet smokeParams smokeCodec smokeEnv smokeRun 4 smokeEnv.Δ :=
  healingSet smokeEnv.Δ (by decide)
example : HealingPrem smokeParams smokeCodec 4 6 smokeEnv smokeRun () :=
  ⟨healingSet 6 (by decide), ⟨by decide⟩⟩
example : HealingPrem smokeParams smokeCodec 4 smokeEnv.Δ smokeEnv smokeRun () :=
  ⟨healingSet smokeEnv.Δ (by decide), ⟨by decide⟩⟩

#print axioms healingSet

end AvailableChain.FGSA.Run.Tests.HealingW
end
