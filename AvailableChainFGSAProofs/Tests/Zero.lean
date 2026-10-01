module
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean -- shake: keep (test examples use the Export names)

-- Test fixtures and examples stay private.
set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.Zero

private abbrev p4 : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

private abbrev rho0 : V2.D.Run (Fin 4) (fgsa p4 unitCodec) where
  honest := {0}
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

private abbrev env0 : Generic.Env (Fin 4) :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private theorem schedule0 : V2.D.ScheduleWellFormed env0 rho0 where
  horizon_nonneg := le_rfl
  sorted := List.pairwise_singleton _ _
  nodup := List.nodup_singleton _
  in_horizon := by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨le_rfl, le_rfl⟩
  honest_only := by
    intro e he
    have heq := List.mem_singleton.mp he
    subst e
    exact Finset.mem_singleton_self _
  tick_public := by
    intro v t ht
    have he : V2.Event.tick v t = .tick 0 0 := List.mem_singleton.mp ht
    cases he
    exact ⟨0, rfl⟩
  tick_total := by
    intro v hv t _ ht hh
    have he : t = 0 := le_antisymm hh ht
    subst t
    have hv : v = 0 := Finset.mem_singleton.mp hv
    subst v
    exact List.mem_singleton_self _

private theorem noDelivery0 (i : Nat) (v : Fin 4) (o : (fgsa p4 unitCodec).Object)
    (t : Time) : rho0.events[i]? ≠ some (.deliver v o t) := by
  cases i <;> simp

-- Horizon zero with three faulty validators; no receipt is scheduled.
private theorem base0 : Base₂ p4 unitCodec env0 rho0 where
  valid := {
    toScheduleWellFormed := schedule0
    wire := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    deps := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    fresh := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    unforgeable := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim
    carried := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim }
  linked := by
    refine ⟨4, Equiv.refl _, ?_⟩
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · exact hℓ.elim
    · exact ⟨rfl, fun _ => rfl⟩
    · exact hℓ.elim
  cstar := by
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · change Function.Bijective (fun i : Fin 4 => i)
      exact Function.bijective_id
    · exact hℓ.elim
    · exact hℓ.elim
  noRestart := by intro i v t; cases i <;> simp
  delta := rfl

private theorem healthy0 : V2.D.HealthyPrefixDelivery env0 rho0 0 where
  broadcast := by
    rintro v _ o t ⟨i, hi, _⟩ w _ hd _
    have ht : 0 ≤ t := (schedule0.in_horizon _ (List.mem_of_getElem? hi)).1
    change t + 1 ≤ 0 at hd
    exact (not_le_of_gt (lt_add_of_le_of_pos ht (by decide)) hd).elim
  relay := by
    rintro v _ i o t ⟨⟨o', hi, _⟩, _⟩
    exact (noDelivery0 i v o' t hi).elim

private theorem prefix0 : HealthyPrefix₂ p4 unitCodec env0 rho0 0 :=
  ⟨base0, ⟨le_rfl, le_rfl⟩, healthy0, fun _ ht hb => (not_lt_of_ge ht hb).elim⟩

-- Three faulty nodes and a required tick of the one honest node.
example : (Gen.V2.Duty.faulty rho0).card = 3 := by decide +kernel
example : ¬ Gen.Pure.FaultQ p4.n (Gen.V2.Duty.faulty rho0).card := by
  intro h
  have hn : ¬ (Gen.V2.Duty.faulty rho0).card < Gen.Pure.qF p4.n := by decide +kernel
  exact hn h.lt
example : timeIdx rho0 0 = 1 := by decide +kernel
example : timeIdx rho0 (-1) = 0 ∧ timeIdx rho0 (rho0.horizon + 1) = 1 := by decide +kernel

-- A complete, nonempty healthy-prefix witness with false FaultQ.
example : CleanHistoryAt p4 unitCodec env0 rho0 0 ∧
    CleanTruncAt p4 unitCodec env0 rho0 0 :=
  ⟨cleanHistoryAt_zero prefix0, cleanTruncAt_zero prefix0⟩

example : CleanSafetyAt p4 unitCodec env0 rho0 :=
  cleanSafetyAt_of_trunc p4 unitCodec env0 rho0 schedule0 (cleanTruncAt_zero prefix0)

-- Both theorem applications keep exactly the requested premises.
example (E : Generic.Env (Fin 4)) (h : HealthyPrefix₂ p4 unitCodec E rho0 0) :
    CleanHistoryAt p4 unitCodec E rho0 0 ∧ CleanTruncAt p4 unitCodec E rho0 0 :=
  ⟨cleanHistoryAt_zero h, cleanTruncAt_zero h⟩

example (E : Generic.Env (Fin 4)) (hs : V2.D.ScheduleWellFormed E rho0)
    (ht : CleanTruncAt p4 unitCodec E rho0 rho0.horizon) :
    CleanSafetyAt p4 unitCodec E rho0 := cleanSafetyAt_of_trunc p4 unitCodec E rho0 hs ht

end AvailableChain.FGSA.Run.Tests.Zero
end
