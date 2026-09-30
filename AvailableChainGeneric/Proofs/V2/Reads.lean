module
public import AvailableChainGeneric.Statements.V2.Reads
public import AvailableChainKitV2.Execution

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

-- S3-01; Statements/V2/Reads.lean:97–100; KitV2/Execution.lean:53–65.
theorem stateBefore_idxBefore_statement : StateBeforeIdxBeforeStatement := by
  intro V _ In P E rho t hS
  rw [Run.idxBefore_def]
  unfold Run.stateBefore Run.stateBeforeTime
  apply congrArg (fun events : List (Event V P.Object) =>
    events.foldl (World.step E rho) World.init)
  exact (filter_eq_take hS (fun e => decide (e.time < t)) (by
    intro e f hk hf
    exact decide_eq_true
      (lt_of_le_of_lt (time_le_of_key_le e f hk) (of_decide_eq_true hf)))).symm

-- S3-01 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
theorem stateBefore_idxBefore :
    ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
      (E : Generic.Env V) (rho : Run V P) (t : Time) (hS : ScheduleWellFormed E rho),
      Run.stateBefore E rho (Run.idxBefore rho t) = Run.stateBeforeTime E rho t :=
  @stateBefore_idxBefore_statement

-- S3-01; pubFloor_def and positive-divisor integer division.
theorem pubFloor_le {V : Type} (E : Generic.Env V) (t : Time) :
    pubFloor E t ≤ t := by
  rw [pubFloor_def, Int.mul_comm]
  exact Int.mul_ediv_self_le (ne_of_gt E.Δ_pos)

-- S3-01; EngineV2/Conditions/Schedule.lean:18–19.
theorem publicTime_le_pubFloor {V : Type} (E : Generic.Env V) {a t : Time}
    (hpub : PublicTime E a) (hat : a ≤ t) : a ≤ pubFloor E t := by
  unfold PublicTime at hpub
  rcases hpub with ⟨k, rfl⟩
  rw [pubFloor_def]
  exact Int.mul_le_mul_of_nonneg_right
    ((Int.le_ediv_iff_mul_le E.Δ_pos).mpr hat) (le_of_lt E.Δ_pos)

-- S3-01; strict variant of KitV2/Execution.lean:99–115, using :59 and :67.
theorem index_lt_idxBefore_iff {V In : Type} {P : ProtocolSpec In}
    {E : Generic.Env V} {rho : Run V P} (hS : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object} (hi : rho.events[i]? = some e) (t : Time) :
    i < Run.idxBefore rho t ↔ e.time < t := by
  rw [Run.idxBefore_def]
  let q := fun f : Event V P.Object => decide (f.time < t)
  have hdown : ∀ a b, a.key ≤ b.key → q b = true → q a = true := by
    intro a b hk hb
    exact decide_eq_true
      (lt_of_le_of_lt (time_le_of_key_le a b hk) (of_decide_eq_true hb))
  constructor
  · intro hl
    have hm : e ∈ rho.events.filter q := by
      rw [filter_eq_take hS q hdown]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hl]; exact hi)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · intro ht
    by_contra hn
    have hf := filter_false_of_index_ge hS q hdown (Nat.le_of_not_gt hn) hi
    simp [q, ht] at hf

end AvailableChain.Gen.V2
