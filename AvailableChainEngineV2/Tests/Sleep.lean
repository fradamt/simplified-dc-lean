module
public import AvailableChainEngineV2.Tests.Engine
public import AvailableChainEngineV2.Tests.Duties
public import AvailableChainEngineV2.Conditions.Duty.Lift

@[expose] public section

namespace AvailableChain.V2.Tests.Sleep

open AvailableChain

/-- A clock and a receipt list. Restart clears receipts and sets the exact time. -/
abbrev toy : ProtocolSpec Unit :=
  { Tests.specA with
    State := Time × List Nat
    Durable := Unit
    init := (0, [])
    clock := fun st t => (t, st.2)
    act := fun _ _ _ => none
    gossip := fun st _ =>
      if st.1 = 0 then [1] else if st.1 = 4 then [2] else []
    process := fun st o => (st.1, o.payload :: st.2)
    recordOwn := fun st _ => st
    durable := fun _ => ()
    restore := fun _ t => (t, [])
    processed := fun st o => decide (o.payload ∈ st.2) }

def first : toy.Object := ⟨.none, 1⟩
def second : toy.Object := ⟨.none, 2⟩

/-- Node 0 sleeps on [2,5) and [7,10). Node 1 stays awake. -/
def env : Generic.Env (Fin 2) :=
  ⟨4, by decide, 5, by decide,
    fun v t => decide (v = 1 ∨ t < 2 ∨ (5 ≤ t ∧ t < 7) ∨ 10 ≤ t)⟩

/-- The sender emits before sleep and during sleep. Both receipts follow the wake. -/
def run : Run (Fin 2) toy where
  honest := Finset.univ
  horizon := 10
  events := [.tick 0 0, .tick 1 0, .tick 1 4, .restart 0 5,
    .deliver 0 first 5, .deliver 0 second 5, .tick 1 8, .restart 0 10]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

-- Test 1: each local event at an asleep time contradicts its sleep field.
example : ¬ SleepWellFormed env { run with events := [.tick 0 3] } := by
  intro h
  have := h.tick_awake 0 3 (by simp)
  contradiction

example : ¬ SleepWellFormed env { run with events := [.deliver 0 first 3] } := by
  intro h
  have := h.deliver_awake 0 first 3 (by simp)
  contradiction

example : ¬ SleepWellFormed env { run with events := [.restart 0 3] } := by
  intro h
  have := h.restart_awake 0 3 (by simp)
  contradiction

example : ¬ D.SleepWellFormed env { run.toD with events := [.tick 0 3] } := by
  intro h
  have := h.tick_awake 0 3 (by simp)
  contradiction

example : ¬ D.SleepWellFormed env { run.toD with events := [.deliver 0 first 3] } := by
  intro h
  have := h.deliver_awake 0 first 3 (by simp)
  contradiction

example : ¬ D.SleepWellFormed env { run.toD with events := [.restart 0 3] } := by
  intro h
  have := h.restart_awake 0 3 (by simp)
  contradiction

private theorem sleep_valid : SleepWellFormed env run := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.tick.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro v o t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.deliver.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  · intro v t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.restart.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro v _ t h0 hh hw
    fin_cases v <;> simp [Wakes, env] at hw
    have ht : t = 5 ∨ t = 10 := by omega
    rcases ht with rfl | rfl <;> simp [run]

private theorem valid : ExecutionValid env run := by
  refine { toSleepWellFormed := sleep_valid, toScheduleWellFormed := ?_,
    toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e _; exact Finset.mem_univ _
    · intro v t h
      simp only [run, List.mem_cons, List.not_mem_nil, or_false,
        Event.tick.injEq, reduceCtorEq, or_false, false_or] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · intro v _ t ⟨k, hk⟩ h0 hh ha
      have ht : t = 0 ∨ t = 4 ∨ t = 8 := by simp [env] at hk; simp [run] at hh; omega
      fin_cases v <;> rcases ht with rfl | rfl | rfl <;> simp_all [env, run]
  · refine ⟨by intros; rfl, by intros; rfl, ?_⟩
    intro i v o t hi
    have he := List.mem_of_getElem? hi
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.deliver.injEq, reduceCtorEq, or_false, false_or] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have : i = 4 := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp [run] at this
        interval_cases i <;> simp_all [run, first, second]
      subst i; decide
    · have : i = 5 := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp [run] at this
        interval_cases i <;> simp_all [run, first, second]
      subst i; decide
  · refine ⟨?_, ?_⟩
    · rintro v o t ⟨i, hi⟩ u _ hu
      have he := List.mem_of_getElem? hi
      simp only [run, List.mem_cons, List.not_mem_nil, or_false,
        Event.deliver.injEq, reduceCtorEq, or_false, false_or] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [Run.holder, first, second] at hu
    · intro v o t _ o' hc; exact hc.elim

-- Tests 2 and 9: a valid run freezes the sleeping node, in both twins.
example : ExecutionValid env run ∧
    Run.stateBefore env run 2 0 = Run.stateBefore env run 3 0 := ⟨valid, by decide⟩

example : D.ExecutionValid env run.toD ∧
    D.Run.stateBefore env run.toD 2 0 = D.Run.stateBefore env run.toD 3 0 := by
  exact ⟨(D.executionValid_toD_iff env run).mpr valid, by decide⟩

example : D.ExecutionValid env run.toD ↔ ExecutionValid env run :=
  D.executionValid_toD_iff env run

-- Test 3: a missing restart at a positive wake, including the horizon, is invalid.
example : ¬ SleepWellFormed env { run with events := [] } := by
  intro h
  exact (by simp : Event.restart 0 5 ∉ ([] : List (Event (Fin 2) toy.Object)))
    (h.wake_restart 0 (by simp [run]) 5 (by decide) (by decide) (by decide))

example : ¬ SleepWellFormed env { run with events := [.restart 0 5] } := by
  intro h
  have := h.wake_restart 0 (by simp [run]) 10 (by decide) (by decide) (by decide)
  simp at this

example : ¬ D.SleepWellFormed env { run.toD with events := [] } := by
  intro h
  have := h.wake_restart 0 (by simp [Run.toD, run]) 5
    (by decide) (by decide) (by decide)
  simp at this

example : ¬ D.SleepWellFormed env { run.toD with events := [.restart 0 5] } := by
  intro h
  have := h.wake_restart 0 (by simp [Run.toD, run]) 10
    (by decide) (by decide) (by decide)
  simp at this

-- Test 4: node 0 is awake at zero, has no restart at zero, and the run is valid.
example : env.awake 0 0 = true ∧ Event.restart 0 0 ∉ run.events ∧
    ExecutionValid env run := ⟨by decide, by decide, valid⟩

example : env.awake 0 0 = true ∧ Event.restart 0 0 ∉ run.toD.events ∧
    D.ExecutionValid env run.toD :=
  ⟨by decide, by decide, (D.executionValid_toD_iff env run).mpr valid⟩

-- Test 5: same-time phases and the action cut include only the restart.
private def sameTime : Run (Fin 2) toy :=
  { run with events := [.restart 0 5, .tick 0 5, .deliver 0 first 5] }

example : sameTime.events.Pairwise (fun e f => e.key ≤ f.key) ∧
    Run.actionCut sameTime 5 = 1 ∧ D.Run.actionCut sameTime.toD 5 = 1 := by decide

-- Test 6: 5 is not a public tick time; both restore clocks still read exactly 5.
example : ¬ PublicTime env 5 := by rintro ⟨k, hk⟩; simp [env] at hk; omega

example : (Run.stateAfterRestartsAt env run 5 0).1 = 5 ∧
    (D.Run.stateAfterRestartsAt env run.toD 5 0).1 = 5 := by decide

-- Test 7: these are real emissions before sleep and during sleep.
example : Run.emits env run 1 first 0 := ⟨1, rfl, by decide⟩
example : Run.emits env run 1 second 4 := ⟨2, rfl, by decide⟩

private theorem demand (o : toy.Object) (ho : o = first ∨ o = second) (send : Time) :
    DeliveryDemand env run 1 0 o send (fun a => max a 5 + 2) 10 := by
  intro a _ _ hlt _ hh hr _
  have ha : a = 5 := by
    have hs := hr a le_rfl hlt
    have h2 := hr 2
    have h7 := hr 7
    simp only [LinkReadyOn, AwakeOn] at hr
    simp [env] at hs h2 h7
    simp only [run] at hh
    omega
  subst a
  apply Or.inr
  rcases ho with rfl | rfl
  · exact ⟨5, by decide, by decide, 4, first, rfl, rfl⟩
  · exact ⟨5, by decide, by decide, 5, second, rfl, rfl⟩

example : DeliveryDemand env run 1 0 first 0 (fun a => max a 5 + 2) 10 :=
  demand first (Or.inl rfl) 0

example : DeliveryDemand env run 1 0 second 4 (fun a => max a 5 + 2) 10 :=
  demand second (Or.inr rfl) 4

example : D.DeliveryDemand env run.toD 1 0 first 0 (fun a => max a 5 + 2) 10 :=
  (D.deliveryDemand_toD_iff env run 1 0 first 0 _ 10).mpr (demand first (Or.inl rfl) 0)

example : D.DeliveryDemand env run.toD 1 0 second 4 (fun a => max a 5 + 2) 10 :=
  (D.deliveryDemand_toD_iff env run 1 0 second 4 _ 10).mpr (demand second (Or.inr rfl) 4)

-- The second sleep cancels the anchor at 6 (deadline 8).
example : ¬ LinkReadyOn env run 1 0 6 8 := by
  intro h
  have := h 7 (by decide) (by decide)
  contradiction

example : ¬ D.LinkReadyOn env run.toD 1 0 6 8 := by
  intro h
  have := h 7 (by decide) (by decide)
  contradiction

-- Test 8: a pre-restart receipt meets service even when the restart erases it.
example : toy.processed (Run.stateAfterRestartsAt env run 10 0) first = false ∧
    DeliveryService env run 0 first 10 12 := by
  refine ⟨by decide, Or.inl ⟨5, by decide, by decide⟩⟩

example : toy.toD.processed (D.Run.stateAfterRestartsAt env run.toD 10 0) first = false ∧
    D.DeliveryService env run.toD 0 first 10 12 := by
  refine ⟨by decide, Or.inl ⟨5, by decide, by decide⟩⟩

end AvailableChain.V2.Tests.Sleep

end
