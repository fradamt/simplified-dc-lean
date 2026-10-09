module
public import AvailableChainKitV2.EngineClock
public import AvailableChainKitV2.DutyEngineClock
public import AvailableChainEngineV2.Tests.Sleep

@[expose] public section

namespace AvailableChain.V2.Engine.Tests.Sleep

open AvailableChain

abbrev proto := V2.Tests.Sleep.toy
abbrev obj : proto.Object := V2.Tests.Sleep.first
abbrev env : Generic.Env Unit := ⟨2, by decide, 0, le_rfl, fun _ t => decide (1 ≤ t)⟩
abbrev run : Run Unit proto where
  honest := {()}
  horizon := 2
  events := [.restart () 1, .deliver () obj 1, .tick () 2]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem schedule : ScheduleWellFormed env run where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by simp [Event.time]
  honest_only := by simp
  tick_public := by
    intro v t h
    have ht : t = 2 := by simpa using h
    exact ht ▸ ⟨1, rfl⟩
  tick_total := by
    intro v _ t ⟨k, hk⟩ h0 hh ha
    have ht : t = 2 := by
      change t = (k : Int) * 2 at hk
      change t ≤ 2 at hh
      change decide (1 ≤ t) = true at ha
      have := of_decide_eq_true ha
      dsimp [Time] at *; omega
    rw [ht]
    simp

private theorem sleep : SleepWellFormed env run where
  tick_awake := by intros v t h; simp_all
  deliver_awake := by intros v o t h; simp_all
  restart_awake := by intros v t h; simp_all
  wake_restart := by
    intro v _ t _ _ hw
    have ht : t = 1 := by
      simp only [Wakes, decide_eq_true_eq, decide_eq_false_iff_not] at hw
      dsimp [Time] at *; omega
    subst t; simp

abbrev clock : ClockLaws proto := ⟨Prod.fst, rfl, fun _ _ => rfl,
  fun _ _ => rfl, fun _ _ => rfl⟩
abbrev restoreTime : RestoreTimeLaw clock := ⟨fun _ _ => rfl⟩

-- The non-public wake at 1 precedes the delivery at the same time.
example : ∃ i, i < 1 ∧ run.events[i]? = some (.restart () 1) :=
  wake_restart_before_event schedule sleep (by simp) (by decide) (by decide)
    ⟨rfl, rfl⟩ rfl rfl rfl (by decide)

example : ∃ i, i < 1 ∧ run.toD.events[i]? = some (.restart () 1) :=
  D.Engine.wake_restart_before_event ((D.scheduleWellFormed_toD_iff env run).mpr schedule)
    ((D.sleepWellFormed_toD_iff env run).mpr sleep)
    (by simp) (by decide) (by decide) ⟨rfl, rfl⟩ rfl rfl rfl (by decide)

example : clock.now (Run.stateBefore env run 1 ()) = 1 := by
  rw [state_after_restart (show run.events[0]? = some (.restart () 1) from rfl)]

abbrev frozenEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, le_rfl, fun v _ => decide (v = 1)⟩
abbrev frozenRun : Run (Fin 2) proto where
  honest := Finset.univ
  horizon := 2
  events := [.tick 1 0, .tick 1 2]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

private theorem frozenSleep : SleepWellFormed frozenEnv frozenRun where
  tick_awake := by
    intro v t h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Event.tick.injEq] at h
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  deliver_awake := by intros v o t h; simp at h
  restart_awake := by intros v t h; simp at h
  wake_restart := by
    intro v _ t _ _ hw
    have := hw.1
    have := hw.2
    simp_all [Wakes]

-- Two events of another node occur while node 0 sleeps. Every field stays fixed.
example : Run.stateBefore frozenEnv frozenRun 0 0 =
    Run.stateBefore frozenEnv frozenRun 2 0 :=
  asleep_state_frozen frozenSleep (by decide) (by intros; rfl)

example : D.Run.stateBefore frozenEnv frozenRun.toD 0 0 =
    D.Run.stateBefore frozenEnv frozenRun.toD 2 0 :=
  D.Engine.asleep_state_frozen
    ((D.sleepWellFormed_toD_iff frozenEnv frozenRun).mpr frozenSleep)
    (by decide) (by intros; rfl)

-- The tick reads the restored state; the old strict-time read omits the restart.
example : Run.stateBefore env run 2 () = Run.stateAfterRestartsAt env run 2 () :=
  stateBefore_tick_eq_stateAfterRestartsAt schedule rfl

abbrev wakeTickEnv : Generic.Env Unit :=
  ⟨2, by decide, 0, le_rfl, fun _ t => decide (2 ≤ t)⟩
abbrev wakeTickRun : Run Unit proto :=
  { run with events := [.restart () 2, .tick () 2] }

private theorem wakeTickSchedule : ScheduleWellFormed wakeTickEnv wakeTickRun where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by simp [Event.time]
  honest_only := by simp
  tick_public := by
    intro v t h
    have ht : t = 2 := by simpa using h
    exact ht ▸ ⟨1, rfl⟩
  tick_total := by
    intro v _ t _ _ hh ha
    have ht : t = 2 := by
      change t ≤ 2 at hh
      have ha' : 2 ≤ t := of_decide_eq_true ha
      exact le_antisymm hh ha'
    rw [ht]; simp

private theorem wakeTickSleep : SleepWellFormed wakeTickEnv wakeTickRun where
  tick_awake := by intros v t h; simp_all
  deliver_awake := by intros v o t h; simp at h
  restart_awake := by intros v t h; simp_all
  wake_restart := by
    intro v _ t _ hh hw
    have ht : t = 2 := by
      change t ≤ 2 at hh
      have ha : 2 ≤ t := of_decide_eq_true hw.1
      exact le_antisymm hh ha
    rw [ht]; simp

-- A valid sleep schedule with a wake exactly at the public tick.
example : ∃ i, i < 1 ∧ wakeTickRun.events[i]? = some (.restart () 2) :=
  wake_restart_before_event wakeTickSchedule wakeTickSleep (by simp) (by decide)
    (by decide) ⟨rfl, rfl⟩ rfl rfl rfl (by decide)

example : Run.stateBefore wakeTickEnv wakeTickRun 1 () =
    Run.stateAfterRestartsAt wakeTickEnv wakeTickRun 2 () :=
  stateBefore_tick_eq_stateAfterRestartsAt wakeTickSchedule rfl

example : Run.stateBefore wakeTickEnv wakeTickRun 1 () ≠
    Run.stateBeforeTime wakeTickEnv wakeTickRun 2 () := by decide

end AvailableChain.V2.Engine.Tests.Sleep

end
