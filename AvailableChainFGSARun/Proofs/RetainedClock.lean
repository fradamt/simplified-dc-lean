module
public import AvailableChainKitV2.DutyEngineClock
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt

public section

/-! Ruling Y: Kit clock proofs for a restore that retains the supplied clock.
These variants are local to FG-SA and leave the shared Kit contracts unchanged. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.V2 (Event)
open AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : V2.ProtocolSpecD In}

private theorem fgsa_retained_stateBefore_zero (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) :
    V2.D.Run.stateBefore E rho 0 v = P.init := by
  rfl

/-! ### The clock source and the clock bound -/

private theorem fgsa_retained_now_source_aux (C : ClockLaws P)
    (E : Generic.Env V) (rho : V2.D.Run V P) (v : V)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      C.now (P.restore (P.durable (V2.D.Run.stateBefore E rho k v))) =
        C.now (V2.D.Run.stateBefore E rho k v)) (i : Nat) :
    C.now (V2.D.Run.stateBefore E rho i v) ≤ 0 ∨
      ∃ j < i, rho.events[j]? = some (.tick v (C.now (V2.D.Run.stateBefore E rho i v))) := by
  induction i with
  | zero => left; rw [fgsa_retained_stateBefore_zero, C.init]
  | succ i ih =>
      have ih' : C.now (V2.D.Run.stateBefore E rho i v) ≤ 0 ∨
          ∃ j < i + 1, rho.events[j]? = some (.tick v (C.now (V2.D.Run.stateBefore E rho i v))) :=
        ih.imp_right fun ⟨j, hj, he⟩ => ⟨j, Nat.lt_succ_of_lt hj, he⟩
      cases hi : rho.events[i]? with
      | none => simpa [V2.D.Run.stateBefore, List.take_add_one, hi] using ih'
      | some e =>
          rw [V2.D.Run.stateBefore_succ E rho hi]
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                dsimp only [Event.node] at hv; subst u
                simpa only [V2.D.World.step, Function.update_self, hR i t hi] using ih'
            | tick u t =>
                dsimp only [Event.node] at hv; subst u
                right
                simp only [V2.D.World.step, Function.update_self, C.now_tick]
                exact ⟨i, Nat.lt_succ_self i, hi⟩
            | deliver u o t =>
                dsimp only [Event.node] at hv; subst u
                simpa only [V2.D.World.step, Function.update_self, C.process] using ih'
          · rwa [V2.D.World.step_apply_of_node_ne E rho _ hv]

theorem stateBefore_now_source_retained (C : ClockLaws P)
    (hrestore_now : ∀ st, C.now (P.restore (P.durable st)) = C.now st)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (v : V) :
    C.now (V2.D.Run.stateBefore E rho i v) ≤ 0 ∨
      ∃ j < i, rho.events[j]? = some (.tick v (C.now (V2.D.Run.stateBefore E rho i v))) :=
  fgsa_retained_now_source_aux C E rho v (fun _ _ _ => hrestore_now _) i

private theorem fgsa_retained_now_le_event_aux (C : ClockLaws P)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (hs : ScheduleWellFormed E rho) (v : V)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      C.now (P.restore (P.durable (V2.D.Run.stateBefore E rho k v))) =
        C.now (V2.D.Run.stateBefore E rho k v))
    {i : Nat} {e : Event V P.Object} (hi : rho.events[i]? = some e) :
    C.now (V2.D.Run.stateBefore E rho i v) ≤ e.time := by
  rcases fgsa_retained_now_source_aux C E rho v hR i with hz | ⟨j, hj, ht⟩
  · exact le_trans hz (hs.in_horizon e (List.mem_of_getElem? hi)).1
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ht
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
    rw [hje, hie] at hk
    exact time_le_of_key_le _ _ hk

theorem stateBefore_now_le_event_retained (C : ClockLaws P)
    (hrestore_now : ∀ st, C.now (P.restore (P.durable st)) = C.now st)
    (E : Generic.Env V) (rho : V2.D.Run V P) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object}
    (hi : rho.events[i]? = some e) (v : V) :
    C.now (V2.D.Run.stateBefore E rho i v) ≤ e.time :=
  fgsa_retained_now_le_event_aux C E rho hs v (fun _ _ _ => hrestore_now _) hi

/-! ### Invariants and stability with the clock precondition -/

private theorem fgsa_retained_stable_clock_aux (C : ClockLaws P)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (hs : ScheduleWellFormed E rho) (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    {i j : Nat} (hij : i ≤ j) (v : V)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      C.now (P.restore (P.durable (V2.D.Run.stateBefore E rho k v))) =
        C.now (V2.D.Run.stateBefore E rho k v))
    (hrestart : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.restart v t) →
      Q (V2.D.Run.stateBefore E rho k v) →
      Q (P.restore (P.durable (V2.D.Run.stateBefore E rho k v))))
    (hi : Q (V2.D.Run.stateBefore E rho i v)) : Q (V2.D.Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q hij v ?_ hi
  intro k e hik hkj he hv hk
  cases e with
  | restart u t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [V2.D.World.step, Function.update_self] using hrestart k t hik hkj he hk
  | tick u t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [V2.D.World.step, Function.update_self] using
        tick_preserve E rho Q hrecord
          (hclock _ t (fgsa_retained_now_le_event_aux C E rho hs v hR he) hk)
  | deliver u o t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [V2.D.World.step, Function.update_self] using hprocess _ o hk

theorem stateBefore_invariant_retained (C : ClockLaws P)
    (hrestore_now : ∀ st, C.now (P.restore (P.durable st)) = C.now st)
    (E : Generic.Env V) (rho : V2.D.Run V P) (hs : ScheduleWellFormed E rho)
    (Q : P.State → Prop) (hinit : Q P.init)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st, Q st → Q (P.restore (P.durable st))) (i : Nat) (v : V) :
    Q (V2.D.Run.stateBefore E rho i v) :=
  fgsa_retained_stable_clock_aux C E rho hs Q hclock hprocess hrecord (Nat.zero_le i) v
    (fun _ _ _ => hrestore_now _) (fun _ _ _ _ _ => hrestore _)
    (by rw [fgsa_retained_stateBefore_zero]; exact hinit)

/-- Relay admission stays timely when restart retains the clock. -/
theorem timely_of_relay_retained
    (E : Generic.Env V) (rho : V2.D.Run V P)
    {Timely : P.State → P.Object → Prop} (C : Gen.V2.Duty.TimelyClock P Timely)
    (hAS : Gen.V2.Duty.AdmitSound P C) (hS : ScheduleWellFormed E rho)
    (hrestore : ∀ st, C.clock.now (P.restore (P.durable st)) = C.clock.now st)
    (v : V) (i : Nat) (o : P.Object) (t : Time)
    (hacc : V2.D.Run.acceptsAt E rho i v o t) :
    C.actTime o ≤ Gen.V2.Duty.pubFloor E t := by
  have hzero : 0 ≤ (0 : Time) ∧ V2.PublicTime E 0 := by
    refine ⟨le_rfl, ?_⟩
    unfold V2.PublicTime
    exact ⟨0, (Int.zero_mul E.Δ).symm⟩
  have hclock : 0 ≤ C.clock.now (V2.D.Run.stateBefore E rho i v) ∧
      V2.PublicTime E (C.clock.now (V2.D.Run.stateBefore E rho i v)) := by
    refine stateBefore_step_induction E rho
      (fun st => 0 ≤ C.clock.now st ∧ V2.PublicTime E (C.clock.now st))
      (Nat.zero_le i) v ?_ ?_
    · intro k e h0k hki he hv hk
      cases e with
      | restart u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [V2.D.World.step]
          rw [Function.update_self, hrestore]
          exact hk
      | tick u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [V2.D.World.step]
          rw [Function.update_self, C.clock.now_tick]
          have hmem := List.mem_of_getElem? he
          exact ⟨(hS.in_horizon _ hmem).1, hS.tick_public v t' hmem⟩
      | deliver u o' t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [V2.D.World.step]
          rw [Function.update_self, C.clock.process]
          exact hk
    · unfold V2.D.Run.stateBefore V2.D.World.init
      simp only [List.take_zero, List.foldl_nil, C.clock.init]
      exact hzero
  unfold V2.D.Run.acceptsAt V2.D.Run.handlesAt at hacc
  rcases hacc with ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩
  rw [V2.D.Run.stateBefore_succ E rho hi] at htrue
  dsimp only [V2.D.World.step] at htrue
  rw [Function.update_self] at htrue
  have htimely := hAS.timely _ o' o
    (by rw [C.clockOf_eq]; exact hclock.1) hfalse htrue hhandles
  have hact := (C.timely_iff _ o).1 htimely
  rw [C.clockOf_eq] at hact
  exact hact.trans (publicTime_le_pubFloor E hclock.2
    (stateBefore_now_le_event_retained C.clock hrestore E rho hS hi v))

end AvailableChain.FGSA.Run

end
