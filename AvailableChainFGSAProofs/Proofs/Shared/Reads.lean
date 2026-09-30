module
public import AvailableChainFGSAClaims.Statements.Reads
import AvailableChainKitV2.Execution

public section

/-! Post-gate cut proofs (P3 F0.1). -/

namespace AvailableChain.FGSA.Run

variable {V : Type} {In : Type} {P : V2.ProtocolSpec In}
    (E : Generic.Env V) (rho : V2.Run V P)

private theorem cut_downward (t : Time) :
    ∀ e f : V2.Event V P.Object, e.key ≤ f.key →
      cutPred t f = true → cutPred t e = true := by
  intro e f hk hf
  exact decide_eq_true (hk.trans (of_decide_eq_true hf))

variable [DecidableEq V]

/-- The post-gate cut is an event-prefix state. -/
theorem afterTicks_eq_stateBefore (hs : V2.ScheduleWellFormed E rho) (t : Time) :
    afterTicks E rho t = V2.Run.stateBefore E rho (afterTicksIdx rho t) := by
  exact congrArg (fun events => events.foldl (V2.World.step E rho) V2.World.init)
    (V2.Engine.filter_eq_take hs (cutPred t) (cut_downward t))

/-- Later ticks at the cut belong to other nodes. No restart premise is needed. -/
theorem afterTicks_node (hs : V2.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    afterTicks E rho t v =
      (V2.tick E rho (V2.Run.stateBefore E rho i v) v t).1 := by
  have hf := V2.Engine.filter_eq_take hs (cutPred t) (cut_downward t)
  have hcut : cutPred t (V2.Event.tick v t : V2.Event V P.Object) = true :=
    decide_eq_true le_rfl
  have hic : i < afterTicksIdx rho t := by
    by_contra hn
    have hfalse := V2.Engine.filter_false_of_index_ge hs (cutPred t)
      (cut_downward t) (Nat.le_of_not_gt hn) hi
    rw [hcut] at hfalse
    contradiction
  rw [afterTicks_eq_stateBefore E rho hs t]
  calc
    V2.Run.stateBefore E rho (afterTicksIdx rho t) v =
        V2.Run.stateBefore E rho (i + 1) v := by
      apply V2.Engine.stateBefore_other_node E rho (Nat.succ_le_of_lt hic)
      intro j e hij hjc hj hnode
      have hm : e ∈ rho.events.filter (cutPred t) := by
        rw [hf]
        apply List.mem_of_getElem? (i := j)
        change (rho.events.take (afterTicksIdx rho t))[j]? = some e
        rw [List.getElem?_take_of_lt hjc]
        exact hj
      have hecut : e.key ≤ toLex (t, 1) :=
        of_decide_eq_true (List.mem_filter.mp hm).2
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl (by omega)
      rw [hie, hje] at hk
      change toLex (t, 1) ≤ toLex (e.time, e.phase) at hk
      change toLex (e.time, e.phase) ≤ toLex (t, 1) at hecut
      have hpair : (e.time, e.phase) = (t, 1) :=
        congrArg ofLex (le_antisymm hecut hk)
      have ht : e.time = t := congrArg Prod.fst hpair
      have hp : e.phase = 1 := congrArg Prod.snd hpair
      have he : e = .tick v t := by
        cases e with
        | restart u a => change (0 : Nat) = 1 at hp; contradiction
        | tick u a => change u = v at hnode; change a = t at ht; rw [hnode, ht]
        | deliver u o a => change (2 : Nat) = 1 at hp; contradiction
      have hji : j = i :=
        (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
      omega
    _ = _ := (V2.Run.step_tick_eq E rho hi).1

/-- Without restarts, the tick input is the strict-before-time read. -/
theorem afterTicks_eq_tick_preTick (hs : V2.ScheduleWellFormed E rho)
    (hnr : V2.NoRestart rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    afterTicks E rho t v =
      (V2.tick E rho (V2.Run.stateBeforeTime E rho t v) v t).1 := by
  rw [afterTicks_node E rho hs hi, V2.Engine.stateBefore_tick_eq_stateBeforeTime hs hnr hi]

omit [DecidableEq V] in
/-- The strict-before index is before the cut, and the inclusive index is after it. -/
theorem preIdx_le_afterTicksIdx (hs : V2.ScheduleWellFormed E rho) (t : Time) :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤ afterTicksIdx rho t ∧
    afterTicksIdx rho t ≤ (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  have _ := hs.sorted
  constructor
  · change _ ≤ (rho.events.filter (cutPred t)).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr (Or.inl (of_decide_eq_true he)))
  · change (rho.events.filter (cutPred t)).length ≤ _
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
    · exact decide_eq_true (le_of_lt h)
    · exact decide_eq_true (le_of_eq h)

omit [DecidableEq V] in
/-- The post-gate index increases with time. -/
theorem afterTicksIdx_mono (rho : V2.Run V P) {t u : Time} (htu : t ≤ u) :
    afterTicksIdx rho t ≤ afterTicksIdx rho u := by
  change (rho.events.filter (cutPred t)).length ≤ (rho.events.filter (cutPred u)).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  have htu' : toLex (t, (1 : Nat)) ≤ toLex (u, 1) :=
    Prod.Lex.toLex_le_toLex.mpr (htu.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩))
  exact decide_eq_true ((of_decide_eq_true he).trans htu')

end AvailableChain.FGSA.Run

end
