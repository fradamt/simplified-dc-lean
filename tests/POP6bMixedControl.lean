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

private abbrev tickIndex (t : Nat) : Nat := 2 * t + 2 * ((t - 4) / 4)

private theorem execution_premises_sat :
    V2.D.ScheduleWellFormed env run ∧ FGHonestSeats reads run = {0} ∧
    v5E.weightOf (historyFaulty reads run) < v5E.q ∧
    (∀ t : Fin 257, run.events[tickIndex t]? = some (.tick 7 (t : Time)) ∧
      run.events[tickIndex t + 1]? = some (.tick 9 (t : Time))) := by
  have table : ∀ t : Fin 257,
      eventShape[tickIndex t]? = some (true, 7, t.val) ∧
      eventShape[tickIndex t + 1]? = some (true, 9, t.val) := by decide +kernel
  have ticks : ∀ t : Fin 257, run.events[tickIndex t]? = some (.tick 7 (t : Time)) ∧
      run.events[tickIndex t + 1]? = some (.tick 9 (t : Time)) := by
    intro t
    constructor
    · change (eventShape.map eventOf)[tickIndex t]? = _
      rw [List.getElem?_map, (table t).1]
      rfl
    · change (eventShape.map eventOf)[tickIndex t + 1]? = _
      rw [List.getElem?_map, (table t).2]
      rfl
  have info : ∀ e ∈ run.events, 0 ≤ e.time ∧ e.time ≤ 256 ∧
      e.node ∈ ({7, 9} : Finset Nat) := by
    have tab : ∀ e ∈ eventShape, 0 ≤ (eventOf e).time ∧ (eventOf e).time ≤ 256 ∧
        (eventOf e).node ∈ ({7, 9} : Finset Nat) := by decide +kernel
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact tab d hd
  refine ⟨?_, ?_, by decide, ticks⟩
  · refine ⟨by decide, ?_, ?_, fun e he => ⟨(info e he).1, (info e he).2.1⟩,
      fun e he => (info e he).2.2, ?_, ?_⟩
    · have key (e : Bool × Nat × Nat) : (eventOf e).key =
          toLex ((e.2.2 : Time), if e.1 then (1 : Nat) else 2) := by
        obtain ⟨b, x, t⟩ := e
        cases b <;> rfl
      have sorted : eventShape.Pairwise (fun a b =>
          toLex ((a.2.2 : Time), if a.1 then (1 : Nat) else 2) ≤
            toLex ((b.2.2 : Time), if b.1 then (1 : Nat) else 2)) := by
        have adjacent : (eventShape.map (fun e =>
            toLex ((e.2.2 : Time), if e.1 then (1 : Nat) else 2))).IsChain
              (fun a b => a ≤ b) := by decide +kernel
        exact List.pairwise_map.mp (List.isChain_iff_pairwise.mp adjacent)
      change (eventShape.map eventOf).Pairwise _
      rw [List.pairwise_map]
      simpa only [key] using sorted
    · have recover : Function.LeftInverse
          (fun e : V2.Event Nat protocol.Object => match e with
            | .tick x t => (true, x, t.toNat)
            | .deliver x _ t => (false, x, t.toNat)
            | .restart x t => (true, x, t.toNat)) eventOf := by
        rintro ⟨b, x, t⟩
        cases b <;> simp [eventOf]
      have adjacent : (eventShape.map (fun e => 8 * e.2.2 +
          (if e.1 then 0 else 2) + (if e.2.1 = 9 then 1 else 0))).IsChain
            (fun a b => a < b) := by decide +kernel
      have nd : eventShape.Nodup := List.Nodup.of_map _
        ((List.isChain_iff_pairwise.mp adjacent).imp ne_of_lt)
      exact List.Nodup.map recover.injective nd
    · intro x t ht
      have hn : 0 ≤ t := (info _ ht).1
      refine ⟨t.toNat, ?_⟩
      change t = (t.toNat : Int) * 1
      rw [Int.toNat_of_nonneg hn, Int.mul_one]
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 257 := by change (k : Int) * 1 ≤ 256 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa [run] using hx
      rcases hx' with rfl | rfl
      · simpa [env] using List.mem_of_getElem? (ticks ⟨k, hk⟩).1
      · simpa [env] using List.mem_of_getElem? (ticks ⟨k, hk⟩).2
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide

#print axioms execution_premises_sat

private def shapeStep (w : Nat → Nat) (e : Bool × Nat × Nat) : Nat → Nat :=
  if e.1 then w else Function.update w e.2.1 (max (w e.2.1) (e.2.2 / 4))
private def shapeState (es : List (Bool × Nat × Nat)) : Nat → Nat :=
  es.foldl shapeStep (fun _ => 0)

-- This is a proved calculation of this ordinary event fold, with the actual releases.
private theorem fold_premises_sat :
    (∀ i x, run.stateBefore env i x = shapeState (eventShape.take i) x) ∧
    (∀ t x, run.stateBeforeTime env t x =
      shapeState (eventShape.filter (fun e => decide ((e.2.2 : Time) < t))) x) ∧
    (∀ j x t, run.events[j]? = some (.tick x t) →
      postClock env run x t = some (shapeState (eventShape.take j) x)) := by
  have tick (st x : Nat) (t : Time) : (V2.D.tick env run st x t).1 = st := by
    change List.foldl (fun st (_ : protocol.Object) => st) st _ = st
    exact List.foldl_fixed _
  have step (w : Nat → Nat) (e : Bool × Nat × Nat) :
      V2.D.World.step env run w (eventOf e) = shapeStep w e := by
    obtain ⟨b, x, t⟩ := e
    cases b
    · change Function.update w x (max (w x) (chain (t / 4)).slot) =
        Function.update w x (max (w x) (t / 4))
      rw [chain_slot]
    · change Function.update w x (V2.D.tick env run (w x) x (t : Time)).1 = w
      rw [tick, Function.update_eq_self]
  have fold (es : List (Bool × Nat × Nat)) (w : Nat → Nat) :
      (es.map eventOf).foldl (V2.D.World.step env run) w = es.foldl shapeStep w := by
    rw [List.foldl_map]
    simp only [step]
  have prefixCalc (i x : Nat) : run.stateBefore env i x = shapeState (eventShape.take i) x := by
    unfold V2.D.Run.stateBefore
    change (((eventShape.map eventOf).take i).foldl (V2.D.World.step env run)
      (fun _ => 0)) x = _
    rw [← List.map_take, fold]
    rfl
  have before (t : Time) (x : Nat) : run.stateBeforeTime env t x =
      shapeState (eventShape.filter (fun e => decide ((e.2.2 : Time) < t))) x := by
    have time (e : Bool × Nat × Nat) : (eventOf e).time = (e.2.2 : Time) := by
      obtain ⟨b, x, d⟩ := e
      cases b <;> rfl
    unfold V2.D.Run.stateBeforeTime
    change (((eventShape.map eventOf).filter (fun e => decide (e.time < t))).foldl
      (V2.D.World.step env run) (fun _ => 0)) x = _
    rw [List.filter_map, fold]
    simp only [Function.comp_def, time]
    rfl
  refine ⟨prefixCalc, before, ?_⟩
  intro j x t hj
  have hjl : j < run.events.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? run x t = some k := by
    rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
    refine ⟨run.events[j], List.getElem_mem hjl, ?_⟩
    rw [(List.getElem?_eq_some_iff.mp hj).2]
    simp
  have hk' := V2.D.Run.tickIdx?_spec hk
  have hkj : k = j := by
    have hkl : k < run.events.length := (List.getElem?_eq_some_iff.mp hk').1
    apply (execution_premises_sat.1.nodup.getElem_inj_iff (hi := hkl) (hj := hjl)).mp
    rw [(List.getElem?_eq_some_iff.mp hk').2, (List.getElem?_eq_some_iff.mp hj).2]
  simp only [postClock, preTick, hk, hkj, Option.map_some]
  change some (run.stateBefore env j x) = _
  rw [prefixCalc]

#print axioms fold_premises_sat

private theorem action_premises_sat : ∀ r : Fin 32, ∀ x ∈ run.honest,
    postClock env run x (v5T.action r) = some (2 * r.val) ∧
    actionSourceFG core env run v5T x r = some (some (chain (2 * r.val))) := by
  have table : ∀ r : Fin 32,
      shapeState (eventShape.take (tickIndex (8 * r.val + 6))) 7 = 2 * r.val ∧
      shapeState (eventShape.take (tickIndex (8 * r.val + 6) + 1)) 9 = 2 * r.val := by
    decide +kernel
  intro r x hx
  have hx' : x = 7 ∨ x = 9 := by simpa [run] using hx
  have ht : v5T.action r = ((8 * r.val + 6 : Nat) : Time) := by
    dsimp [v5T]
  have hs := execution_premises_sat.2.2.2 ⟨8 * r.val + 6, by omega⟩
  have hp : postClock env run x (v5T.action r) = some (2 * r.val) := by
    rw [ht]
    rcases hx' with rfl | rfl
    · rw [fold_premises_sat.2.2 _ _ _ hs.1, (table r).1]
    · rw [fold_premises_sat.2.2 _ _ _ hs.2, (table r).2]
  refine ⟨hp, ?_⟩
  change (postClock env run x (v5T.action r)).map core.source = _
  rw [hp]
  change some (some (chain (min (2 * r.val) 64))) = _
  rw [Nat.min_eq_left (by omega)]

#print axioms action_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end
