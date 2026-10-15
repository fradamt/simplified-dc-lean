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

end AvailableChain.FGCompose.Tests.POP6bMixed
end
