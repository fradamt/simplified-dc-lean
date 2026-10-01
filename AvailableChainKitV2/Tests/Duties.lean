module
public import AvailableChainKitV2.DutyEmission
public import AvailableChainKitV2.DutyLinked

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.V2.D.Engine.Tests.Duties

/-- Two FG duties at times 0 and 1 use the same signing label and seat. -/
abbrev toy : ProtocolSpecD Unit where
  State := List Bool
  Label := Unit
  Duty := Bool
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Bool
  Durable := List Bool
  init := []
  clock := fun st _ => st
  actTime := fun d => if d then 1 else 0
  duties := fun t => if t = 0 then [false] else if t = 1 then [true] else []
  duties_spec := by
    intro d t
    cases d <;> split_ifs <;> simp_all [eq_comm]
  duties_nodup := by intro t; split_ifs <;> simp
  act := fun st d _ => if d ∈ st then none else some d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st o => o.payload :: st
  durable := id
  restore := id
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

abbrev env : Generic.Env (Fin 1) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩

abbrev run : D.Run (Fin 1) toy where
  honest := {0}
  horizon := 1
  events := [.tick 0 0, .tick 0 1]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem exact_emission (st : toy.State) (v : Fin 1) (t : Time) (p : Bool) :
    (⟨.seat () 0, p⟩ : toy.Object) ∈ (D.tick env run st v t).2 ↔
      env.awake v t = true ∧ run.seatOf () 0 = v ∧
        ∃ d, toy.signLabel d = () ∧ toy.actTime d = t ∧
          toy.act (toy.clock st t) d (run.input v t) = some p :=
  mem_tick_seat_iff env run st v t () 0 p

theorem same_label_two_times :
    (⟨.seat () 0, false⟩ : toy.Object) ∈ (D.tick env run [] 0 0).2 ∧
    (⟨.seat () 0, true⟩ : toy.Object) ∈ (D.tick env run [false] 0 1).2 := by
  constructor
  · exact (mem_tick_seat_iff env run [] 0 0 () 0 false).mpr
      ⟨rfl, rfl, false, rfl, rfl, rfl⟩
  · exact (mem_tick_seat_iff env run [false] 0 1 () 0 true).mpr
      ⟨rfl, rfl, true, rfl, rfl, rfl⟩

theorem single_bijection : D.Linked (fun ℓ => ℓ = ()) run :=
  (linked_singleton_iff run ()).mpr ⟨Equiv.refl (Fin 1), fun _ => rfl⟩

theorem exact_bijective_seat (st : toy.State) (v : Fin 1) (t : Time) (p : Bool) :
    (⟨.seat () 0, p⟩ : toy.Object) ∈ (D.tick env run st v t).2 ↔
      0 = v ∧ env.awake v t = true ∧
        ∃ d, toy.signLabel d = () ∧ toy.actTime d = t ∧
          toy.act (toy.clock st t) d (run.input v t) = some p :=
  emits_bijSeat env run (Equiv.refl (Fin 1)) (fun _ => rfl) st v t 0 p

end AvailableChain.V2.D.Engine.Tests.Duties

#print axioms AvailableChain.V2.D.Engine.Tests.Duties.exact_emission
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.same_label_two_times
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.single_bijection
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.exact_bijective_seat
