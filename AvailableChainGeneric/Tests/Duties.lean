module
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures
public import AvailableChainGeneric.Proofs.V2.Duty.Linked

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.Gen.V2.Duty.Tests

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

theorem no_single_duty : ¬ SingleDuty toy () := by
  rintro ⟨d, _, h⟩
  have hf := h false rfl
  have ht := h true rfl
  exact Bool.false_ne_true (hf.trans ht.symm)

theorem send_once : EmitOnceUnder env run () := by
  intro i _ p j k t u hj hk hp hq
  have hjlt : j < 2 := (List.getElem?_eq_some_iff.mp hj).1
  have hklt : k < 2 := (List.getElem?_eq_some_iff.mp hk).1
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have emitted : D.Run.emitsAt env run 0 = [⟨.seat () 0, false⟩] ∧
      D.Run.emitsAt env run 1 = [⟨.seat () 0, true⟩] := by decide
  have hjcases : j = 0 ∨ j = 1 := by omega
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hjcases with rfl | rfl <;> rcases hkcases with rfl | rfl
  · rfl
  · simp only [emitted.1, List.mem_singleton, Signed.mk.injEq, true_and] at hp
    simp only [emitted.2, List.mem_singleton, Signed.mk.injEq, true_and] at hq
    exact (Bool.false_ne_true (hp.symm.trans hq)).elim
  · simp only [emitted.2, List.mem_singleton, Signed.mk.injEq, true_and] at hp
    simp only [emitted.1, List.mem_singleton, Signed.mk.injEq, true_and] at hq
    exact (Bool.false_ne_true (hq.symm.trans hp)).elim
  · rfl

theorem uniqueness_consumer (p : Bool) (j k : Nat) (t u : Time)
    (hj : run.events[j]? = some (.tick 0 t)) (hk : run.events[k]? = some (.tick 0 u))
    (hp : (⟨.seat () 0, p⟩ : toy.Object) ∈ D.Run.emitsAt env run j)
    (hq : (⟨.seat () 0, p⟩ : toy.Object) ∈ D.Run.emitsAt env run k) :
    j = k ∧ t = u :=
  emit_unique_of_emitOnce env run () send_once 0 (by simp) p j k t u hj hk hp hq

/-- This protocol repeats one content, so the send-once premise is false. -/
abbrev repeats : ProtocolSpecD Unit := { toy with act := fun _ _ _ => some false }

abbrev repeatRun : D.Run (Fin 1) repeats where
  honest := {0}
  horizon := 1
  events := [.tick 0 0, .tick 0 1]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem repeat_rejected : ¬ EmitOnceUnder env repeatRun () := by
  intro h
  have heq := h 0 (by simp) false 0 1 0 1 rfl rfl (by decide) (by decide)
  exact (by decide : (0 : Nat) ≠ 1) heq

end AvailableChain.Gen.V2.Duty.Tests

#print axioms AvailableChain.Gen.V2.Duty.Tests.no_single_duty
#print axioms AvailableChain.Gen.V2.Duty.Tests.send_once
#print axioms AvailableChain.Gen.V2.Duty.Tests.uniqueness_consumer
#print axioms AvailableChain.Gen.V2.Duty.Tests.repeat_rejected
