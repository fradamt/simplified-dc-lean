module
public import AvailableChainFGCompose.Proofs.Population.Seats

set_option linter.privateModule false

noncomputable section
public section

/-! Pure seat/count controls. No execution or client producer is claimed here. -/
namespace AvailableChain.FGCompose.Tests.PopulationCounts
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev protocol (n : Nat) : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => n
  Payload := Unit
  Durable := Unit
  init := ()
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False
private abbrev reads (n : Nat) : FGSafetyReads (protocol n) n Unit where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun _ => ⟨.none, ()⟩
  decode := fun _ => none
  decodeObject := fun _ => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, genesisRoot, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis
private abbrev run {V : Type} (n : Nat) (holder : Fin n → V) (honest : Finset V) :
    V2.D.Run V (protocol n) where
  honest := honest
  horizon := 20
  events := []
  seatOf := fun _ => holder
  input := fun _ _ => ()
private abbrev electorate (n : Nat) : Electorate (Fin n) :=
  ⟨fun _ => 1, fun _ => by decide⟩
private abbrev before := run 1 (fun _ => (9 : Fin 11)) {7, 9}
private abbrev extra := run 1 (fun _ => (9 : Fin 12)) {7, 9}
private abbrev faultySeat := run 1 (fun _ => (11 : Fin 12)) {7, 9}
private abbrev four := run 4 (fun i => i.val + 9) {7, 9, 10}
private abbrev frozen := run 4 (fun i : Fin 4 => i) {0, 1, 2}

private theorem counts_premises_sat :
    before.honest = {7, 9} ∧ extra.honest = {7, 9} ∧
    faultySeat.honest = {7, 9} ∧ four.honest = {7, 9, 10} ∧
    Function.Injective (safetyHolder (reads 4) four) ∧
    FGSafetyUnitLaws (electorate 4) ∧
    (∀ i, safetyHolder (reads 4) frozen i = (Equiv.refl (Fin 4)) i) ∧
    (Gen.V2.Duty.faulty frozen).card ≤ (4 - 1) / 3 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, fun _ => rfl, by decide⟩
  · intro i j h
    apply Fin.ext
    change i.val + 9 = j.val + 9 at h
    omega
  · exact ⟨by decide, by decide, fun A => by simp [Electorate.weightOf], by decide⟩

end AvailableChain.FGCompose.Tests.PopulationCounts
end
