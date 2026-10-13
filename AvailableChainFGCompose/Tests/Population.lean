module
public import AvailableChainFGCompose.Proofs.Population.Seats
public import AvailableChainFGCompose.Proofs.Population.Safety
public import AvailableChainFGCompose.Proofs.HolderClient

set_option linter.privateModule false

noncomputable section
public section

/-! Generic ordinary-event-fold controls, not concrete PC executions.
One FG holder (9), an honest nonholder (7), and a real signed release followed by a
malformed unsigned release. Both honest nodes remain in every safety conclusion. -/

namespace AvailableChain.FGCompose.Tests.Population
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate (n : Nat) : Electorate (Fin n) :=
  ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev head : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := RecordOnce
  Label := Time
  Duty := Time
  signLabel := id
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := RecordOnce
  init := RecordOnce.initial
  clock := fun st _ => st
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun st _ _ => (createRowOnce (electorate 1) cfg st 0 (some .genesis) head).1
  gossip := fun _ _ => [row]
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st o => match o.auth with
    | .none => st
    | .seat _ _ => record_row_once st o.payload
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev wire : protocol.Object := ⟨.seat 6 0, row⟩
private abbrev raw : protocol.Object := ⟨.none, row⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with
  | .seat l _ => if l = 6 then some o.payload else none
  | .none => none
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := id
  inputs := fun _ => (some .genesis, head)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis
private abbrev env : Generic.Env Nat where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 20
  events := [.tick 9 6, .tick 7 7]
  seatOf := fun _ _ => 9
  input := fun _ _ => ()
private abbrev selection : FGSelectionReads protocol 1 where
  select := fun _ => (some .genesis, some .genesis)
  clientInputs := reads.inputs

private theorem mixed_client_premises_sat :
    FGHolderClientLaws reads (electorate 1) cfg env run (ordinaryFGExecutionObs env run)
      (safetyHolder reads run) where
  holder_eq _ := rfl
  holder_inj _ _ _ := Subsingleton.elim _ _
  initial_record := rfl
  record_step x k hk := by
    change k < 6 at hk
    by_cases h9 : x = 9
    · subst x; interval_cases k <;> rfl
    by_cases h7 : x = 7
    · subst x; interval_cases k <;> rfl
    interval_cases k <;>
      simp [ordinaryFGExecutionObs, ordinaryCutState, ordinaryEntry, ordinaryEntryStep,
        ordinaryReleaseStep, V2.D.Run.stateBefore, V2.D.World.step,
        V2.D.World.init, V2.D.tick, V2.D.Run.ownSeats, V2.ProtocolSpecD.objSelfVisible,
        protocol, run, env, reads, h9, h7, Ne.symm h9, Ne.symm h7]
  holder_rows j x t i ht hi := by
    have hx : x = 9 := hi.symm
    subst hx
    have hj : j < 2 := (List.getElem?_eq_some_iff.mp ht).1
    interval_cases j
    · have ht' : t = 6 := by simpa [safetyHolder, reads, run] using ht.symm
      subst t
      have hi' : i = 0 := Subsingleton.elim _ _
      subst i
      decide
    · simp at ht
  nonholder_rows j x t ht hn := by
    have hj : j < 2 := (List.getElem?_eq_some_iff.mp ht).1
    interval_cases j
    · have hx : x = 9 := by simpa [V2.Event.node] using
        (congrArg V2.Event.node (Option.some.inj ht)).symm
      exact False.elim (hn 0 hx.symm)
    · have hxt : x = 7 ∧ t = 7 := by simpa using ht.symm
      rcases hxt with ⟨rfl, rfl⟩
      decide

private theorem mixed_wire_premises_sat : FGSafetyWireLaws reads where
  encode_injective := Function.injective_id
  decode_encode _ := rfl
  decode_auth a u hd := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => cases hd
    | seat l i =>
      change (if l = 6 then some payload else none) = some u at hd
      split_ifs at hd with hl
      · subst l
        have hu : payload = u := Option.some.inj hd
        subst u
        exact congrArg (V2.Auth.seat 6) (Subsingleton.elim i payload.signer)
  decoded_visible o u hd := by
    rcases o with ⟨auth, payload⟩
    cases auth with
    | none => cases hd
    | seat l i => rfl
  carried _ _ ha := False.elim (List.not_mem_nil ha)

private theorem mixed_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 20 ∧
    run.events = [.tick 9 6, .tick 7 7] ∧
    FGSafetyUnitLaws (electorate 1) ∧
    FGSelectionClientLaws selection reads ∧
    FGHolderClientLaws reads (electorate 1) cfg env run (ordinaryFGExecutionObs env run)
      (safetyHolder reads run) ∧ FGSafetyWireLaws reads ∧
    FGHonestSeats reads run = {0} ∧ historyFaulty reads run = ∅ ∧
    V2.D.Run.emitsAt env run 0 = [wire, raw] ∧
    V2.D.Run.emitsAt env run 1 = [raw] ∧ reads.decode raw = none := by
  refine ⟨rfl, rfl, rfl, ?_, ⟨fun _ => rfl⟩, mixed_client_premises_sat,
    mixed_wire_premises_sat, ?_, ?_, ?_, ?_, rfl⟩
  · exact ⟨by decide, by decide,
      fun A => by simp [Electorate.weightOf], by decide⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · ext i
    simp [historyFaulty, safetyHolder]
  · decide
  · decide

end AvailableChain.FGCompose.Tests.Population
end
