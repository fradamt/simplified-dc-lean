module
public import AvailableChainFGCompose.Proofs.Population.PromotionRows
public import AvailableChainFGCompose.Proofs.Population.PromotionBridges

set_option linter.privateModule false

noncomputable section
public section

/-! Generic ordinary-event-fold controls. These are not concrete PC executions.
The FG label is 6; seat 0 belongs to 9. Honest nonholder 7 also has an action cut
and later carrier cuts, but never emits an encoded FG wire. -/
namespace AvailableChain.FGCompose.Tests.PopulationPromotion
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

private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with
  | .seat l _ => if l = 6 then some o.payload else none
  | .none => none
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun a => ⟨.seat 6 0, a⟩
  decode := some
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
  events := [.tick 9 6, .tick 7 6, .tick 7 8, .tick 7 12]
  seatOf := fun l _ => if l = 6 then 9 else 7
  input := fun _ _ => ()
private noncomputable abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private abbrev core : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), Store.init, [], []⟩
  erase := fun _ => .genesis
  source := fun _ => some .genesis
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => some .genesis
  proposalFG := fun _ _ => none
private noncomputable abbrev height : FGHeightView (Fin 1) :=
  fun _ => ⟨.genesis, 0, 1, .genesis, ∅, ∅, 0, .genesis⟩
private theorem height_premises_sat : FGHeightLaws (electorate 1) height where
  one_le_h _ := by change 1 ≤ (1 : Nat); decide
  h_mono _ := le_rfl
  node_cases _ _ _ _ _ := Or.inl ⟨rfl, rfl⟩
  entry_preceq B := genesis_preceq B
  entry_same_height _ := rfl
  entry_idem _ := rfl
  entry_plateau _ _ := rfl
  justified_preceq_entry _ := preceq_refl _
  justified_below_height _ := by change 0 < (1 : Nat); decide
  target_sub_progress _ := Finset.Subset.refl _
  target_origin _ _ hi := False.elim (Finset.notMem_empty _ hi)
  progress_origin _ _ hi := False.elim (Finset.notMem_empty _ hi)
  height_crossing _ y hy hlo := by
    change y < 1 at hlo
    exact ((Nat.not_lt_of_ge hy) hlo).elim
  justification_certificate _ hn := False.elim (hn rfl)


#print axioms height_premises_sat

private theorem mixed_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 20 ∧
    run.events = [.tick 9 6, .tick 7 6, .tick 7 8, .tick 7 12] ∧
    (∀ i, safetyHolder reads run i = 9) ∧ FGHonestSeats reads run = {0} ∧
    protocol.objSelfVisible (reads.encode row) = true ∧
    reads.decodeObject (reads.encode row) = some row ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    (∀ x ∈ run.honest,
      actionSourceFG core env run timing x 0 = some (some .genesis)) ∧
    OpeningEntry core env run height timing 0 1 ∧
    OpeningCoveredFG core reads env run height timing Row.height_pair
      (FGHonestSeats reads run) 0 .genesis := by
  refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · unfold HonestRowAt
    decide +kernel
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · exact ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  · intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨.genesis, RecordOnce.initial, 0, 0, row, ?_, ?_, ?_, ?_, le_rfl, ?_, rfl⟩
    · rfl
    · decide +kernel
    · decide
    · decide
    · unfold HonestRowAt
      decide +kernel

#print axioms mixed_premises_sat

private theorem geometry_premises_sat :
    (∀ x y K L, x ∈ run.honest → y ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) →
      actionSourceFG core env run timing y 0 = some (some L) →
      (height K).T_h.root = (height L).T_h.root → (height K).T_h = (height L).T_h) ∧
    (∀ x K, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) → K.slot ≤ 0 * timing.roundSlots) ∧
    (∀ x K U, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) → FGBlock.Preceq U K →
      U.slot ≤ K.slot) := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ => rfl, ?_, ?_⟩
  · intro x K hx hK
    have he := mixed_premises_sat.2.2.2.2.2.2.2.2.1 x hx
    have hk : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans he))
    subst K
    exact le_rfl
  · intro x K U hx hK hUK
    have he := mixed_premises_sat.2.2.2.2.2.2.2.2.1 x hx
    have hk : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans he))
    subst K
    have hu : U = .genesis := by simpa [FGBlock.Preceq, FGBlock.preceq] using hUK
    subst U
    exact le_rfl

#print axioms geometry_premises_sat

end AvailableChain.FGCompose.Tests.PopulationPromotion
end
