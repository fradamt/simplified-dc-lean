module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchAge
public import AvailableChainFGCompose.Proofs.Population.PromotionSourceBridges
public import AvailableChainFGCompose.Proofs.Finality.History

set_option linter.privateModule false

noncomputable section
public section

/-! POP-3 generic ordinary-event-fold controls, not concrete PC execution producers.
The sole FG seat belongs to 9; honest proposer 7 carries its exact row. -/
namespace AvailableChain.FGCompose.Tests.PopulationAge
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev ef : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev child : FGBlock (Fin 1) := .node .genesis 4 ⟨41⟩ 0 [row]
private def erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (erase p) s r (encFGBody x rs)
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Unit
  Label := Time
  Duty := Time
  signLabel := id
  seats := fun _ => 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
  Durable := Unit
  init := ()
  clock := fun st _ => st
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun _ t _ => if t = 6 then some (.inl row)
    else if t = 16 then some (.inr child) else none
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
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun a => ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject := fun o => match o.auth with
    | .seat l _ => if l = 6 then o.payload.getLeft? else none
    | .none => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (some .genesis, ⟨0, genesisRoot, 0⟩)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis
private abbrev env : Generic.Env Nat := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 30
  events := [.tick 9 6, .tick 7 6, .tick 7 16]
  seatOf := fun l _ => if l = 6 then 9 else 7
  input := fun _ _ => ()
private abbrev timing : FGTiming where
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
  core _ := ⟨(), ⟨{.genesis, child}, .genesis, .genesis, 1, 1⟩, [], [row]⟩
  erase := erase
  source := fun _ => some .genesis
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => some .genesis
  proposalFG := fun _ _ => none
private abbrev height := Window.certificateHeight ef cfg 2
private abbrev obs : FGObservationReads core where
  height := height
  finality := Window.certificateFinality ef cfg 2
  controls nd := treeStoreControlsView height (core.core nd).fg
  viable nd X := treeStoreFrameView height (core.core nd).fg X
private abbrev iface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_injective (mul_left_cancel₀ (by decide : (4 : Int) ≠ 0) h)
  block := fun p => match p with | .inr X => some (erase X) | .inl _ => none
private abbrev wire : FGHistoryWireReads reads where
  signer := fun a => some a.signer
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  decode_finality := by intro a b h; cases h; rfl
  decode_signer := by intro a b h; cases h; rfl
  decode_height := by intro a b h; cases h; rfl
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inr X => some (X.slot, X) | .inl _ => none
private abbrev parentFG (_ : Unit) (_ : Block) : Option (FGBlock (Fin 1)) := some .genesis
private abbrev fold (_ : Unit) (_ : Slot) (P : FGBlock (Fin 1)) := Window.derive ef cfg 2 P
private abbrev parentHeight (nd : Unit) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((fold nd s P).h, (fold nd s P).T_h.root)
private abbrev validFor (nd : Unit) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  Window.r6w (fold nd s P) a

private theorem erase_injective : Function.Injective erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [erase] at h
    | node q t u y ts =>
      simp only [erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

#print axioms erase_injective

private theorem source_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 30 ∧
    run.events = [.tick 9 6, .tick 7 6, .tick 7 16] ∧
    (∀ i, safetyHolder reads run i = 9) ∧ FGHonestSeats reads run = {0} ∧
    protocol.objSelfVisible (reads.encode row) = true ∧
    reads.decodeObject (reads.encode row) = some row ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    V2.D.proposerOf run iface 4 = 7 ∧
    HonestCarrier env run iface (kernelCarrier decodeProposal erase FGBlock.rows)
      4 (erase child) [row] ∧
    (∀ x ∈ run.honest,
      actionSourceFG core env run timing x 0 = some (some .genesis)) ∧
    PromotionSourceAtFG core reads env run obs timing iface wire
      (FGHonestSeats reads run) 1 0 1 .genesis 4 child := by
  have hp : HonestProposal env run iface 4 (erase child) := by
    refine ⟨⟨by decide, by decide⟩, ⟨.seat 16 0, .inr child⟩,
      ⟨2, by decide +kernel, by decide +kernel⟩, rfl⟩
  have hr : HonestRowAt reads env run timing 0 9 0 row := by
    unfold HonestRowAt
    decide +kernel
  refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_, rfl, rfl, hr, rfl, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · exact ⟨hp, ⟨.seat 16 0, .inr child⟩,
      ⟨2, by decide +kernel, by decide +kernel⟩, child, rfl, rfl, rfl⟩
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · refine ⟨⟨rfl, rfl⟩, preceq_refl _, hp, rfl, by decide,
      by decide, by decide, by decide, ?_⟩
    intro i _
    exact ⟨0, 0, row, le_rfl, hr, false, rfl⟩

#print axioms source_premises_sat
end AvailableChain.FGCompose.Tests.PopulationAge
end
