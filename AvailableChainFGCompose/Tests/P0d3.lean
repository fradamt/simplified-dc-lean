module
public import AvailableChainFGCompose.Proofs.Healing.CommonEntry
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGCompose.Proofs.Healing.PromotionRows

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d3
open AvailableChain.SimplexFG AvailableChain.KitFG

-- An inhabited interface trace. This is not an ExecutionValid protocol fixture.
private noncomputable abbrev d3_row : Row (Fin 1) :=
  ⟨0, .vote 1 genesisRoot false, some ⟨0, genesisRoot⟩⟩
private noncomputable abbrev d3_protocol : V2.ProtocolSpecD Unit where
  State := List (Row (Fin 1))
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := List (Row (Fin 1))
  init := []
  clock st _ := st
  actTime s := (s : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs; subst s; exact Int.toNat_of_nonneg ht
      · intro hs; subst t; simp
    · next ht =>
      constructor
      · intro hm; cases hm
      · intro hs; exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ _ _ := none
  gossip _ _ := [d3_row]
  process st o := o.payload :: st
  selfVisible _ := false
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable abbrev d3_env : Generic.Env Unit :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private noncomputable abbrev d3_trace : V2.D.Run Unit d3_protocol where
  honest := {()}
  horizon := 40
  events := [.tick () 6, .tick () 8, .deliver () ⟨.none, d3_row⟩ 8]
  seatOf _ _ := ()
  input _ _ := ()
private noncomputable abbrev d3_clock : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private theorem d3_clock_laws : FGTimingLaws d3_clock where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := by simp
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by dsimp; ring
private noncomputable abbrev d3_core : FGCoreReads d3_protocol 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨{.genesis}, .genesis, .genesis, 0, 1⟩, [], st⟩
  erase _ := .genesis
  source _ := some .genesis
  headVote _ _ := .genesis
  finalityHead _ := some .genesis
  proposalFG _ _ := none
private noncomputable abbrev d3_safety : FGSafetyReads d3_protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some .genesis, ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private noncomputable abbrev d3_height : FGHeightView (Fin 1) :=
  fun _ => ⟨.genesis, 0, 1, .genesis, ∅, ∅, 0, .genesis⟩
private noncomputable abbrev d3_electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private theorem d3_height_laws : FGHeightLaws d3_electorate d3_height where
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

private theorem d3_source :
    actionSourceFG d3_core d3_env d3_trace d3_clock () 0 = some (some .genesis) := by
  decide +kernel
private theorem d3_sent : HonestRowAt d3_safety d3_env d3_trace d3_clock 0 () 0 d3_row := by
  refine ⟨by decide +kernel, rfl, ?_⟩
  change (⟨.none, d3_row⟩ : d3_protocol.Object) ∈ [⟨.none, d3_row⟩]
  exact List.mem_singleton_self _
private theorem d3_sources : ∀ x K, x ∈ d3_trace.honest →
    actionSourceFG d3_core d3_env d3_trace d3_clock x 0 = some (some K) →
    FGBlock.Preceq .genesis K ∧ (d3_height K).h ≤ 1 := by
  intro x K _ _
  exact ⟨genesis_preceq K, le_rfl⟩
private theorem d3_high_entry : OpeningEntry d3_core d3_env d3_trace d3_height d3_clock 0 1 :=
  common_entry_at_high d3_core d3_env d3_trace d3_height d3_clock
    d3_electorate d3_height_laws d3_sources rfl
private theorem d3_low_branch :
    OpeningEntry d3_core d3_env d3_trace d3_height d3_clock 0 (2 - 1) := by
  rcases common_low_or_high d3_core d3_env d3_trace d3_height d3_clock
      d3_electorate d3_height_laws 0 2 .genesis rfl
      (fun x K hx hK => ⟨(d3_sources x K hx hK).1, by change 1 ≤ (2 : Nat); decide⟩) with low | high
  · exact low
  · obtain ⟨x, K, _, _, hh⟩ := high
    change 1 = 2 at hh
    contradiction
private theorem d3_covered : OpeningCovered d3_core d3_safety d3_env d3_trace
    d3_height d3_clock Row.height_pair 0 .genesis := by
  intro x _
  cases x
  exact ⟨.genesis, [], 0, 0, d3_row, by decide +kernel, d3_source,
    by decide, by decide, le_rfl, d3_sent, rfl⟩
private theorem d3_fixed_batch : ∃ U, EntryAt d3_height U 1 ∧
    FixedRows d3_core d3_safety d3_env d3_trace d3_height d3_clock
      Row.height_pair 0 1 .genesis U := by
  apply healing_promotion_fixed_rows d3_core d3_safety d3_env d3_trace d3_height
    d3_clock Row.height_pair d3_electorate d3_height_laws
    (by simp) d3_high_entry d3_covered
  · intro x y K L hx hy hK hL he; rfl
  · intro x K hx hK
    cases x
    have he : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans d3_source))
    subst K
    exact le_rfl

-- The fixed row retains its finality field; a different height pair cannot replace it.
private theorem d3_fixed_identity : NamesEntry Row.height_pair .progress d3_row 1
    (.genesis : FGBlock (Fin 1)) ∧ d3_row.finality_pair = some ⟨0, genesisRoot⟩ :=
  ⟨⟨false, rfl⟩, rfl⟩
private theorem d3_reject_replacement : ¬ NamesEntry Row.height_pair .progress
    ({d3_row with height_pair := .vote 2 genesisRoot false}) 1
      (.genesis : FGBlock (Fin 1)) := by
  rintro ⟨timeout, h⟩
  cases h
private theorem d3_reject_parent : ¬ FGBlock.Preceq
    (.node .genesis 1 ⟨7⟩ 0 [] : FGBlock (Fin 1)) .genesis := by decide

-- Delivery at the deadline is absent from the strict read; the next read holds that row.
private theorem d3_strict_receipt :
    ¬ HeldBefore d3_core d3_env d3_trace (fun _ => []) () d3_row 8 ∧
      HeldBefore d3_core d3_env d3_trace (fun _ => []) () d3_row 9 := by
  change ¬ (d3_row ∈ ([] : List (Row (Fin 1))) ∨ d3_row ∈ []) ∧
    (d3_row ∈ [d3_row] ∨ d3_row ∈ [])
  decide +kernel
private theorem d3_strict_deadline : PromotionRowDeadlineStrict d3_env d3_clock 1 0 0 4 :=
  healing_promotion_row_deadline_strict d3_clock d3_clock_laws d3_env
    (by decide) ⟨by decide⟩ (by decide) (by decide) (by decide)
private theorem d3_reject_deadline_equality : ¬ ((0 + 1 : Time) * FGCompose.P d3_clock <
    d3_clock.proposal 2) := by decide

private noncomputable abbrev d3_window : Window.State (Fin 1) :=
  { Window.initial with h := 3, W := [⟨1, .genesis, ∅⟩] }
private noncomputable abbrev d3_stale : Row (Fin 1) :=
  ⟨0, .vote 2 genesisRoot false, some ⟨1, genesisRoot⟩⟩
private theorem d3_finality_useful : Window.heightMatch d3_window d3_stale = false ∧
    Window.r6w d3_window d3_stale = true := by decide
private theorem d3_reject_finality_mismatch : Window.r6w d3_window
    ({d3_stale with finality_pair := some ⟨1, ⟨9⟩⟩}) = false := by decide

private noncomputable abbrev d3_interface : V2.D.Interface d3_protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := some .genesis
  opening _ := True
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h
private noncomputable abbrev d3_child : FGBlock (Fin 1) := .node .genesis 2 ⟨7⟩ 0 []
private noncomputable abbrev d3_parent (_ : List (Row (Fin 1))) (_ : Block) :=
  some (.genesis : FGBlock (Fin 1))
private noncomputable abbrev d3_parent_height (_ : List (Row (Fin 1))) (_ : Slot)
    (_ : FGBlock (Fin 1)) := (1, genesisRoot)
private noncomputable abbrev d3_valid (_ : List (Row (Fin 1))) (_ : Slot)
    (_ : FGBlock (Fin 1)) (a : Row (Fin 1)) := Window.r6w Window.initial a
private noncomputable abbrev d3_fold (_ : List (Row (Fin 1))) (_ : Slot)
    (_ : FGBlock (Fin 1)) : Window.State (Fin 1) := Window.initial
private theorem d3_parent_transfer :
    ValidForParent d3_env d3_trace d3_interface d3_parent d3_valid
      d3_child.slot (d3_core.erase d3_child) d3_row ∧
    HeightMatch d3_env d3_trace d3_interface (fun a => namedEntry a.height_pair)
      d3_parent d3_parent_height d3_child.slot (d3_core.erase d3_child) d3_row := by
  exact p0d3_same_row d3_core d3_safety d3_env d3_trace d3_height d3_interface
    Row.height_pair d3_parent d3_parent_height d3_valid d3_fold
    d3_electorate d3_height_laws (s := 2) (nd := []) (U := .genesis)
    rfl ⟨rfl, rfl⟩ (preceq_refl _) rfl (by decide +kernel) rfl ⟨rfl, rfl⟩ rfl
    ⟨d3_row, rfl, rfl⟩ ⟨false, rfl⟩ rfl

#print axioms d3_parent_transfer
#print axioms d3_height_laws
#print axioms d3_source
#print axioms d3_sent
#print axioms d3_high_entry
#print axioms d3_low_branch
#print axioms d3_fixed_batch
#print axioms d3_fixed_identity
#print axioms d3_reject_replacement
#print axioms d3_reject_parent
#print axioms d3_strict_receipt
#print axioms d3_strict_deadline
#print axioms d3_reject_deadline_equality
#print axioms d3_finality_useful
#print axioms d3_reject_finality_mismatch

end AvailableChain.FGCompose.Tests.P0d3
end
