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
private abbrev env : Generic.Env Nat :=
  ⟨1, by decide, 0, by decide, fun x t => decide (t = 6 ∨ (x = 7 ∧ t = 16))⟩
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

private theorem row_identity {j r x : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt reads env run timing j x r a) :
    j = 0 ∧ x = 9 ∧ r = 0 ∧ a = row := by
  obtain ⟨_, hj, ha⟩ := h
  have hjlt : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · have hx : x = 9 := by
      have he := congrArg (fun e => e.map V2.Event.node) hj
      exact Option.some.inj he.symm
    have ht : timing.action r = 6 := by
      have he := congrArg (fun e => e.map V2.Event.time) hj
      exact Option.some.inj he.symm
    have hr : r = 0 := by change 8 * (r : Int) + 6 = 6 at ht; omega
    subst x r
    change reads.encode a ∈ [reads.encode row] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    exact ⟨rfl, rfl, rfl, Sum.inl.inj he⟩
  · change reads.encode a ∈ [] at ha
    cases ha
  · change reads.encode a ∈ [⟨.seat 16 0, .inr child⟩] at ha
    have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
    cases he

#print axioms row_identity

/-- The sole missing old premise is a row at honest nonholder 7. -/
private theorem nonholder_source_rejected :
    (¬ PromotionSourceAt core reads env run obs timing iface wire 1 0 1 .genesis 4 child) ∧
    (∀ j r a, ¬ HonestRowAt reads env run timing j 7 r a) ∧
    (∀ j t a, run.events[j]? = some (.tick 7 t) →
      reads.encode a ∉ V2.D.Run.emitsAt env run j) := by
  have hn (j r a) (h : HonestRowAt reads env run timing j 7 r a) : False := by
    have hx := (row_identity h).2.1
    omega
  refine ⟨?_, hn, ?_⟩
  · intro h
    obtain ⟨j, r, a, _, hr, _⟩ := h.rows 7 (by decide)
    exact hn j r a hr
  · intro j t a hj ha
    have hjlt : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j
    · have he := congrArg (fun e => e.map V2.Event.node) hj
      have hx : (9 : Nat) = 7 := Option.some.inj he
      omega
    · change reads.encode a ∈ [] at ha
      cases ha
    · change reads.encode a ∈ [⟨.seat 16 0, .inr child⟩] at ha
      have he := congrArg V2.Signed.payload (List.mem_singleton.mp ha)
      cases he

#print axioms nonholder_source_rejected

private theorem proposal_unique {s : Slot} {X : FGBlock (Fin 1)}
    (h : HonestProposal env run iface s (erase X)) : s = 4 ∧ X = child := by
  obtain ⟨_, o, ⟨j, hj, ho⟩, hb⟩ := h
  have hjlt : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · have ht : (6 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · change o ∈ [] at ho
    cases ho
  · have ht : (16 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    have hs : s = 4 := by
      apply Int.ofNat_injective
      change (s : Int) = 4
      linarith only [ht]
    change o ∈ [⟨.seat 16 0, .inr child⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact ⟨hs, erase_injective (Option.some.inj hb).symm⟩

#print axioms proposal_unique

private theorem fold_premises_sat : ProgressFoldAdvance ef height 4 := by
  have m9transition_progress (σ : ChainState (Fin 1)) (B : FGBlock (Fin 1))
      (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : ef.IsQuorum S)
      (hcover : ∀ i ∈ S, i ∈ σ.progress ∨
        ∃ a ∈ rs, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true)
      (hmature : σ.T_h.slot + cfg.timeoutDelay ≤ B.slot) :
      (transition ef cfg σ B rs).h = σ.h + 1 := by
    have hfold (rows : List (Row (Fin 1))) (σ : ChainState (Fin 1)) (i : Fin 1)
        (hi : i ∈ σ.progress ∨
          ∃ a ∈ rows, a.signer = i ∧ a.height_pair.matchesEntry σ.h σ.T_h.root = true) :
        i ∈ (rows.foldl process_row σ).progress := by
      induction rows generalizing σ with
      | nil => simpa using hi
      | cons a rows ih =>
          apply ih
          rw [(process_row_fields σ a).2.2.1, (process_row_fields σ a).2.2.2.1]
          rcases hi with hi | ⟨b, hb, hbi, hm⟩
          · left
            rw [process_row_progress]
            split_ifs
            · exact Finset.mem_insert_of_mem hi
            · exact hi
          · rcases List.mem_cons.mp hb with rfl | hb
            · left
              rw [process_row_progress, ite_eq_left hm]
              exact Finset.mem_insert.mpr (Or.inl hbi.symm)
            · exact Or.inr ⟨b, hb, hbi, hm⟩
    have hq : ef.IsQuorum (foldRows σ B rs).progress :=
      isQuorum_of_subset ef hS (fun i hi => hfold rs { σ with s := B.slot } i (hcover i hi))
    have hp : progReady ef cfg (afterFin ef (foldRows σ B rs)) = true := by
      simp only [progReady, Bool.or_eq_true, Bool.and_eq_true]
      right
      constructor
      · simpa only [afterFin_T_h, afterFin_s, (foldRows_fields σ B rs).2.2.1,
          foldRows_s, decide_eq_true_eq] using hmature
      · change decide (ef.q ≤ ef.weightOf (afterFin ef (foldRows σ B rs)).progress) = true
        rw [decide_eq_true_eq, afterFin_progress]
        exact hq
    change (process_height_events ef cfg (foldRows σ B rs)).h = σ.h + 1
    rw [process_height_events_eq]
    have hh := (afterFin_h ef (foldRows σ B rs)).trans (foldRows_fields σ B rs).2.1
    split_ifs with ht
    · exact congrArg (· + 1) hh
    · exact congrArg (· + 1) hh
  have m9progress_of_cover (hb : HeightBridge ef cfg height)
      (p : FGBlock (Fin 1)) (s : Slot) (r_s : BlockId) (x : Nat)
      (rs : List (Row (Fin 1))) (S : Finset (Fin 1)) (hS : ef.IsQuorum S)
      (hcover : ∀ i ∈ S, i ∈ (height p).progress ∨
        ∃ a ∈ rs, a.signer = i ∧
          a.height_pair.matchesEntry (height p).h (height p).T_h.root = true)
      (hmature : (height p).T_h.slot + cfg.timeoutDelay ≤ s) :
      (height (.node p s r_s x rs)).h = (height p).h + 1 := by
    have heq : ∀ B, height B = heightOf (derive ef cfg B) := hb
    simp only [heq, heightOf_def] at hcover hmature ⊢
    exact m9transition_progress (derive ef cfg p) (.node p s r_s x rs) rs S hS hcover hmature
  intro y U X hX hU hUX hc hm
  have hb := KitFG.Window.windowHeightBridge ef cfg 2 (by decide)
  have laws := heightLaws_of_bridge ef cfg _ hb
  have hlow := laws.h_mono hUX
  change (height U).h ≤ (height X.parent).h at hlow
  rw [hU.1] at hlow
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s root x rs =>
    change y ≤ (height P).h at hlow
    by_cases hP : (height P).h = y
    · have hT : (height P).T_h = U :=
        (laws.entry_plateau hUX (hU.1.trans hP.symm)).symm.trans hU.2
      obtain ⟨S, hS, hcov⟩ := hc hP
      have hh := m9progress_of_cover hb P s root x rs S hS (by
          intro i hi
          rcases hcov i hi with hbit | ⟨a, ha, hs, timeout, hp⟩
          · exact Or.inl hbit
          · refine Or.inr ⟨a, ha, hs, ?_⟩
            rw [hp]
            change decide (y = (height P).h ∧ U.root = (height P).T_h.root) = true
            simp only [hP, hT, and_self, decide_true]) (by
          change (height P).T_h.slot + 4 ≤ s
          rw [hT]
          exact hm)
      change (height (.node P s root x rs)).h = (height P).h + 1 at hh
      rw [hh, hP]
    · have hPX := laws.h_mono (preceq_parent_node P s root x rs)
      change (height P).h ≤ (height (.node P s root x rs)).h at hPX
      simp only [Height] at *
      omega

#print axioms fold_premises_sat
end AvailableChain.FGCompose.Tests.PopulationAge
end
