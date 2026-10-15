module
public import AvailableChainFGCompose.Proofs.Population.Kernel
public import AvailableChainFGCompose.Proofs.Population.KernelBridges

set_option linter.privateModule false
noncomputable section
public section

/-! Generic ordinary event-fold controls for the full selected middle and action records.
The mixed run has both honest receivers; FG label 0 belongs only to holder 9. -/
namespace AvailableChain.FGCompose.Tests.PopulationKernel
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev row0 : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev aBlock : FGBlock (Fin 1) := .node .genesis 2 ⟨1⟩ 0 [row0]
private abbrev row1 : Row (Fin 1) := ⟨0, .vote 2 aBlock.root false, none⟩
private abbrev bBlock : FGBlock (Fin 1) := .node aBlock 4 ⟨2⟩ 0 [row1]
private abbrev row2 : Row (Fin 1) := ⟨0, .vote 3 bBlock.root false, none⟩
private abbrev dBlock : FGBlock (Fin 1) := .node bBlock 6 ⟨3⟩ 0 [row2]
private abbrev row3 : Row (Fin 1) := ⟨0, .vote 4 dBlock.root false, some ⟨3, bBlock.root⟩⟩
private abbrev xBlock : FGBlock (Fin 1) := .node dBlock 8 ⟨4⟩ 0 [row3]
private abbrev storeA := SimplexFG.Window.on_block electorate cfg 2 Store.init aBlock
private abbrev storeB := SimplexFG.Window.on_block electorate cfg 2 storeA bBlock
private abbrev storeD := SimplexFG.Window.on_block electorate cfg 2 storeB dBlock
private abbrev storeX := SimplexFG.Window.on_block electorate cfg 2 storeD xBlock
private abbrev staged (t : Time) : Store (Fin 1) :=
  { (if t < 16 then storeA else if t < 24 then storeB else if t < 32 then storeD else storeX)
    with TF := if t < 16 then {.genesis, aBlock} else
      if t < 24 then {.genesis, aBlock, bBlock} else
      if t < 32 then {.genesis, aBlock, bBlock, dBlock} else
      {.genesis, aBlock, bBlock, dBlock, xBlock} }
private def erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r b rows => .node (erase p) s r (encFGBody b rows)
private abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * s
  vote s := 4 * s + 1
  early s := 4 * s + 2
  freeze s := 4 * s + 3
  release s := 4 * s + 5
  gate s := 4 * s + 6
  action r := 4 * (r * 2 : Nat) + 6
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Time
  Label := Nat
  Duty := Time
  signLabel t := if t % 8 = 6 then 0 else t.toNat + 1
  seats _ := 1
  Payload := FGBlock (Fin 1) ⊕ Row (Fin 1)
  Durable := Time
  init := 0
  clock st t := max st t
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inr row0) else
    if t = 14 then some (.inr row1) else if t = 22 then some (.inr row2) else
    if t = 30 then some (.inr row3) else if t = 8 then some (.inl aBlock) else
    if t = 16 then some (.inl bBlock) else if t = 24 then some (.inl dBlock) else
    if t = 32 then some (.inl xBlock) else none
  gossip _ _ := []
  process st _ := st
  selfVisible _ := true
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev wire (row : Row (Fin 1)) : protocol.Object := ⟨.seat 0 0, .inr row⟩
private abbrev prop (X : FGBlock (Fin 1)) : protocol.Object :=
  ⟨.seat (4 * X.slot + 1) 0, .inl X⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.payload with | .inl _ => none | .inr row => some row
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase o := match o.payload with | .inl X => some (erase X) | .inr _ => none
  proposalRows o := match o.payload with | .inl X => X.rows.map wire | .inr _ => []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs t := (some (if t < 8 then .genesis else if t < 16 then aBlock else
      if t < 24 then bBlock else dBlock),
    ⟨3, bBlock.root, 0⟩)
  enabled t := decide (t % 8 = 6)
  finalizedOut _ := .genesis
private abbrev source (t : Time) : FGBlock (Fin 1) :=
  if t < 8 then .genesis else if t < 16 then aBlock else
    if t < 24 then bBlock else dBlock
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core t := ⟨(), staged t, [], [wire row0, wire row1, wire row2, wire row3]⟩
  erase := erase
  source t := some (source t)
  headVote _ s := erase (if s = 2 then aBlock else if s = 4 then bBlock else dBlock)
  finalityHead _ := some dBlock
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := KitFG.Window.certificateHeight electorate cfg 2
  finality := KitFG.Window.certificateFinality electorate cfg 2
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X
private abbrev history : FGHistoryWireReads reads where
  heightPair a := (decode a).map (·.height_pair) |>.getD .empty
  finalityPair a := (decode a).bind (·.finality_pair)
  signer a := (decode a).map (·.signer)
  decode_height a u hd := by
    change ((decode a).map (·.height_pair)).getD .empty = u.height_pair
    change decode a = some u at hd
    rw [hd]; rfl
  decode_finality a u hd := by
    change (decode a).bind (·.finality_pair) = u.finality_pair
    change decode a = some u at hd
    rw [hd]; rfl
  decode_signer a u hd := by
    change (decode a).map (·.signer) = some u.signer
    change decode a = some u at hd
    rw [hd]; rfl
private abbrev interface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block o := match o with | .inl X => some (erase X) | .inr _ => none
  opening _ := True
  propLabel s := 4 * s + 1
  propDuty s := 4 * s
  propDuty_label s := by
    change (if (4 * s : Int) % 8 = 6 then 0 else (4 * s : Int).toNat + 1) = 4 * s + 1
    have hn : (4 * s : Int) % 8 ≠ 6 := by omega
    rw [ite_eq_right hn]
    have ht : (4 * s : Int) = ((4 * s : Nat) : Int) := by push_cast; rfl
    rw [ht, Int.toNat_natCast]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * a + 1 = 4 * b + 1 at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (Nat.add_right_cancel h)
private abbrev env (V : Type) : Generic.Env V :=
  ⟨2, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 33
  events := [.tick 9 0, .tick 7 0, .tick 9 2, .tick 7 2, .tick 9 4, .tick 7 4, .tick 9 6,
    .tick 7 6, .tick 9 8, .tick 7 8, .tick 9 10, .tick 7 10, .tick 9 12, .tick 7 12, .tick 9 14,
    .tick 7 14, .tick 9 16, .tick 7 16, .tick 9 18, .tick 7 18, .tick 9 20, .tick 7 20,
    .tick 9 22, .tick 7 22, .tick 9 24, .tick 7 24, .tick 9 26, .tick 7 26, .tick 9 28,
    .tick 7 28, .tick 9 30, .tick 7 30, .tick 9 32, .tick 7 32]
  seatOf label _ := if label = 0 then 9 else 7
  input _ _ := ()
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := Finset.univ
  horizon := 33
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8, .tick 0 10, .tick 0 12,
    .tick 0 14, .tick 0 16, .tick 0 18, .tick 0 20, .tick 0 22, .tick 0 24, .tick 0 26,
    .tick 0 28, .tick 0 30, .tick 0 32]
  seatOf _ _ := 0
  input _ _ := ()
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inl X => some (X.slot, X) | .inr _ => none
private abbrev parentRead (_ : Time) (Q : Block) : Option (FGBlock (Fin 1)) :=
  if Q = erase aBlock then some aBlock else if Q = erase bBlock then some bBlock else
    if Q = erase dBlock then some dBlock else some .genesis
private abbrev parentHeight (_ : Time) (_ : Slot) (X : FGBlock (Fin 1)) : Height × BlockId :=
  ((obs.height X).h, (obs.height X).T_h.root)
private abbrev makeFG (_ : FGBlock (Fin 1)) (Q : Block) (_ : List protocol.Object) :=
  if Q = erase aBlock then aBlock else if Q = erase bBlock then bBlock else
    if Q = erase dBlock then dBlock else xBlock
private abbrev ac (V : Type) : FGACServiceReads V where
  honest _ := True
  proposal _ _ := True
  proposalTime := timing.proposal
  actionHeadLabel r := r * 2 + 1
  actionTime := timing.action
  proposalScope _ _ := True
  sourceScope _ _ _ := True
  actionScope _ _ := True
  actionHead _ _ := some (some (erase dBlock))
  parent _ := some (erase bBlock)
  gateFloor _ _ := some (erase bBlock)
  frame _ _ _ := True
  below := Block.Preceq
  headScope _ _ := True
  gateScope _ _ := True
  voteTime s := timing.vote s
  gateTime s := timing.gate s
  gateLabel r := r * 2
  headAtLabel _ _ := some (erase dBlock)
  gate _ _ := some (some (erase dBlock))
  source _ _ := some (some (erase dBlock))
private abbrev point : FGServicePoint := ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 0⟩
private abbrev pt : KernelPt := ⟨1⟩
private abbrev middleType {V : Type} [DecidableEq V] (rho : V2.D.Run V protocol) :=
  KernelMiddleWitnessFG_W core reads obs timing (env V) rho interface history electorate
    decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) parentRead parentHeight
    (fun _ _ _ _ => true) makeFG (fun _ => true) (ac V) cfg 2 2 point pt (erase aBlock)


private theorem block_premises_sat :
    (obs.height aBlock).h = 2 ∧ (obs.height bBlock).h = 3 ∧
    (obs.height bBlock).T_h = bBlock ∧ (obs.height dBlock).h = 4 ∧
    (obs.height dBlock).J = bBlock ∧ (obs.height dBlock).h_j = 3 ∧
    (SimplexFG.Window.derive electorate cfg 2 dBlock).h_F < 3 ∧
    KitFG.Window.RetainedW electorate cfg 2 dBlock 3 bBlock := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ⟨⟨3, bBlock, ∅⟩, ?_, rfl, rfl⟩⟩
  decide +kernel

#print axioms block_premises_sat

private theorem exact_rows (j x q : Nat) (a : protocol.Object)
    (ha : HonestRowAt reads (env Nat) run timing j x q a) :
    (j = 6 ∧ x = 9 ∧ q = 0 ∧ a = wire row0) ∨
    (j = 14 ∧ x = 9 ∧ q = 1 ∧ a = wire row1) ∨
    (j = 22 ∧ x = 9 ∧ q = 2 ∧ a = wire row2) ∨
    (j = 30 ∧ x = 9 ∧ q = 3 ∧ a = wire row3) := by
  obtain ⟨_, hj, hw⟩ := ha
  have hlen : j < 34 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (6 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (6 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 0 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row0] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inl (⟨rfl, rfl, rfl, hw'⟩)
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (8 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (8 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (14 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (14 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 1 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row1] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩))
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (16 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (16 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (22 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (22 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 2 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row2] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩)))
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (24 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (24 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 9 = x ∧ (30 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (30 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 3 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row3] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl, hw'⟩)))
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : 7 = x ∧ (32 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (32 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega

#print axioms exact_rows

private theorem schedule_premises_sat : V2.D.ScheduleWellFormed (env Nat) run := by
  constructor
  · decide
  · decide +kernel
  · decide +kernel
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals decide
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals decide
  · intro x t hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      or_false] at hm
    rcases hm with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨15, rfl⟩
    · exact ⟨15, rfl⟩
    · exact ⟨16, rfl⟩
    · exact ⟨16, rfl⟩
  · intro x hx t ht _ hhor _
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    obtain ⟨k, hk⟩ := ht
    change t = (k : Time) * 2 at hk
    change t ≤ 33 at hhor
    rw [hk] at hhor
    have hb : k * 2 ≤ 32 := by
      have : (k : Int) * 2 ≤ 33 := by simpa using hhor
      omega
    have hbound : k ≤ 16 := by omega
    subst t
    rcases hx' with rfl | rfl <;> interval_cases k <;> simp

#print axioms schedule_premises_sat

private abbrev batchType {V : Type} [DecidableEq V] (rho : V2.D.Run V protocol)
    (q y : Nat) (U X : FGBlock (Fin 1)) :=
  BatchPrem core reads obs timing (env V) rho interface history electorate decodeProposal
    erase (fun X => X.rows.map wire) (fun _ => []) parentRead parentHeight
    (fun _ _ _ _ => true) 2 .target q y U X

private theorem batch_premises_sat :
    batchType run 1 2 aBlock bBlock ∧ batchType run 2 3 bBlock dBlock := by
  have hweight : electorate.weightOf (historyFaulty reads run) < electorate.q := by
    change (0 : Nat) < 1
    decide
  have receipt : TRowsReceipt core reads (env Nat) run timing (fun _ => []) 2 := by
    intro j x q a ha _ z _
    rcases exact_rows j x q a ha with h | h | h | h
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl (by
        change wire _ ∈ [wire row0, wire row1, wire row2, wire row3]
        decide +kernel)
  have height := KitFG.Window.windowHeightLaws electorate cfg 2 (by decide)
  constructor
  · refine kmid_batchPrem_holder core reads obs timing (env Nat) run interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 1 2 aBlock bBlock (by decide) ?_ 16 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (9 : Nat) ∈ ({7, 9} : Finset Nat); decide
    · refine ⟨[wire row1], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop bBlock, ⟨17, rfl, by decide +kernel⟩, rfl⟩,
        prop bBlock, ⟨17, rfl, by decide +kernel⟩, bBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))), FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨14, 1, wire row1, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
  · refine kmid_batchPrem_holder core reads obs timing (env Nat) run interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 2 3 bBlock dBlock (by decide) ?_ 24 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (9 : Nat) ∈ ({7, 9} : Finset Nat); decide
    · refine ⟨[wire row2], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop dBlock, ⟨25, rfl, by decide +kernel⟩, rfl⟩,
        prop dBlock, ⟨25, rfl, by decide +kernel⟩, dBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))),
            FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row2 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨22, 2, wire row2, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩

#print axioms batch_premises_sat

private theorem mixed_premises_sat : ∃ m : middleType run,
    m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
    m.cD = 6 ∧ m.d = 2 := by
  have first : ∀ j x q a h t, HonestRowAt reads (env Nat) run timing j x q a →
      historyRowHeight reads history a = some h → 3 ≤ h → eventTime run j = some t →
      timing.action 2 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have second : ∀ j x q a h t, HonestRowAt reads (env Nat) run timing j x q a →
      historyRowHeight reads history a = some h → 4 ≤ h → eventTime run j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have noFin : ∀ j x q a h t, HonestRowAt reads (env Nat) run timing j x q a →
      historyFinHeight reads history a = some h → 3 ≤ h → eventTime run j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh _ ht
    rcases exact_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      cases hh
      all_goals exact le_of_eq (Option.some.inj ht)
  have chains : ChainRowsBefore core (env Nat) run aBlock 14 ∧
      ChainRowsBefore core (env Nat) run bBlock 22 ∧
      ChainRowsBefore core (env Nat) run dBlock 30 := by
    refine ⟨?_, ?_, ?_⟩
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl
      · exact ⟨9, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨9, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨9, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨9, 25, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨9, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨9, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
  have capB : ∀ i x W, i ≤ run.events.length → i ≤ afterTicksIdx run 22 →
      HeldAt core (env Nat) run i x W → (obs.height W).h ≤ 3 := by
    intro i x W _ hi ⟨hx, hW⟩
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    have hib : i ≤ 24 := hi
    have ht : V2.D.Run.stateBefore (env Nat) run i x < 24 := by
      rcases hx' with rfl | rfl <;> interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env Nat) run i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
  have capFinal : ∀ i x W, i ≤ afterTicksIdx run 30 → HeldAt core (env Nat) run i x W →
      (obs.height W).h ≤ 4 ∧ (obs.finality W).h_F < 3 := by
    intro i x W hi ⟨hx, hW⟩
    have ht : V2.D.Run.stateBefore (env Nat) run i x < 32 := by
      have hib : i ≤ 32 := hi
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl <;> interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env Nat) run i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env Nat) run i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel
  let m : middleType run := {
    A₀ := aBlock
    B := bBlock
    U := bBlock
    X_D := dBlock
    cD := 6
    d := 2
    opening := ⟨⟨by decide, by decide⟩, prop aBlock, ⟨9, rfl, by decide +kernel⟩, rfl⟩
    eraseA := rfl
    carrierA := ⟨prop aBlock, aBlock, 8, .genesis,
      ⟨9, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, rfl⟩
    carrierB := ⟨prop bBlock, bBlock, 16, aBlock,
      ⟨17, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    carrierD := ⟨prop dBlock, dBlock, 24, bBlock,
      ⟨25, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    honestB := ⟨⟨by decide, by decide⟩, prop bBlock, ⟨17, rfl, by decide +kernel⟩, rfl⟩
    honestD := ⟨⟨by decide, by decide⟩, prop dBlock, ⟨25, rfl, by decide +kernel⟩, rfl⟩
    slotA := rfl
    slotB := rfl
    slotD := rfl
    earlySlot := ⟨by decide, by decide⟩
    heightA := block_premises_sat.1
    highA := by decide
    heightB := block_premises_sat.2.1
    entryB := block_premises_sat.2.2.1
    freshEntry := ⟨by decide +kernel, by decide +kernel⟩
    strictAU := ⟨by decide, by decide⟩
    pathUB := preceq_refl _
    freshSlot := ⟨by decide, by decide⟩
    parentAB := preceq_refl _
    parentBD := preceq_refl _
    sourceA := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    sourceB := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    serviceD := ⟨fun _ x _ _ => rfl, fun _ x _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
    heightD := by decide +kernel
    justifiedD := by decide +kernel
    justifiedHeightD := by decide +kernel
    pendingD := by decide +kernel
    retainedD := block_premises_sat.2.2.2.2.2.2.2
    noFirstHeight := first
    noSecondHeight := second
    noEarlyFinality := noFin
    chainA := chains.1
    chainB := chains.2.1
    chainD := chains.2.2
    freshD := ⟨schedule_premises_sat, by change (0 : Nat) < 1; decide,
      30, le_rfl, chains.2.2, second, noFin⟩
    noMixedD := by
      intro W hp
      change FGBlock.Preceq W bBlock at hp
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl <;> unfold MixedCross <;> decide +kernel
    batchB := fun _ => batch_premises_sat.1
    batchD := fun _ => batch_premises_sat.2
    targetsB := by
      intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨22, wire row2, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
    actionsInRun := by decide
    capThroughBAction := capB
    capThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).1
    finalityThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).2
    heldDAtFinalAction := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    heldAAtEnd := by
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
  }
  exact ⟨m, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms mixed_premises_sat

set_option maxRecDepth 2048 in
private theorem action_premises_sat : ∃ m : middleType run,
    (m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
      m.cD = 6 ∧ m.d = 2) ∧
    KernelActionSupplyFG_W core reads obs timing (env Nat) run interface history electorate m := by
  obtain ⟨m, hA, hB, hU, hD, hc, hd⟩ := mixed_premises_sat
  have honestRead (x : Nat) (nd : Time) (hnd : postClock (env Nat) run x 30 = some nd) :
      x = 7 ∨ x = 9 := by
    unfold postClock preTick at hnd
    cases hi : V2.D.Run.tickIdx? run x 30 with
    | none => simp only [hi, Option.map_none] at hnd; contradiction
    | some j =>
      have he := V2.D.Run.tickIdx?_spec hi
      have hm := List.mem_of_getElem? he
      have hx := schedule_premises_sat.honest_only _ hm
      change x ∈ run.honest at hx
      simpa using hx
  refine ⟨m, ⟨hA, hB, hU, hD, hc, hd⟩, ?_⟩
  constructor
  · intro x nd hnd
    change postClock (env Nat) run x 30 = some nd at hnd
    have hx := honestRead x nd hnd
    rcases hx with rfl | rfl
    all_goals
      change some 30 = some nd at hnd
      obtain rfl := Option.some.inj hnd
      decide +kernel
  · intro x hx
    rw [hc, hD]
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    all_goals
      constructor
      · intro _; exact ⟨30, by decide +kernel, rfl⟩
      · intro h; change (6 : Nat) < 6 at h; omega
  · intro x nd hx hnd
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    all_goals
      change some 30 = some nd at hnd
      obtain rfl := Option.some.inj hnd
      exact ⟨dBlock, rfl, by decide⟩
  · intro x nd _ _ H hH
    have he : dBlock = H := Option.some.inj hH
    subst H
    rw [hD]
    decide

#print axioms action_premises_sat

private abbrev blocks : Finset (FGBlock (Fin 1)) := {.genesis, aBlock, bBlock, dBlock, xBlock}

private theorem store_premises_sat : ∀ t,
    FGStoreInvariant obs.height obs.finality (staged t) := by
  have closed : ∀ B ∈ blocks, B.parent ∈ blocks := by decide
  have roots (st : Store (Fin 1)) (B : FGBlock (Fin 1))
      (hst : st.TF ⊆ blocks) (hB : B ∈ blocks) : StoreStepRoots st B := by
    have sub : insert B st.TF ⊆ blocks := Finset.insert_subset hB hst
    intro X Y ⟨W, hW, hX⟩ ⟨Z, hZ, hY⟩ hr
    have hx := KitFG.ancestor_closed_of_parent_closed blocks closed W (sub hW) X hX
    have hy := KitFG.ancestor_closed_of_parent_closed blocks closed Z (sub hZ) Y hY
    exact (by decide : ∀ X ∈ blocks, ∀ Y ∈ blocks, X.root = Y.root → X = Y) X hx Y hy hr
  have invA : FGStoreInvariant obs.height obs.finality storeA :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _
      (KitFG.Window.windowStoreInvariant_init electorate cfg 2)
      (roots _ _ (by decide) (by decide))
  have invB : FGStoreInvariant obs.height obs.finality storeB :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ invA
      (roots _ _ (by decide +kernel) (by decide))
  have invD : FGStoreInvariant obs.height obs.finality storeD :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ invB
      (roots _ _ (by decide +kernel) (by decide))
  have invX : FGStoreInvariant obs.height obs.finality storeX :=
    KitFG.Window.windowStoreInvariant_on_block electorate cfg 2
      (by change ¬ (1 ≤ 0); decide) (by decide) _ _ invD
      (roots _ _ (by decide +kernel) (by decide))
  intro t
  unfold staged
  split_ifs
  · have he : { storeA with TF := {.genesis, aBlock} } = storeA := by
      have ht : {.genesis, aBlock} = storeA.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invA
  · have he : { storeB with TF := {.genesis, aBlock, bBlock} } = storeB := by
      have ht : {.genesis, aBlock, bBlock} = storeB.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invB
  · have he : { storeD with TF := {.genesis, aBlock, bBlock, dBlock} } = storeD := by
      have ht : {.genesis, aBlock, bBlock, dBlock} = storeD.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invD
  · have he : { storeX with TF := {.genesis, aBlock, bBlock, dBlock, xBlock} } = storeX := by
      have ht : {.genesis, aBlock, bBlock, dBlock, xBlock} = storeX.TF := by decide +kernel
      rw [ht]
    rw [he]; exact invX

#print axioms store_premises_sat

private theorem durable_premises_sat : FGFinalityDurableLaws core := by
  have fin (t : Time) : (staged t).F = if t < 32 then .genesis else bBlock := by
    unfold staged
    split_ifs <;> first | rfl | decide +kernel | linarith
  have mono (s t : Time) (h : s ≤ t) : FGBlock.Preceq (staged s).F (staged t).F := by
    rw [fin s, fin t]
    split_ifs <;> first | exact preceq_refl _ | exact genesis_preceq _ | linarith
  refine ⟨fun X => ⟨?_, fun _ _ h => h, fun _ _ h => h⟩, fun _ _ => rfl⟩
  intro st t h
  exact KitFG.preceq_trans h (mono st (max st t) (le_max_left _ _))

#print axioms durable_premises_sat

private abbrev ready (i : Nat) (x : Nat) (W : FGBlock (Fin 1)) (t : Time) : Prop :=
  ((i = 32 ∧ x = 9) ∨ (i = 33 ∧ x = 7)) ∧ W = xBlock ∧ t = 32

-- Both actual terminal ticks run exactly the window insertion/update required by the owner.
set_option maxRecDepth 2048 in
private theorem acceptance_effect_premises_sat :
    AcceptStep_W core (env Nat) run electorate cfg 2 ready ∧
    ready 32 9 xBlock 32 ∧ ready 33 7 xBlock 32 ∧
    (SimplexFG.Window.derive electorate cfg 2 xBlock).F = bBlock := by
  refine ⟨?_, by decide, by decide, by decide +kernel⟩
  rintro i x W t _ ⟨h, rfl, rfl⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    constructor
    · change Store.mk _ _ _ _ _ = Store.mk _ _ _ _ _
      simp only [Store.mk.injEq]
      refine ⟨?_, rfl, rfl, rfl, rfl⟩
      decide +kernel
    · decide +kernel

#print axioms acceptance_effect_premises_sat

private def selectedDelivery : BlockDelivery_W core (env Nat) run ready xBlock bBlock 32
    (kernelDeadlineW timing 2 3) where
  selected x _ := if x = 9 then ⟨32, 32⟩ else ⟨33, 32⟩
  witness x hx := by
    have hx : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx with rfl | rfl
    all_goals
      refine ⟨rfl, by decide, Or.inr ⟨le_rfl, ?_⟩⟩
      decide

set_option maxRecDepth 2048 in
private theorem receipt_premises_sat :
    Nonempty (AcceptPrem_W core (env Nat) run electorate cfg 2 ready xBlock bBlock 32
      (kernelDeadlineW timing 2 3)) := by
  refine ⟨⟨schedule_premises_sat, ?_, selectedDelivery, ?_, by decide⟩⟩
  · rw [acceptance_effect_premises_sat.2.2.2]
    exact preceq_refl _
  · constructor
    · intro x hx
      dsimp only
      intro _
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl
      all_goals
        change FGBlock.Preceq .genesis bBlock ∨ FGBlock.Preceq bBlock .genesis
        exact Or.inl (genesis_preceq _)
    · intro x hx
      dsimp only
      intro _ _
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl
      all_goals
        change FGBlock.Preceq bBlock xBlock ∨ (3 : Nat) < (obs.height xBlock).h_j
        exact Or.inl (by decide)
    · intro x hx
      dsimp only
      intro _ _
      have hx : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx with rfl | rfl <;> dsimp only [selectedDelivery] <;> decide +kernel

#print axioms receipt_premises_sat

private theorem target_supplier_premises_sat :
    ∀ i : Fin 1, safetyHolder reads run i ∈ run.honest → ∀ r C,
      actionSourceFG core (env Nat) run timing (safetyHolder reads run i) r = some (some C) →
      point.reset.M + 1 ≤ (obs.height C).h →
      (env Nat).awake (safetyHolder reads run i) (timing.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧
        HonestRowAt reads (env Nat) run timing j (safetyHolder reads run i) rSent a ∧
        RowComplete reads run history.signer (fun _ => true) (safetyHolder reads run i) a ∧
        history.heightPair a = .vote (obs.height C).h (obs.height C).T_h.root false := by
  intro i _ r C hs _ _
  obtain rfl : i = 0 := Subsingleton.elim _ _
  change actionSourceFG core (env Nat) run timing 9 r = some (some C) at hs
  have bound : r ≤ 3 := by
    unfold actionSourceFG postClock preTick at hs
    cases hi : V2.D.Run.tickIdx? run 9 (timing.action r) with
    | none => simp only [hi, Option.map_none] at hs; contradiction
    | some j =>
      have he := V2.D.Run.tickIdx?_spec hi
      have ht := (schedule_premises_sat.in_horizon _ (List.mem_of_getElem? he)).2
      change 4 * (r * 2 : Nat) + 6 ≤ (33 : Int) at ht
      omega
  interval_cases r
  all_goals
    have hc : _ = C := Option.some.inj (Option.some.inj hs)
    subst C
  · exact ⟨6, 0, wire row0, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩
  · exact ⟨14, 1, wire row1, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩
  · exact ⟨22, 2, wire row2, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩
  · exact ⟨30, 3, wire row3, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
      ⟨rfl, 0, rfl, rfl⟩, by decide +kernel⟩

#print axioms target_supplier_premises_sat

private theorem opening_premises_sat :
    HonestProposal (env Nat) run interface 2 (erase aBlock) ∧
    ∀ A, HonestProposal (env Nat) run interface 2 A → A = erase aBlock := by
  refine ⟨⟨⟨by decide, by decide⟩, prop aBlock, ⟨9, rfl, by decide +kernel⟩, rfl⟩, ?_⟩
  intro A ⟨_, o, ⟨j, hj, ho⟩, hb⟩
  have he : run.events[j]? = some (.tick 7 8) := hj
  have idx : j = 9 := by
    have hjlt : j < 34 := (List.getElem?_eq_some_iff.mp he).1
    have unique : ∀ k : Fin 34, run.events[k.val]? = some (.tick 7 8) → k.val = 9 := by
      decide +kernel
    exact unique ⟨j, hjlt⟩ he
  subst j
  change o ∈ [prop aBlock] at ho
  obtain rfl := List.mem_singleton.mp ho
  exact (Option.some.inj hb).symm

#print axioms opening_premises_sat

-- Bounded owner composition: the selected holder middle and its exact terminal acceptance
-- give the original, all-honest-receiver conclusion without constructing an old middle.
private theorem kernel_conclusion_premises_sat :
    KernelConclusion_W core (env Nat) run obs timing interface decodeProposal erase
      (fun X => X.rows.map wire) (fun nd Q => parentRead nd Q.parent) makeFG 2 1 ∧
    AcceptsFinalBefore core (env Nat) run 7 bBlock (kernelDeadlineW timing 2 3) ∧
    AcceptsFinalBefore core (env Nat) run 9 bBlock (kernelDeadlineW timing 2 3) := by
  obtain ⟨m, ⟨hA, _, hU, _, _, _⟩, _⟩ := action_premises_sat
  obtain ⟨prem⟩ := receipt_premises_sat
  have accepted := acceptBefore_W core (env Nat) run electorate cfg 2
    (by change ¬ (1 ≤ 0); decide) (by decide) durable_premises_sat ready
    acceptance_effect_premises_sat.1 (fun i x _ => store_premises_sat _)
    xBlock bBlock 32 _ prem
  refine ⟨?_, accepted 7 (by decide), accepted 9 (by decide)⟩
  intro A h
  obtain rfl := opening_premises_sat.2 A h
  refine ⟨m.A₀, m.eraseA, m.carrierA, m.heldAAtEnd, m.U, m.strictAU.1, m.strictAU.2, ?_, ?_⟩
  · rw [m.freshEntry.1, m.heightA]
  · rw [hU]
    exact accepted

#print axioms kernel_conclusion_premises_sat

-- Isolated old supplier failure: its source antecedent is active at honest nonholder 7.
private theorem old_target_supplier_impossible :
    ¬ (∀ x ∈ run.honest, ∀ r C,
      actionSourceFG core (env Nat) run timing x r = some (some C) →
      point.reset.M + 1 ≤ (obs.height C).h → (env Nat).awake x (timing.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt reads (env Nat) run timing j x rSent a ∧
        RowComplete reads run history.signer (fun _ => true) x a ∧
        history.heightPair a = .vote (obs.height C).h (obs.height C).T_h.root false) := by
  intro old
  obtain ⟨_, _, _, _, _, complete, _⟩ := old 7 (by decide) 1 aBlock
    (by decide +kernel) (by decide +kernel) rfl
  obtain ⟨i, _, hi⟩ := complete.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_target_supplier_impossible

private abbrev honestSlot (s : Slot) : Prop := s = 2 ∨ s = 4 ∨ s = 6 ∨ s = 8

private theorem kernel_population_premises_sat :
    KernelPrem_W timing 2 run.horizon point pt honestSlot electorate.q
      (electorate.weightOf (Finset.univ \ historyFaulty reads run)) cfg.timeoutDelay 2 ∧
    KernelRunFacts reads (env Nat) run electorate 2 ∧
    ∃ m : middleType run,
      KernelActionSupplyFG_W core reads obs timing (env Nat) run interface history
        electorate m := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · exact ⟨by decide⟩
    · rw [Gen.Pure.FGoodE_W_def]
      exact ⟨by decide, by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩
    · decide
    · decide
    · decide
    · rfl
    · decide
  · constructor
    · exact schedule_premises_sat
    · decide
    · exact le_rfl
    · intro i j _; exact Subsingleton.elim _ _
    · intro x hx t ht hhor; rfl
  · obtain ⟨m, _, act⟩ := action_premises_sat
    exact ⟨m, act⟩

#print axioms kernel_population_premises_sat

private theorem frozen_rows (j : Nat) (x : Fin 1) (q : Nat) (a : protocol.Object)
    (ha : HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a) :
    (j = 3 ∧ x = 0 ∧ q = 0 ∧ a = wire row0) ∨
    (j = 7 ∧ x = 0 ∧ q = 1 ∧ a = wire row1) ∨
    (j = 11 ∧ x = 0 ∧ q = 2 ∧ a = wire row2) ∨
    (j = 15 ∧ x = 0 ∧ q = 3 ∧ a = wire row3) := by
  obtain ⟨_, hj, hw⟩ := ha
  have hlen : j < 17 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (6 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (6 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 0 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row0] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inl (⟨rfl, rfl, rfl, hw'⟩)
  · have he : (0 : Fin 1) = x ∧ (8 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (8 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (14 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (14 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 1 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row1] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩))
  · have he : (0 : Fin 1) = x ∧ (16 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (16 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (22 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (22 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 2 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row2] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl, hw'⟩)))
  · have he : (0 : Fin 1) = x ∧ (24 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (24 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : (0 : Fin 1) = x ∧ (30 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (30 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    have hq : q = 3 := by omega
    obtain rfl := he.1.symm
    subst q
    change a ∈ [wire row3] at hw
    have hw' := List.mem_singleton.mp hw
    exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl, hw'⟩)))
  · have he : (0 : Fin 1) = x ∧ (32 : Time) = 4 * (q * 2 : Nat) + 6 :=
      V2.Event.tick.inj (Option.some.inj hj)
    have hn : (32 : Nat) = 4 * (q * 2) + 6 := by exact_mod_cast he.2
    omega

#print axioms frozen_rows

private theorem frozen_schedule_premises_sat :
    V2.D.ScheduleWellFormed (env (Fin 1)) frozenRun := by
  constructor
  · decide
  · decide +kernel
  · decide +kernel
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with
      rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro x t hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      or_false] at hm
    rcases hm with
      ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨15, rfl⟩
    · exact ⟨16, rfl⟩
  · intro x _ t ht _ hhor _
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := ht
    change t = (k : Time) * 2 at hk
    change t ≤ 33 at hhor
    rw [hk] at hhor
    have hb : k * 2 ≤ 32 := by
      have : (k : Int) * 2 ≤ 33 := by simpa using hhor
      omega
    have hbound : k ≤ 16 := by omega
    subst t
    interval_cases k <;> simp

#print axioms frozen_schedule_premises_sat

private theorem frozen_batch_premises_sat :
    batchType frozenRun 1 2 aBlock bBlock ∧ batchType frozenRun 2 3 bBlock dBlock := by
  have hweight : electorate.weightOf (historyFaulty reads frozenRun) < electorate.q := by
    change (0 : Nat) < 1
    decide
  have receipt : TRowsReceipt core reads (env (Fin 1)) frozenRun timing (fun _ => []) 2 := by
    intro j x q a ha _ z _
    rcases frozen_rows j x q a ha with h | h | h | h
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl (by
        change wire _ ∈ [wire row0, wire row1, wire row2, wire row3]
        decide +kernel)
  have height := KitFG.Window.windowHeightLaws electorate cfg 2 (by decide)
  constructor
  · refine kmid_batchPrem_holder core reads obs timing (env (Fin 1)) frozenRun interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      frozen_schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 1 2 aBlock bBlock (by decide) ?_ 16 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)); decide
    · refine ⟨[wire row1], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop bBlock, ⟨8, rfl, by decide +kernel⟩, rfl⟩,
        prop bBlock, ⟨8, rfl, by decide +kernel⟩, bBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))), FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨7, 1, wire row1, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
  · refine kmid_batchPrem_holder core reads obs timing (env (Fin 1)) frozenRun interface history
      electorate cfg 2 height rfl decodeProposal erase (fun X => X.rows.map wire)
      (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) (fun _ => true) 2
      frozen_schedule_premises_sat hweight ?_ {0} ?_ (by change (1 : Nat) ≤ 1; decide)
      (by decide) receipt 2 3 bBlock dBlock (by decide) ?_ 24 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_ ?_ ?_ rfl (by intros; rfl)
      (by decide) (by constructor <;> decide +kernel) (preceq_refl _) (by decide +kernel) ?_
    · intro i i' _; exact Subsingleton.elim _ _
    · intro i _; change (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)); decide
    · refine ⟨[wire row2], ?_, rfl⟩
      refine ⟨⟨⟨by decide, by decide⟩, prop dBlock, ⟨12, rfl, by decide +kernel⟩, rfl⟩,
        prop dBlock, ⟨12, rfl, by decide +kernel⟩, dBlock, rfl, rfl, rfl⟩
    · intro W hW
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> decide +kernel
    · have ancestors (X : FGBlock (Fin 1))
          (hX : ∃ W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))),
            FGBlock.Preceq X W) :
          X ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) := by
        obtain ⟨W, hW, hXW⟩ := hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
        rcases hW with rfl | rfl | rfl | rfl
        all_goals
          simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hXW
          tauto
      intro W Z hW hZ he
      have hw := ancestors W hW
      have hz := ancestors Z hZ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
      rcases hw with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
        simp_all [FGBlock.root, genesisRoot]
    · intro W hW row hr
      change W ∈ ({.genesis, aBlock, bBlock, dBlock} : Finset (FGBlock (Fin 1))) at hW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl
      · cases hr
      · have he : row = row0 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row1 := List.mem_singleton.mp hr
        subst row
        decide +kernel
      · have he : row = row2 := List.mem_singleton.mp hr
        subst row
        decide +kernel
    · intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨11, 2, wire row2, le_rfl, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩

#print axioms frozen_batch_premises_sat

private theorem frozen_premises_sat : ∃ m : middleType frozenRun,
    m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
    m.cD = 6 ∧ m.d = 2 := by
  have first : ∀ j x q a h t, HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a →
      historyRowHeight reads history a = some h → 3 ≤ h → eventTime frozenRun j = some t →
      timing.action 2 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have second : ∀ j x q a h t, HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a →
      historyRowHeight reads history a = some h → 4 ≤ h → eventTime frozenRun j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh hy ht
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      simp only [historyRowHeight, decode, Option.map_some,
        Option.getD_some, Option.some.injEq] at hh
      obtain rfl := hh.symm
      have htime : _ = t := Option.some.inj ht
      subst t
      first | omega | decide
  have noFin : ∀ j x q a h t, HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a →
      historyFinHeight reads history a = some h → 3 ≤ h → eventTime frozenRun j = some t →
      timing.action 3 ≤ t := by
    intro j x q a h t ha hh _ ht
    rcases frozen_rows j x q a ha with he | he | he | he
    all_goals
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      cases hh
      all_goals exact le_of_eq (Option.some.inj ht)
  have chains : ChainRowsBefore core (env (Fin 1)) frozenRun aBlock 14 ∧
      ChainRowsBefore core (env (Fin 1)) frozenRun bBlock 22 ∧
      ChainRowsBefore core (env (Fin 1)) frozenRun dBlock 30 := by
    refine ⟨?_, ?_, ?_⟩
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl
      · exact ⟨0, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨0, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
    · intro W hp row hr
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨0, 25, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨0, 17, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · exact ⟨0, 1, by decide, by decide, by unfold Gen.V2.Duty.HoldsBefore; decide +kernel⟩
      · cases hr
  have capB : ∀ i x W, i ≤ frozenRun.events.length → i ≤ afterTicksIdx frozenRun 22 →
      HeldAt core (env (Fin 1)) frozenRun i x W → (obs.height W).h ≤ 3 := by
    intro i x W _ hi ⟨hx, hW⟩
    have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
    have hib : i ≤ 12 := hi
    have ht : V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 := by
      rcases hx' with rfl
      interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl <;> decide +kernel
  have capFinal : ∀ i x W, i ≤ afterTicksIdx frozenRun 30 →
      HeldAt core (env (Fin 1)) frozenRun i x W →
      (obs.height W).h ≤ 4 ∧ (obs.finality W).h_F < 3 := by
    intro i x W hi ⟨hx, hW⟩
    have ht : V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 32 := by
      have hib : i ≤ 16 := hi
      obtain rfl : x = (0 : Fin 1) := Subsingleton.elim _ _
      interval_cases i <;> decide +kernel
    change W ∈ (if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 16 then
      ({FGBlock.genesis, aBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 24 then
      ({FGBlock.genesis, aBlock, bBlock} :
        Finset (FGBlock (Fin 1))) else if V2.D.Run.stateBefore (env (Fin 1)) frozenRun i x < 32 then
      ({FGBlock.genesis, aBlock, bBlock, dBlock} :
        Finset (FGBlock (Fin 1))) else ({FGBlock.genesis, aBlock, bBlock, dBlock, xBlock} :
        Finset (FGBlock (Fin 1)))) at hW
    rw [ite_eq_left ht] at hW
    split_ifs at hW
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel
  let m : middleType frozenRun := {
    A₀ := aBlock
    B := bBlock
    U := bBlock
    X_D := dBlock
    cD := 6
    d := 2
    opening := ⟨⟨by decide, by decide⟩, prop aBlock, ⟨4, rfl, by decide +kernel⟩, rfl⟩
    eraseA := rfl
    carrierA := ⟨prop aBlock, aBlock, 8, .genesis,
      ⟨4, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, rfl⟩
    carrierB := ⟨prop bBlock, bBlock, 16, aBlock,
      ⟨8, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    carrierD := ⟨prop dBlock, dBlock, 24, bBlock,
      ⟨12, rfl, by decide +kernel⟩, rfl, rfl, by decide +kernel, by decide +kernel, by decide⟩
    honestB := ⟨⟨by decide, by decide⟩, prop bBlock, ⟨8, rfl, by decide +kernel⟩, rfl⟩
    honestD := ⟨⟨by decide, by decide⟩, prop dBlock, ⟨12, rfl, by decide +kernel⟩, rfl⟩
    slotA := rfl
    slotB := rfl
    slotD := rfl
    earlySlot := ⟨by decide, by decide⟩
    heightA := block_premises_sat.1
    highA := by decide
    heightB := block_premises_sat.2.1
    entryB := block_premises_sat.2.2.1
    freshEntry := ⟨by decide +kernel, by decide +kernel⟩
    strictAU := ⟨by decide, by decide⟩
    pathUB := preceq_refl _
    freshSlot := ⟨by decide, by decide⟩
    parentAB := preceq_refl _
    parentBD := preceq_refl _
    sourceA := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
    sourceB := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
    serviceD := ⟨fun _ x _ _ => rfl, fun _ x _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
    heightD := by decide +kernel
    justifiedD := by decide +kernel
    justifiedHeightD := by decide +kernel
    pendingD := by decide +kernel
    retainedD := block_premises_sat.2.2.2.2.2.2.2
    noFirstHeight := first
    noSecondHeight := second
    noEarlyFinality := noFin
    chainA := chains.1
    chainB := chains.2.1
    chainD := chains.2.2
    freshD := ⟨frozen_schedule_premises_sat, by change (0 : Nat) < 1; decide,
      30, le_rfl, chains.2.2, second, noFin⟩
    noMixedD := by
      intro W hp
      change FGBlock.Preceq W bBlock at hp
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hp
      rcases hp with rfl | rfl | rfl <;> unfold MixedCross <;> decide +kernel
    batchB := fun _ => frozen_batch_premises_sat.1
    batchD := fun _ => frozen_batch_premises_sat.2
    targetsB := by
      intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact ⟨11, wire row2, ⟨by decide, rfl, by decide +kernel⟩,
        ⟨rfl, 0, rfl, rfl⟩, rfl⟩
    actionsInRun := by decide
    capThroughBAction := capB
    capThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).1
    finalityThroughFinalAction := fun i x W _ hi h => (capFinal i x W hi h).2
    heldDAtFinalAction := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
    heldAAtEnd := by
      intro x hx
      have hx' : x = (0 : Fin 1) := Subsingleton.elim _ _
      rcases hx' with rfl
      decide +kernel
  }
  exact ⟨m, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms frozen_premises_sat

set_option maxRecDepth 2048 in
private theorem frozen_action_premises_sat : ∃ m : middleType frozenRun,
    (m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
      m.cD = 6 ∧ m.d = 2) ∧
    KernelActionSupplyFG_W core reads obs timing (env (Fin 1)) frozenRun interface
      history electorate m := by
  obtain ⟨m, hA, hB, hU, hD, hc, hd⟩ := frozen_premises_sat
  refine ⟨m, ⟨hA, hB, hU, hD, hc, hd⟩, ?_⟩
  constructor
  · intro x nd hnd
    obtain rfl : x = 0 := Subsingleton.elim _ _
    change some 30 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    decide +kernel
  · intro x _
    obtain rfl : x = 0 := Subsingleton.elim _ _
    rw [hc, hD]
    constructor
    · intro _; exact ⟨30, by decide +kernel, rfl⟩
    · intro h; change (6 : Nat) < 6 at h; omega
  · intro x nd _ hnd
    obtain rfl : x = 0 := Subsingleton.elim _ _
    change some 30 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    exact ⟨dBlock, rfl, by decide⟩
  · intro x nd _ _ H hH
    have he : dBlock = H := Option.some.inj hH
    subst H
    rw [hD]
    decide

#print axioms frozen_action_premises_sat

private theorem reflection_premises_sat (A B : FGBlock (Fin 1))
    (h : Block.Preceq (erase A) (erase B)) : FGBlock.Preceq A B := by
  have inj : Function.Injective erase := by
    intro X
    induction X with
    | genesis => intro Y he; cases Y <;> simp_all [erase]
    | node p s r x rs ih =>
      intro Y he
      cases Y with
      | genesis => simp [erase] at he
      | node q t u y ts =>
        simp only [erase, Block.node.injEq] at he
        obtain ⟨hp, hs, hr, hb⟩ := he
        obtain ⟨hx, hrows⟩ := encFGBody_inj hb
        cases ih hp
        cases hs
        cases hr
        cases hx
        cases hrows
        rfl
  induction B with
  | genesis =>
    have he : erase A = erase .genesis := of_decide_eq_true h
    exact inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (erase A = erase (.node P slot root app rows)) ||
      Block.preceq (erase A) (erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

#print axioms reflection_premises_sat

private theorem old_middle_impossible (m : KernelMiddleWitness_W core reads obs timing
    (env Nat) run interface history electorate decodeProposal erase (fun X => X.rows.map wire)
    (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true)
    (ac Nat) cfg 2 2 point pt (erase aBlock)) : False := by
  obtain ⟨_, _, _, complete, _⟩ := m.targetsB 7 (by decide)
  obtain ⟨i, _, hi⟩ := complete.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_middle_impossible

private abbrev frozenOldType :=
  KernelMiddleWitness_W core reads obs timing (env (Fin 1)) frozenRun interface history
    electorate decodeProposal erase (fun X => X.rows.map wire) (fun _ => []) parentRead
    parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true) (ac (Fin 1))
    cfg 2 2 point pt (erase aBlock)


set_option maxRecDepth 2048 in
private theorem frozen_bridge_premises_sat :
    (Nonempty frozenOldType ↔ Nonempty (middleType frozenRun)) ∧
    ∃ m : frozenOldType, ∃ h : middleType frozenRun,
      (m.A₀ = h.A₀ ∧ m.B = h.B ∧ m.U = h.U ∧
        m.X_D = h.X_D ∧ m.cD = h.cD ∧ m.d = h.d) ∧
      KernelActionSupply_W core reads obs timing (env (Fin 1)) frozenRun interface
        history electorate m ∧
      KernelActionSupplyFG_W core reads obs timing (env (Fin 1)) frozenRun interface
        history electorate h ∧
      (∀ x ∈ frozenRun.honest, ∃ H, core.finalityHead 30 = some H ∧
        FGBlock.Preceq m.X_D H ∧ (obs.height H).h = m.d + 2 ∧
        (obs.height H).J = m.U ∧ (obs.height H).h_j = m.d + 1) ∧
      (∀ x ∈ frozenRun.honest, ∃ H, core.finalityHead 30 = some H ∧
        FGBlock.Preceq h.X_D H ∧ (obs.height H).h = h.d + 2 ∧
        (obs.height H).J = h.U ∧ (obs.height H).h_j = h.d + 1) := by
  have bridge := kernel_middle_holder_frozen_iff core reads obs timing (env (Fin 1))
    frozenRun interface history electorate decodeProposal erase (fun X => X.rows.map wire)
    (fun _ => []) parentRead parentHeight (fun _ _ _ _ => true) makeFG (fun _ => true)
    (ac (Fin 1)) cfg 2 2 point pt (erase aBlock) (Equiv.refl _) (by
      intro i; exact Subsingleton.elim _ _)
  obtain ⟨h, _, act⟩ := frozen_action_premises_sat
  obtain ⟨m, selected⟩ := bridge.2.2 h
  have oldAct := (kernel_action_holder_frozen_iff
    (m := m) (h := h) (selected := selected)).mpr act
  have newHead := rowsPrem_pending_head_holder h
    (KitFG.Window.windowHeightLaws electorate cfg 2 (by decide))
    (KitFG.Window.windowHeightBridge electorate cfg 2 (by decide))
    act.read act.head act.walk (fun _ A B _ _ hp => reflection_premises_sat A B hp)
  have oldHead := rowsPrem_pending_head m
    (KitFG.Window.windowHeightLaws electorate cfg 2 (by decide))
    (KitFG.Window.windowHeightBridge electorate cfg 2 (by decide))
    oldAct.read oldAct.head oldAct.walk
    (fun _ A B _ _ hp => reflection_premises_sat A B hp)
  refine ⟨bridge.1, m, h, selected, oldAct, act, ?_, ?_⟩
  · intro x hx
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain ⟨H, hH, hp, hh, hJ, hj, _⟩ := oldHead 0 30 hx (by decide +kernel)
    exact ⟨H, hH, hp, hh, hJ, hj⟩
  · intro x hx
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain ⟨H, hH, hp, hh, hJ, hj, _⟩ := newHead 0 30 hx (by decide +kernel)
    exact ⟨H, hH, hp, hh, hJ, hj⟩

#print axioms frozen_bridge_premises_sat

private theorem timing_premises_sat : FGTimingLaws timing := by
  constructor <;> intros <;> simp


#print axioms timing_premises_sat

-- Logical frozen specialization: reuse every old leaf and the paired record bridges.
-- This implication is separate from the exact-data bounded controls above.
namespace FrozenOwner

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (chainWireRows : P.State → Block → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)
variable (cfg : FGConfig) (K : Nat) (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt)
variable {Jst : Time}

include L in
private theorem frozen_owner_specialization
    (e : Fin n ≃ V) (he : ∀ i, safetyHolder S rho i = e i)
    (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (keep : FGTreeKeepLaws R) (restore : FGTreeRestoreLaws R)
    (hc : FGCertificateLaws Ef O.height O.finality)
    (heightBridge : HeightBridge Ef cfg O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅)
    (target : TargetJustification Ef O.height)
    (foldTarget : ∀ y U X, X ≠ .genesis → EntryAt O.height U y →
      FGBlock.Preceq U X.parent →
      ((O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y) →
      y + 1 ≤ (O.height X).h)
    (noMixed : ∀ y U X, SlotChain X → EntryAt O.height U y →
      FGBlock.Preceq U X.parent → X.slot < U.slot + cfg.timeoutDelay + 1 →
      NoMixedOnPath O.height X y)
    (honestSlot : Slot → Prop)
    (hK : KernelPrem_W T ΔF rho.horizon sp pt honestSlot Ef.q
      (Ef.weightOf (Finset.univ \ historyFaulty S rho)) cfg.timeoutDelay K)
    (run : KernelRunFacts S E rho Ef ΔF)
    (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGSTstart : E.t_GST ≤ sp.serviceStart)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (chain : ∀ horizon, FGHistoricalHighChain R O T E rho sp horizon)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (hOrigin : RawHistoryOrigin R S E rho T D)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (honest_slot : ∀ s, honestSlot s → ∃ x, x ∈ rho.honest)
    (proposal : ∀ s, honestSlot s → pt.r * T.roundSlots ≤ s →
      s ≤ (pt.r + 2) * T.roundSlots → ∃ Q, HonestProposal E rho I s Q)
    (terminalProposal : honestSlot ((pt.r + 2) * T.roundSlots + kappaF T ΔF) →
      ∃ Q, HonestProposal E rho I ((pt.r + 2) * T.roundSlots + kappaF T ΔF) Q)
    (carrier : ∀ s Q, HonestProposal E rho I s Q →
      ∃ X : FGBlock (Fin n), R.erase X = Q ∧
        OpeningCarrier_W decodeProposal bodyErase bodyRows (fun nd Q => parentFG nd Q.parent)
          makeFG E rho I s Q X ∧ X.slot = s ∧
        (∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
          s Q rows ∧ X.rows = rows.filterMap S.decode) ∧
        ∃ nd, proposalStateAt E rho I s = some nd ∧
          parentFG nd Q.parent = some X.parent ∧ X.parent ∈ (R.core nd).fg.TF)
    (exactService : ∀ s Q, HonestProposal E rho I s Q → pt.r * T.roundSlots ≤ s →
      KernelExactService ac rho.horizon s Q)
    (source_read : ∀ s Q r x, KernelExactService ac rho.horizon s Q →
      T.gate s ≤ rho.horizon → s = r * T.roundSlots → x ∈ rho.honest →
      pt.r * T.roundSlots ≤ s → ac.source x r = some (some Q))
    (source_eq : ∀ x r, ac.source x r =
      (actionSourceFG R E rho T x r).map (Option.map R.erase))
    (head_read : ∀ s Q x, KernelExactService ac rho.horizon s Q →
      pt.r * T.roundSlots ≤ s → s ≤ (pt.r + 2) * T.roundSlots → x ∈ rho.honest →
      headAtLabel R E rho T x s = some Q)
    (head_held : ∀ s X x, headAtLabel R E rho T x s = some (R.erase X) →
      ∃ i, rho.events[i]? = some (.tick x (T.vote s)) ∧
        X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (slot_chain : ∀ i x X, X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF → SlotChain X)
    (closed : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, X.parent ∈ (R.core nd).fg.TF)
    (roots : ∀ s nd, proposalStateAt E rho I s = some nd → ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, ∀ row ∈ X.rows,
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K X.parent) row = true)
    (parentEq : ∀ nd s X, parentHeight nd s X = ((O.height X).h, (O.height X).T_h.root))
    (matchValid : ∀ nd s X a, valid a = true →
      namedEntry (D.heightPair a) = some (parentHeight nd s X) → validFor nd s X a = true)
    (hBatch : ∀ q y U X,
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .target q y U X →
      (O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ r C,
      actionSourceFG R E rho T x r = some (some C) → sp.reset.M + 1 ≤ (O.height C).h →
      E.awake x (T.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
        RowComplete S rho D.signer valid x a ∧
        D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false)
    (action : ∀ A (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase
      bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A),
      KernelActionSupply_W R S O T E rho I D Ef m)
    (makeWire : Row (Fin n) → Wire)
    (wireDecode : ∀ row, S.decode (makeWire row) = some row)
    (wireValid : ∀ i y U B,
      valid (makeWire ⟨i, .vote (y + 1) B false, some ⟨y, U⟩⟩) = true)
    (client : ∀ nd, (S.inputs nd).1 = R.source nd)
    (release : ∀ i q nd row,
      postClock E rho (safetyHolder S rho i) (T.action q) = some nd →
      E.awake (safetyHolder S rho i) (T.action q) = true →
      (createRowOnce Ef cfg (S.record nd) i (S.inputs nd).1 (S.inputs nd).2).1 = some row →
      ∃ j, rho.events[j]? = some (.tick (safetyHolder S rho i) (T.action q)) ∧
        S.encode (makeWire row) ∈ V2.D.Run.emitsAt E rho j)
    (fields : ∀ nd H, R.finalityHead nd = some H →
      (S.inputs nd).2 = certificateHeadFields O.height O.finality H)
    {storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop}
    {SourceService : V → Nat → FGBlock (Fin n) → Prop}
    (hQC : RQCOrigin R S E rho O T storedCarrier SourceService Ef)
    (recordHead : HighRecordHead R S O E rho) (clientLaws : FGSafetyClientLaws S Ef cfg)
    (own : HighRecordOwnOrigin S T E rho)
    (hsel : TRowsSelect R S E rho T I (kernelCarrier decodeProposal bodyErase bodyRows)
      chainWireRows blockWireRows parentFG validFor)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((S.decode a).isSome && ((S.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState Ef cfg K B s))).getD false))
    (pathValid : ∀ s nd, proposalStateAt E rho I s = some nd → ∀ H ∈ (R.core nd).fg.TF,
      ∀ B s' root body rs, FGBlock.Preceq (.node B s' root body rs) H → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true)
    (dutyTime : ∀ s, T.proposal s = V2.D.proposalTime I s)
    (rowDurable : ∀ i j x a, i ≤ j →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho i x) a →
      rowHeld R blockWireRows (V2.D.Run.stateBefore E rho j x) a)
    (rowClock : ∀ nd t a, rowHeld R blockWireRows nd a →
      rowHeld R blockWireRows (P.clock nd t) a)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (step : AcceptStep_W R E rho Ef cfg K ready) (durable : FGFinalityDurableLaws R)
    (inv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (finBlock : FGBlock (Fin n) → Prop)
    (hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (O.finality C).F (O.finality W).F = true)
    (readyBlock : ∀ i x X t, ready i x X t → finBlock X)
    (stored : ∀ i x, ∀ C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF,
      C ≠ .genesis → finBlock C)
    (rootScope : ∀ i x, x ∈ rho.honest → ∀ C k u r a B,
      C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
      HonestRowAt S E rho T k u r a → actionSourceFG R E rho T u r = some (some B) →
      (O.height C).J.root = (O.height B).T_h.root → (O.height C).J = (O.height B).T_h)
    (hStrat : ∀ j z W, z ∈ rho.honest →
      W ∈ (R.core (V2.D.Run.stateBefore E rho j z)).fg.TF →
      ∀ J ∈ certified R O W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore S E rho T j u r a ∧
        namedEntry (D.heightPair a) = some ((O.height J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt S E rho T j z r a →
      namedEntry (D.heightPair a) = some e → ∃ C,
        actionSourceFG R E rho T z r = some (some C) ∧
        e = ((O.height C).h, (O.height C).T_h.root) ∧
        FGBlock.Preceq (O.height C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho j z W →
      (∀ k u r a row h B timeout, HonestRowAt S E rho T k u r a →
        S.decode a = some row → row.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (delivery : ∀ (X U : FGBlock (Fin n)) rows,
      HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
        X.slot (R.erase X) rows →
      E.t_GST ≤ T.proposal X.slot → T.proposal X.slot + T.delta ≤ rho.horizon →
      FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F →
      Nonempty (BlockDelivery_W R E rho ready X U (T.proposal X.slot)
        (T.proposal X.slot + T.delta))) :
    KernelConclusion_W R E rho O T I decodeProposal bodyErase bodyRows
      (fun nd Q => parentFG nd Q.parent) makeFG ΔF pt.r := by
  have holderAction : ∀ A (h : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal
      bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG valid ac
      cfg K ΔF sp pt A), KernelActionSupplyFG_W R S O T E rho I D Ef h := by
    intro A h
    obtain ⟨m, selected⟩ := (kernel_middle_holder_frozen_iff R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG
      valid ac cfg K ΔF sp pt A e he).2.2 h
    exact (kernel_action_holder_frozen_iff (m := m) (h := h) (selected := selected)).mp
      (action A m)
  exact finality_kernel_W_of_holder R S O T L E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows chainWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt
    CL HL keep restore hc heightBridge height_eq finality_eq hne target foldTarget noMixed
    honestSlot hK run hreset hGSTstart reset history chain reflect parent hOrigin emission
    decoded receipt honest_slot proposal terminalProposal carrier exactService source_read
    source_eq head_read head_held slot_chain closed roots validRows parentEq matchValid hBatch
    (fun i hi r C hs hh ha => hSOCOVTarget _ hi r C hs hh ha) holderAction
    makeWire wireDecode wireValid client release fields hQC recordHead clientLaws own hsel
    decode occurrence validFor_eq pathValid dutyTime rowDurable rowClock ready step durable
    inv finBlock hI3 readyBlock stored rootScope hStrat hEmittedSource hcapBefore delivery

#print axioms frozen_owner_specialization

end FrozenOwner

namespace Owner

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
private abbrev env (V : Type) : Generic.Env V :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩

private def block : Nat → FGBlock (Fin 1)
  | 0 => .genesis
  | k + 1 => .node (block k) (2 * (k + 1)) ⟨k + 1⟩ 0
      [⟨0, .vote (k + 1) (block k).root false,
        if k = 0 then none else some ⟨k, (block (k - 1)).root⟩⟩]
private abbrev row (k : Nat) : Row (Fin 1) :=
  ⟨0, .vote (k + 1) (block k).root false,
    if k = 0 then none else some ⟨k, (block (k - 1)).root⟩⟩
private def store : Nat → Store (Fin 1)
  | 0 => Store.init
  | k + 1 => SimplexFG.Window.on_block electorate cfg 2 (store k) (block (k + 1))
private abbrev head (k : Nat) : HeadFields :=
  certificateHeadFields (KitFG.Window.certificateHeight electorate cfg 2)
    (KitFG.Window.certificateFinality electorate cfg 2) (block k)
private abbrev objType := V2.Signed Nat (fun _ => 1) (FGBlock (Fin 1) ⊕ Row (Fin 1))
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Fin 8 × RecordOnce
  Label := Nat
  Duty := Time
  signLabel t := if t % 8 = 6 then 0 else t.toNat + 1
  seats _ := 1
  Payload := FGBlock (Fin 1) ⊕ Row (Fin 1)
  Durable := Fin 8 × RecordOnce
  init := (0, RecordOnce.initial)
  clock st _ := st
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act st t _ := if t % 8 = 6 then
    ((createRowOnce electorate cfg st.2 0 (some (block st.1)) (head st.1)).1.map Sum.inr)
    else if 0 < t ∧ t ≤ 56 ∧ t % 8 = 0 then
      some (.inl (block (t.toNat / 8))) else none
  gossip _ _ := []
  process st o := (match o.payload with
    | .inl X => max st.1 ⟨min 7 (X.slot / 2), by omega⟩
    | .inr _ => st.1, st.2)
  selfVisible _ := true
  recordOwn st o := (st.1, if o.auth = .seat 0 0 then
    match o.payload with | .inr u => record_row_once st.2 u | .inl _ => st.2
    else st.2)
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev wire (u : Row (Fin 1)) : protocol.Object := ⟨.seat 0 0, .inr u⟩
private abbrev prop (k : Nat) : protocol.Object :=
  ⟨.seat (8 * k + 1) 0, .inl (block k)⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  if o.auth = .seat 0 0 then
    match o.payload with | .inr u => some u | .inl _ => none
  else none
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase o := match o.payload with | .inl X => some (erase X) | .inr _ => none
  proposalRows o := match o.payload with | .inl X => X.rows.map wire | .inr _ => []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := 0
  fgSeats := Equiv.refl _
  record := Prod.snd
  inputs st := (some (block st.1), head st.1)
  enabled t := decide (t % 8 = 6)
  finalizedOut st := erase (store st.1).F
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core st := ⟨(), store st.1, [], (List.range 7).map (fun k => wire (row k))⟩
  erase := erase
  source st := some (block st.1)
  headVote st _ := erase (block st.1)
  finalityHead st := some (block st.1)
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := KitFG.Window.certificateHeight electorate cfg 2
  finality := KitFG.Window.certificateFinality electorate cfg 2
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X
private abbrev interface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block o := match o with | .inl X => some (erase X) | .inr _ => none
  opening _ := True
  propLabel s := 4 * s + 1
  propDuty s := 4 * s
  propDuty_label s := by
    change (if (4 * s : Int) % 8 = 6 then 0 else (4 * s : Int).toNat + 1) = 4 * s + 1
    have hn : (4 * s : Int) % 8 ≠ 6 := by omega
    rw [ite_eq_right hn]
    have ht : (4 * s : Int) = ((4 * s : Nat) : Int) := by push_cast; rfl
    rw [ht, Int.toNat_natCast]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * a + 1 = 4 * b + 1 at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) (Nat.add_right_cancel h)
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 57
  events := (List.range 58).flatMap fun t =>
    [.tick 9 t, .tick 7 t] ++
    (if t % 8 = 7 then [.deliver 7 (wire (row (t / 8))) t,
        .deliver 9 (wire (row (t / 8))) t] else []) ++
    (if 0 < t ∧ t % 8 = 0 then [.deliver 7 (prop (t / 8)) t,
        .deliver 9 (prop (t / 8)) t] else [])
  seatOf label _ := if label = 0 then 9 else 7
  input _ _ := ()
private abbrev point : FGServicePoint :=
  ⟨⟨0, 22, 3, 3, 6, erase (block 3)⟩, 8, erase (block 4), 32⟩
private abbrev pt : KernelPt := ⟨4⟩

private theorem erase_injective_premises_sat : Function.Injective erase := by
  intro X
  induction X with
  | genesis => intro Y he; cases Y <;> simp_all [erase]
  | node p s r x rs ih =>
    intro Y he
    cases Y with
    | genesis => simp [erase] at he
    | node q t u y ts =>
      simp only [erase, Block.node.injEq] at he
      obtain ⟨hp, hs, hr, hb⟩ := he
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem core_premises_sat : FGCoreLaws core := by
  have mono : ∀ i j : Fin 8, i ≤ j → (store i).TF ⊆ (store j).TF := by decide +kernel
  have mem : ∀ i : Fin 8, block i ∈ (store i).TF := by decide +kernel
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_,
    fun _ _ => List.prefix_rfl, fun _ _ => List.prefix_rfl, fun _ _ => rfl,
    ?_, erase_injective_premises_sat⟩
  · intro nd o
    cases hp : o.payload with
    | inl X =>
      simpa only [core, protocol, hp] using
        (mono nd.1 (max nd.1 ⟨min 7 (X.slot / 2), by omega⟩) (le_max_left _ _))
    | inr u => simpa only [core, protocol, hp] using Finset.Subset.refl (store nd.1).TF
  · intro nd C h
    obtain rfl := Option.some.inj h
    exact mem nd.1

#print axioms core_premises_sat

private theorem client_premises_sat : FGSafetyClientLaws reads electorate cfg where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record nd o := by
    cases o with
    | mk auth payload =>
      cases auth with
      | none => cases payload <;> rfl
      | seat label i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        cases label <;> cases payload <;> rfl
  tick_rows E rho e he nd x t := by
    have hx : e 0 = x := by
      rw [← e.apply_symm_apply x]
      congr 1
      exact Subsingleton.elim _ _
    have hs : e.symm x = 0 := Subsingleton.elim _ _
    have hseat : rho.seatOf 0 0 = x := (he 0).trans hx
    change ((V2.D.tick E rho nd x t).2.filter protocol.objSelfVisible).filterMap decode =
      if E.awake x t = true ∧ decide (t % 8 = 6) = true then
        (createRowOnce electorate cfg nd.2 (e.symm x) (some (block nd.1)) (head nd.1)).1.toList
      else []
    cases ha : E.awake x t <;> by_cases ht : t % 8 = 6
    · simp [V2.D.tick, ha]
    · simp [V2.D.tick, ha]
    · cases hr : (createRowOnce electorate cfg nd.2 0 (some (block nd.1)) (head nd.1)).1 <;>
        simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ,
          ha, ht, hr, hs, decode]
      all_goals
        have hf : List.filter (fun i : Fin 1 =>
            decide (rho.seatOf (if t % 8 = 6 then 0 else t.toNat + 1) i = x)) [0] = [0] := by
          rw [ite_eq_left ht]
          simp [hseat]
        rw [hf]
        rfl
    · by_cases hp : 0 < t ∧ t ≤ 56 ∧ t % 8 = 0
      · by_cases hb : rho.seatOf (protocol.signLabel t) 0 = x <;>
          simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, ht, hb,
            V2.ProtocolSpecD.objSelfVisible, decode]
        all_goals aesop
      · simp [V2.D.tick, ha, ht]
        aesop

#print axioms client_premises_sat

end Owner

end AvailableChain.FGCompose.Tests.PopulationKernel
end
