module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchTop
import all AvailableChainFGCompose.Proofs.Population.FrontierSearchTop
import all AvailableChainFGCompose.Tests.P0d5c

set_option linter.privateModule false

noncomputable section
namespace AvailableChain.FGCompose.Tests.PopulationSearchPhase
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGCompose.Tests.P0d5c

/-! Generic ordinary-event-fold fixture. Both honest runtime nodes tick at every time
0..42. The FG seat belongs to 9; proposals at slots 1, 5 and 7 belong to 7. The low
seed has height 1; its first opening uses 9's original action-0 row. The actual
slot-5 carrier raises the proposal to height 2 at the original gate time 26. -/

private abbrev low : FGBlock (Fin 1) := .node .genesis 1 ⟨101⟩ 0 []
private abbrev firstRow : Row (Fin 1) := ⟨0, .vote 1 genesisRoot true, none⟩
private abbrev middle : FGBlock (Fin 1) := .node low 5 ⟨105⟩ 0 [firstRow]
private abbrev late : FGBlock (Fin 1) := .node middle 7 ⟨107⟩ 0 []
private abbrev nextRow : Row (Fin 1) := ⟨0, .vote 2 middle.root true, none⟩
private abbrev chainAt (s : Nat) : FGBlock (Fin 1) :=
  if s ≤ 1 then low else if s ≤ 5 then middle else late
private abbrev sourceAt (t : Time) : FGBlock (Fin 1) :=
  if t < 14 then .genesis else if t < 30 then low else middle
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Time
  Label := Time
  Duty := Time
  signLabel t := if t = 6 ∨ t = 30 then 6 else t
  seats _ := 1
  Payload := Row (Fin 1) ⊕ FGBlock (Fin 1)
  Durable := Time
  init := 0
  clock _ t := t
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act _ t _ := if t = 6 then some (.inl firstRow)
    else if t = 30 then some (.inl nextRow)
    else if t = 4 then some (.inr low)
    else if t = 20 then some (.inr middle)
    else if t = 28 then some (.inr late) else none
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
private abbrev env : Generic.Env Nat := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 42
  events := (List.range 43).flatMap fun (t : Nat) => [.tick 7 (t : Time), .tick 9 (t : Time)]
  seatOf l _ := if l = 6 then 9 else if l = 4 ∨ l = 20 ∨ l = 28 then 7 else 0
  input _ _ := ()
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.seat 6 0, .inl a⟩
  decode := some
  decodeObject o := match o.auth with
    | .seat l _ => if l = 6 then o.payload.getLeft? else none
    | .none => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs t := (some (sourceAt t), ⟨0, genesisRoot, 0⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev stored (top : Bool) : Finset (FGBlock (Fin 1)) :=
  if top then {.genesis, low, middle, late, c5x1} else {.genesis, low, middle, late}
private abbrev core (top : Bool) : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), ⟨stored top, .genesis, .genesis, if top then 1 else 0, 2⟩, [],
    [firstRow, nextRow]⟩
  erase := c5erase
  source t := some (sourceAt t)
  headVote _ s := c5erase (chainAt s)
  finalityHead _ := some .genesis
  proposalFG _ _ := none
private abbrev obs (top : Bool) : FGObservationReads (core top) where
  height := c5H
  finality := c5F
  controls st := treeStoreControlsView c5H ((core top).core st).fg
  viable st X := treeStoreFrameView c5H ((core top).core st).fg X
private abbrev iface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := c5erase late
  block p := match p with | .inr X => some (c5erase X) | .inl _ => none
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label s := by
    change (if 4 * (s : Int) = 6 ∨ 4 * (s : Int) = 30 then 6 else 4 * (s : Int)) = _
    rw [ite_eq_right (by omega)]
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_inj.mp (by omega)
private abbrev wire : FGHistoryWireReads reads where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer a := some a.signer
  decode_height _ _ h := by cases h; rfl
  decode_finality _ _ h := by cases h; rfl
  decode_signer _ _ h := by cases h; rfl
private abbrev decodeProposal (o : protocol.Object) : Option (Slot × FGBlock (Fin 1)) :=
  match o.payload with | .inr X => some (X.slot, X) | .inl _ => none
private abbrev parentFG (t : Time) (_ : Block) : Option (FGBlock (Fin 1)) :=
  if t = 4 then some .genesis else if t = 20 then some low else some middle
private abbrev fold (_ : Time) (_ : Slot) (P : FGBlock (Fin 1)) := Window.derive c5E c5cfg 2 P
private abbrev parentHeight (t : Time) (s : Slot) (P : FGBlock (Fin 1)) : Height × BlockId :=
  ((fold t s P).h, (fold t s P).T_h.root)
private abbrev validFor (t : Time) (s : Slot) (P : FGBlock (Fin 1)) (a : Row (Fin 1)) :=
  Window.r6w (fold t s P) a

private theorem geometry_premises_sat (top : Bool) :
    FGCertificateLaws c5E (obs top).height (obs top).finality ∧
    FGObservationLaws (core top) (obs top) ∧
    (∀ i x, FGStoreInvariant (obs top).height (obs top).finality
      ((core top).core (run.stateBefore env i x)).fg) ∧
    (c5H low).h = 1 ∧ (c5H middle).h = 2 ∧ (c5H late).h = 2 ∧
    (c5H low).T_h = .genesis ∧ (c5H middle).T_h = middle ∧ (c5H late).T_h = middle ∧
    PhaseInterval (core top) env run (obs top) 0 42 2
      (if top then some .genesis else none) false := by
  refine ⟨c5cert, ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    cases top <;> constructor <;> dsimp [obs, core] <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · refine ⟨by decide, le_rfl, by decide, ?_⟩
    intro i x _ _ _
    cases top <;> dsimp [obs, core] <;> decide +kernel

#print axioms geometry_premises_sat

private theorem execution_premises_sat :
    V2.D.ScheduleWellFormed env run ∧ FGHonestSeats reads run = {0} ∧
    c5E.weightOf (historyFaulty reads run) < c5E.q ∧
    HonestRowAt reads env run d5cTiming 13 9 0 firstRow ∧
    HonestRowAt reads env run d5cTiming 61 9 3 nextRow ∧
    protocol.objSelfVisible (reads.encode firstRow) = true ∧
    reads.decodeObject (reads.encode firstRow) = some firstRow ∧
    (∀ x ∈ run.honest, ∀ r ≤ 4,
      postClock env run x (d5cTiming.action r) = some (d5cTiming.action r)) ∧
    (∀ x ∈ run.honest, ∀ s ≤ 10,
      postClock env run x (d5cTiming.vote s) = some (d5cTiming.vote s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      dsimp only [run] at ht
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp ht
      have hk' : (x = 7 ∧ t = (k : Time)) ∨ (x = 9 ∧ t = (k : Time)) := by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          V2.Event.tick.injEq] using hk
      rcases hk' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨k, by simp⟩
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 43 := by change (k : Int) * 1 ≤ 42 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      dsimp only [run, env]
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rcases hx' with rfl | rfl <;> simp
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide
  · decide
  · unfold HonestRowAt
    decide +kernel
  · unfold HonestRowAt
    decide +kernel
  · intro x hx r hr
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> interval_cases r <;> decide +kernel
  · intro x hx s hs
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> interval_cases s <;> decide +kernel

#print axioms execution_premises_sat

private theorem proposal_premises_sat :
    (∀ s, Gen.V2.Duty.HonestSlot run iface s → s = 1 ∨ s = 5 ∨ s = 7) ∧
    (∀ s, s = 1 ∨ s = 5 ∨ s = 7 →
      HonestCarrier env run iface (kernelCarrier decodeProposal c5erase FGBlock.rows)
        s (c5erase (chainAt s)) (chainAt s).rows) := by
  constructor
  · intro s hs
    have hp := hs.2
    change (if 4 * (s : Int) = 6 then 9 else
      if 4 * (s : Int) = 4 ∨ 4 * (s : Int) = 20 ∨ 4 * (s : Int) = 28
      then 7 else 0) ∈ ({7, 9} : Finset Nat) at hp
    split_ifs at hp with h6 hslot
    · omega
    · rcases hslot with h | h | h
      · exact Or.inl (Int.ofNat.inj (show (s : Int) = 1 by omega))
      · exact Or.inr (Or.inl (Int.ofNat.inj (show (s : Int) = 5 by omega)))
      · exact Or.inr (Or.inr (Int.ofNat.inj (show (s : Int) = 7 by omega)))
    · simp at hp
  · intro s hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨?_, ⟨.seat 4 0, .inr low⟩,
        ⟨8, by decide +kernel, by decide +kernel⟩, low, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 4 0, .inr low⟩,
        ⟨8, by decide +kernel, by decide +kernel⟩, rfl⟩
    · refine ⟨?_, ⟨.seat 20 0, .inr middle⟩,
        ⟨40, by decide +kernel, by decide +kernel⟩, middle, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 20 0, .inr middle⟩,
        ⟨40, by decide +kernel, by decide +kernel⟩, rfl⟩
    · refine ⟨?_, ⟨.seat 28 0, .inr late⟩,
        ⟨56, by decide +kernel, by decide +kernel⟩, late, rfl, rfl, rfl⟩
      refine ⟨⟨by decide, by decide⟩, ⟨.seat 28 0, .inr late⟩,
        ⟨56, by decide +kernel, by decide +kernel⟩, rfl⟩

#print axioms proposal_premises_sat

private theorem proposal_unique {s : Slot} {Q : Block}
    (hp : HonestProposal env run iface s Q) :
    (s = 1 ∨ s = 5 ∨ s = 7) ∧ Q = c5erase (chainAt s) := by
  have hs := proposal_premises_sat.1 s hp.1
  refine ⟨hs, ?_⟩
  obtain ⟨_, o, ⟨j, hj, ho⟩, hb⟩ := hp
  have hjlt : j < 86 := (List.getElem?_eq_some_iff.mp hj).1
  rcases hs with rfl | rfl | rfl
  · have hu : ∀ k : Fin 86, run.events[k.val]? = some (.tick 7 4) → k.val = 8 := by
      decide +kernel
    have hj' : j = 8 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 4 0, .inr low⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm
  · have hu : ∀ k : Fin 86, run.events[k.val]? = some (.tick 7 20) → k.val = 40 := by
      decide +kernel
    have hj' : j = 40 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 20 0, .inr middle⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm
  · have hu : ∀ k : Fin 86, run.events[k.val]? = some (.tick 7 28) → k.val = 56 := by
      decide +kernel
    have hj' : j = 56 := hu ⟨j, hjlt⟩ hj
    subst j
    change o ∈ [⟨.seat 28 0, .inr late⟩] at ho
    have ho' := List.mem_singleton.mp ho
    subst o
    exact (Option.some.inj hb).symm

#print axioms proposal_unique

end AvailableChain.FGCompose.Tests.PopulationSearchPhase
end
