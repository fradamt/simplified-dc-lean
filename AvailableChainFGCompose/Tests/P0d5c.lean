module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTail
public import AvailableChainFGCompose.Proofs.Finality.History

set_option linter.privateModule false

public section
noncomputable section
namespace AvailableChain.FGCompose.Tests.P0d5c
open AvailableChain.SimplexFG AvailableChain.KitFG

-- These are inhabited event-fold interface tests, not ExecutionValid claims.
-- The phase store keeps H = 3, no contest and an F root while the lower F moves;
-- the last delivery raises the frontier.
private def d5cA : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨41⟩ 7 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d5cC : FGBlock (Fin 1) :=
  .node d5cA 2 ⟨43⟩ 9 [⟨0, .vote 2 d5cA.root false, none⟩]
private def d5cE : FGBlock (Fin 1) :=
  .node d5cC 3 ⟨45⟩ 11 [⟨0, .vote 3 d5cC.root false, none⟩]
private def d5cRow : Row (Fin 1) := ⟨0, .vote 3 d5cC.root false, some ⟨0, genesisRoot⟩⟩
private def d5cStopRow : Row (Fin 1) := ⟨0, .vote 4 d5cE.root true, some ⟨1, d5cA.root⟩⟩
private def d5cElectorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def d5cHeight : FGHeightView (Fin 1) := simplexHeightView d5cElectorate ⟨0⟩
private def d5cErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node P s root body _ => .node (d5cErase P) s root body
-- Same phase bits; the lower F root is genesis before the move and d5cA after it.
private def d5cLow : Store (Fin 1) := ⟨{.genesis, d5cA, d5cC}, .genesis, .genesis, 1, 3⟩
private def d5cMoved : Store (Fin 1) := ⟨{.genesis, d5cA, d5cC}, d5cA, .genesis, 1, 3⟩
private def d5cHigh : Store (Fin 1) :=
  ⟨{.genesis, d5cA, d5cC, d5cE}, d5cA, .genesis, 1, 4⟩

private abbrev d5cProtocol : V2.ProtocolSpecD Unit where
  State := Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Store (Fin 1)
  init := d5cLow
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
  gossip _ _ := [d5cRow]
  process _ o := if o.payload = d5cStopRow then d5cHigh else d5cMoved
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

private def d5cCore : FGCoreReads d5cProtocol 1 Unit Unit (Row (Fin 1)) where
  core nd := ⟨(), nd, [], []⟩
  erase := d5cErase
  source _ := some d5cC
  headVote _ _ := d5cErase d5cC
  finalityHead _ := some d5cC
  proposalFG _ _ := none
private def d5cObs : FGObservationReads d5cCore where
  height := d5cHeight
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d5cHeight nd
  viable nd X := treeStoreFrameView d5cHeight nd X
private theorem d5cObsLaws : FGObservationLaws d5cCore d5cObs where
  controls_eq _ := rfl
  viable_eq _ _ := rfl
private def d5cTiming : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private theorem d5cTimingLaws : FGTimingLaws d5cTiming where
  delta_pos := by decide
  rounds := by decide
  proposal_eq s := by simp [d5cTiming]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [d5cTiming]; ring
private abbrev d5cEnv : Generic.Env Unit := ⟨6, by decide, 0, by decide, fun _ _ => true⟩
private def d5cTrace : V2.D.Run Unit d5cProtocol where
  honest := {()}
  horizon := 29
  events := [.deliver () ⟨.none, d5cRow⟩ 2, .deliver () ⟨.none, d5cStopRow⟩ 29]
  seatOf _ _ := ()
  input _ _ := ()

-- G0 (moving lower F inside one phase): the phase interval [1, 5] holds at both indices,
-- while the honest lower F differs between them. No fixed-F interval is assumed.
private theorem d5cMovingF :
    PhaseInterval d5cCore d5cEnv d5cTrace d5cObs 1 5 3 none false ∧
    (d5cCore.core (d5cTrace.stateBefore d5cEnv 0 ())).fg.F ≠
      (d5cCore.core (d5cTrace.stateBefore d5cEnv 1 ())).fg.F ∧
    PhaseInterval d5cCore d5cEnv d5cTrace d5cObs 1 3 3 none false ∧
    (d5cCore.core (d5cTrace.stateBefore d5cEnv 1 ())).fg.h_max = 3 := by
  have hp : PhaseInterval d5cCore d5cEnv d5cTrace d5cObs 1 5 3 none false := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x hui hiv hx
    have hv : timeIdx d5cTrace 5 = 1 := by decide
    rw [hv] at hiv
    cases x
    interval_cases i <;> decide +kernel
  refine ⟨hp, by decide +kernel, frontierSearch_phase_cut _ _ _ _ hp (by decide) (by decide),
    frontierSearch_phase_hmax _ _ _ _ d5cObsLaws hp (i := 1) (by decide) (by decide)
      (by decide)⟩

-- G0 (effective event before service): the frontier rise at index 1 is the first
-- effective event after the start index 0, at time 29, before a seed saved after 29
-- could serve. The rise arm of the phase result is selected, and it is first.
private theorem d5cRiseExit (pair : Row (Fin 1) → NamedHeightPair)
    (S : FGSafetyReads d5cProtocol 1 (Row (Fin 1))) (I : V2.D.Interface d5cProtocol) :
    FirstEffectiveBy d5cCore d5cEnv d5cTrace d5cObs 0 29 ∧
    FrontierHG3Result d5cCore S d5cEnv d5cTrace d5cObs d5cTiming I pair 0 1 0 3 2 29 ∧
    ¬ FirstEffectiveBy d5cCore d5cEnv d5cTrace d5cObs 0 28 := by
  have hrise : frontierAtIdx d5cCore d5cEnv d5cTrace 1 <
      frontierAtIdx d5cCore d5cEnv d5cTrace 2 := by
    decide +kernel
  refine ⟨⟨1, _, by decide, rfl, le_rfl, Or.inl hrise, fun k hk hk' => by omega⟩,
    Or.inr (Or.inl ⟨1, _, by decide, rfl, le_rfl, Or.inl hrise, by decide +kernel,
      fun k hk hk' => by omega⟩), ?_⟩
  rintro ⟨j, ev, hj, hev, ht, _, _⟩
  have hlen := (List.getElem?_eq_some_iff.mp hev).1
  have hj1 : j = 1 := by
    simp only [d5cTrace, List.length_cons, List.length_nil] at hlen
    omega
  subst hj1
  simp only [d5cTrace, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hev
  subst hev
  exact absurd ht (by decide)

-- G0 (both seed arms): a two-label and a one-label seed both follow the phase start;
-- the first-label threshold itself is not a seed, so a served threshold slot is not
-- charged a second repair.
private theorem d5cSeedArms :
    5 ≤ d5cTiming.proposal 6 ∧ 5 ≤ d5cTiming.proposal 4 ∧
    ¬ FrontierSeedQualification d5cTiming 2 0 5 3 := by
  have hstart : FrontierRepairStart d5cEnv d5cTiming 2 5 (2 + 2 * 2 - 1) :=
    FrontierRepairStart.two 2 (by decide) (fun b hb => by
      change (5 : Int) < 4 * (b : Int) at hb
      by_contra h
      have h1 : (b : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      linarith)
  refine ⟨frontierSearch_seed_after d5cTiming 2 d5cTimingLaws (by decide)
      (frontierSearch_seed_of_start d5cEnv d5cTiming 2 hstart (by decide)),
    frontierSearch_seed_after d5cTiming 2 d5cTimingLaws (GST := 0) (by decide)
      (Or.inr ⟨1, by decide, fun i hi => by
        change (5 : Int) ≤ 4 * (i : Int) + 1 at hi
        by_contra h
        have h1 : (i : Int) ≤ 0 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
        linarith, by decide, by decide, by decide⟩), ?_⟩
  rintro (⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, _, _, hlt⟩)
  · have hb2 : β = 2 := by
      refine le_antisymm (hmin 2 (by decide)) ?_
      change (5 : Int) < 4 * (β : Int) at hβ
      by_contra h
      have h1 : (β : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      linarith
    subst hb2
    exact absurd hlt (by decide)
  · have hb1 : b = 1 := by
      refine le_antisymm (hmin 1 (by decide)) ?_
      change (5 : Int) ≤ 4 * (b : Int) + 1 at hb
      by_contra h
      have h1 : (b : Int) ≤ 0 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
      linarith
    subst hb1
    exact absurd hlt (by decide)

-- G0 (tails): the opening period bound is tight at R = 2, and the row deadline P - 4Δ
-- and the rise deadline 2P + Γ - 9Δ are different deadlines.
private theorem d5cTails :
    8 * d5cTiming.delta ≤ FGCompose.P d5cTiming ∧
    FGCompose.P d5cTiming = 8 * d5cTiming.delta ∧
    FGCompose.P d5cTiming - 4 * d5cTiming.delta <
      2 * FGCompose.P d5cTiming + Γ d5cTiming 8 - 9 * d5cTiming.delta := by
  exact ⟨frontierSearch_period_bound d5cTiming d5cTimingLaws, by decide, by decide⟩


/-! G0 (review): the generic contest consumer on an inhabited event-fold model.
One honest node ticks at every public time 0..8. A delivery at 4 raises the frontier to 3
in a contested phase (two height-3 tips, stored J = x2 does not reach y1). A delivery at 8
raises it to 4. No honest proposal exists (the interface decodes no block), so every
proposal leaf holds trivially and no seed can be saved: the contest repair window
closes at the frontier rise. This is an interface model, not an ExecutionValid run. -/

private def c5r (h : Nat) (e : BlockId) : Row (Fin 1) := ⟨0, .vote h e false, none⟩
private def c5x1 : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [c5r 1 genesisRoot]
private def c5x2 : FGBlock (Fin 1) := .node .genesis 1 ⟨2⟩ 0 [c5r 1 genesisRoot]
private def c5y1 : FGBlock (Fin 1) := .node c5x1 2 ⟨3⟩ 0 [c5r 2 ⟨1⟩]
private def c5y2 : FGBlock (Fin 1) := .node c5x2 2 ⟨4⟩ 0 [c5r 2 ⟨2⟩]
private def c5z : FGBlock (Fin 1) := .node c5y1 3 ⟨5⟩ 0 [c5r 3 ⟨3⟩]

private def c5erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (c5erase p) s r (encFGBody x rs)

private theorem c5erase_inj : Function.Injective c5erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [c5erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [c5erase] at h
    | node q t u y ts =>
      simp only [c5erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem c5erase_mono {A B : FGBlock (Fin 1)} (h : FGBlock.Preceq A B) :
    Block.Preceq (c5erase A) (c5erase B) := by
  induction B with
  | genesis =>
    rw [(preceq_genesis).mp h]
    rfl
  | node P s r x rs ih =>
    change (decide (A = .node P s r x rs) || FGBlock.preceq A P) = true at h
    change (decide (c5erase A = c5erase (.node P s r x rs)) ||
      Block.preceq (c5erase A) (c5erase P)) = true
    rw [Bool.or_eq_true] at h ⊢
    rcases h with he | hp
    · exact Or.inl (decide_eq_true (congrArg c5erase (of_decide_eq_true he)))
    · exact Or.inr (ih hp)

private abbrev c5P : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Nat
  init := 0
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
  gossip _ _ := []
  process st _ := st + 1
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

private abbrev c5TF (st : Nat) : Finset (FGBlock (Fin 1)) :=
  if st = 0 then {.genesis} else if st = 1 then {.genesis, c5x1, c5x2, c5y1, c5y2}
  else {.genesis, c5x1, c5x2, c5y1, c5y2, c5z}

private abbrev c5R : FGCoreReads c5P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨c5TF st, .genesis,
    if st = 0 then .genesis else if st = 1 then c5x2 else c5y1,
    if st = 0 then 0 else if st = 1 then 2 else 3,
    if st = 0 then 1 else if st = 1 then 3 else 4⟩, [], []⟩
  erase := c5erase
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private def c5E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def c5cfg : FGConfig := ⟨4⟩
private abbrev c5H := KitFG.Window.certificateHeight c5E c5cfg 2
private abbrev c5F := KitFG.Window.certificateFinality c5E c5cfg 2

private abbrev c5O : FGObservationReads c5R where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (c5R.core nd).fg
  viable nd X := treeStoreFrameView c5H (c5R.core nd).fg X

private theorem c5obs : FGObservationLaws c5R c5O := ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem c5TF_mono (st : Nat) : c5TF st ⊆ c5TF (st + 1) := by
  rcases Nat.lt_or_ge st 2 with h | h
  · interval_cases st <;> decide
  · have h0 : st ≠ 0 := by omega
    have h1 : st ≠ 1 := by omega
    have h2 : st + 1 ≠ 0 := by omega
    have h3 : st + 1 ≠ 1 := by omega
    simp only [c5TF, h0, h1, h2, h3, ite_false]
    exact Finset.Subset.refl _

private theorem c5core : FGCoreLaws c5R where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := c5TF_mono st
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := c5erase_inj

private noncomputable abbrev c5S : FGSafetyReads c5P 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun a => ⟨.none, a⟩
  decode := some
  decodeObject := fun o => some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def c5I : V2.D.Interface c5P where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := none
  opening _ := False
  propLabel s := s
  propDuty s := s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := h

private abbrev c5env : Generic.Env Unit := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private noncomputable abbrev c5rho : V2.D.Run Unit c5P where
  honest := {()}
  horizon := 8
  events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4,
    .deliver () ⟨.none, c5r 9 ⟨9⟩⟩ 4, .tick () 5, .tick () 6, .tick () 7, .tick () 8,
    .deliver () ⟨.none, c5r 9 ⟨9⟩⟩ 8]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem c5nonneg : ∀ e ∈ c5rho.events, 0 ≤ e.time := by decide

private theorem c5schedule : V2.D.ScheduleWellFormed c5env c5rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    exact ⟨c5nonneg e he, by revert e; decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := c5nonneg _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 8 := by
      change ((k : Nat) : Int) * 1 ≤ 8 at hh
      omega
    cases v
    interval_cases k <;> decide


private theorem c5state (i : Nat) : c5rho.stateBefore c5env i () =
    if i ≤ 5 then 0 else if i ≤ 10 then 1 else 2 := by
  rcases Nat.lt_or_ge i 12 with h | h
  · interval_cases i <;> decide +kernel
  · have he : V2.D.Run.stateBefore c5env c5rho i () =
        V2.D.Run.stateBefore c5env c5rho 11 () := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    rw [he]
    simp only [show ¬ i ≤ 5 by omega, show ¬ i ≤ 10 by omega, ↓reduceIte]
    decide +kernel

private theorem c5state_le (i : Nat) : c5rho.stateBefore c5env i () ≤ 2 := by
  rw [c5state]; split_ifs <;> decide

private theorem c5state_mono {i j : Nat} (hij : i ≤ j) :
    c5rho.stateBefore c5env i () ≤ c5rho.stateBefore c5env j () := by
  rw [c5state, c5state]; split_ifs <;> first | decide | omega

private theorem c5store_inv (st : Nat) (hst : st ≤ 2) :
    FGStoreInvariant c5O.height c5O.finality (c5R.core st).fg := by
  interval_cases st
  all_goals
    constructor
    · intro B hB
      change B ∈ c5TF _ at hB
      simp only [c5TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor
      · first
        | exact ⟨.genesis, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5y2, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5z, by decide +kernel, by decide +kernel, rfl, rfl⟩
      · intro B hB _
        change B ∈ c5TF _ at hB
        simp only [c5TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
          show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide] at hB
        rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem c5inv (i : Nat) (x : Unit) : FGStoreInvariant c5O.height c5O.finality
    (c5R.core (c5rho.stateBefore c5env i x)).fg := by
  cases x
  exact c5store_inv _ (c5state_le i)

private theorem c5cert : FGCertificateLaws c5E c5O.height c5O.finality :=
  KitFG.Window.windowCertificateLaws c5E c5cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)

private theorem c5justif : FGJustificationLaws c5O.height :=
  FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge c5E c5cfg 2 (by decide))

private theorem c5TF_le {a b : Nat} (hab : a ≤ b) (hb : b ≤ 2) : c5TF a ⊆ c5TF b := by
  interval_cases b <;> interval_cases a <;> decide

private theorem c5keep : ∀ i j, i ≤ j → ∀ x,
    TFAt c5R c5env c5rho i x ⊆ TFAt c5R c5env c5rho j x := by
  intro i j hij x
  cases x
  exact c5TF_le (c5state_mono hij) (c5state_le j)

private theorem c5mono : FGRunOrderLaws c5env c5rho c5R := by
  constructor
  intro i j x _ hij
  cases x
  have hm := c5state_mono (i := i) (j := j) hij
  have hj := c5state_le j
  generalize c5rho.stateBefore c5env i () = a at hm
  generalize c5rho.stateBefore c5env j () = b at hm hj
  interval_cases b <;> interval_cases a <;> decide

private theorem c5crossing : RXing c5R c5env c5rho c5O := by
  intro i i' x y K W _ _ _ _ _ _
  exact genesis_preceq W

private abbrev c5receipt (B : Block) (d : Time) (y : Unit) : Prop :=
  ∃ W, c5erase W = B ∧ W ∈ (c5R.core (c5rho.stateBeforeTime c5env d y)).fg.TF

private theorem c5noProposal {s : Slot} {Q : Block} (h : HonestProposal c5env c5rho c5I s Q) :
    False := by
  obtain ⟨_, _, _, hb⟩ := h
  cases hb

private theorem c5ready : ∀ t, (4 : Time) ≤ t →
    c5env.t_GST ≤ slotStartZ d5cTiming (((slotAt d5cTiming t : Slot) : Int) - 1) := by
  intro t ht
  have ht' : (4 : Int) ≤ t := ht
  change (0 : Int) ≤ 4 * 1 * ((((t / (4 * 1)).toNat : Nat) : Int) - 1)
  have h1 : (1 : Int) ≤ t / 4 := by omega
  have h2 : (((t / 4).toNat : Nat) : Int) = t / 4 := Int.toNat_of_nonneg (by omega)
  simp only [Int.mul_one] at *
  rw [h2]
  omega

-- Receipt scope at an event of the model: the witness is held at the read deadline.
private theorem c5scope (W : FGBlock (Fin 1)) (d : Time)
    (hW : W ∈ (c5R.core (c5rho.stateBeforeTime c5env d ())).fg.TF) :
    WitnessReceiptScope c5R c5env c5rho (fun _ => true) c5receipt W d :=
  ⟨fun _ y _ _ _ _ _ _ => by cases y; exact ⟨W, rfl, hW⟩⟩

private theorem c5services : ∀ i (ev : V2.Event Unit c5P.Object) m,
    c5rho.events[i]? = some ev → (4 : Time) ≤ ev.time → 1 ≤ m →
    frontierAtIdx c5R c5env c5rho (i + 1) = m → ev.time + d5cTiming.delta ≤ c5rho.horizon →
    PhaseWitnessReceiptScope c5R c5env c5rho c5O (fun _ => true) c5receipt (i + 1) m
      (ev.time + d5cTiming.delta) := by
  intro i ev m hi hJ hm hf hh
  have hlen : i < 11 := (List.getElem?_eq_some_iff.mp hi).1
  interval_cases i <;> simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at hi <;> subst hi <;> revert hf hJ hh
  all_goals
    first
    | (intro _ hJ _; exact absurd hJ (by decide))
    | (intro _ _ hh; exact absurd hh (by decide))
    | (intro hf _ _; subst hf; refine ⟨?_, ?_, ?_⟩)
  all_goals
    first
    | exact ⟨(), c5y1, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        c5scope _ _ (by decide +kernel)⟩
    | exact ⟨(), .genesis, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        c5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), c5y2, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        by decide +kernel, by decide +kernel, c5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), .genesis, ⟨by decide, by decide +kernel⟩, by decide +kernel,
        by decide +kernel, by decide +kernel, c5scope _ _ (by decide +kernel)⟩
    | exact fun _ => ⟨(), c5y2, c5y1, ⟨by decide, by decide +kernel⟩,
        ⟨by decide, by decide +kernel⟩, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, c5scope _ _ (by decide +kernel),
        c5scope _ _ (by decide +kernel)⟩
    | (rintro ⟨x, _, _, hc⟩; cases x; exact absurd hc (by decide +kernel))

private theorem c5start : FrontierSearchStart c5R c5env c5rho c5O d5cTiming 4 5
    (.deliver () ⟨.none, c5r 9 ⟨9⟩⟩ 4) 3 .contest := by
  refine ⟨rfl, by decide, Or.inl (Or.inl (by decide +kernel)), by decide +kernel, by decide,
    ?_⟩
  exact ⟨(), by decide, by decide +kernel, by decide +kernel⟩

-- The phase from 7 cannot reach 8: the delivery at 8 raises the honest frontier.
private theorem c5phase_breaks {v : Time} (hv : 8 ≤ v) {m : Nat}
    {J : Option (FGBlock (Fin 1))} {contested : Bool}
    (hp : PhaseInterval c5R c5env c5rho c5O 7 v m J contested) : False := by
  have hidx : V2.D.Run.idxBefore c5rho 7 = 8 := by decide
  have ht : 11 ≤ timeIdx c5rho v :=
    (show timeIdx c5rho 8 = 11 by decide) ▸ frontierSearch_timeIdx_mono c5rho hv
  have h8 := (hp.2.2.2 8 () (by omega) (by omega) (by decide)).1
  have h11 := (hp.2.2.2 11 () (by omega) ht (by decide)).1
  rw [h8.symm] at h11
  revert h11
  decide +kernel

private theorem c5allowance (ρbar : Time) (hρ : 1 ≤ ρbar) :
    FrontierRepairAllowance c5R c5env c5rho c5O d5cTiming c5I 4 1 4 ρbar 7 := by
  refine ⟨by linarith, 3, FrontierRepairStart.two (u := 7) 2 (by decide) (fun b hb => ?_), ?_⟩
  · change (7 : Int) < 4 * (b : Int) at hb
    by_contra h
    have : (b : Int) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (Nat.lt_of_not_le h)
    linarith
  · intro _ v m J contested _ hp
    refine ⟨fun s Q _ _ hQ => (c5noProposal hQ).elim, fun hb => ?_⟩
    exact (c5phase_breaks (by linarith) hp).elim

-- G0 (contest exit, event before service): the generic contest consumer applied with
-- every premise proved on the model. The repair window [7, 8] closes at the rise.
private theorem c5contest :
    FrontierHG3Result c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 5 3 4
      (4 + (1 + 3 * d5cTiming.delta)) :=
  frontier_hg3_contest c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 c5E c5obs
    c5cert c5inv c5justif c5keep (by decide) c5core (fun h => c5erase_mono h)
    (fun _ => true) c5receipt d5cTimingLaws le_rfl c5crossing c5schedule c5mono rfl
    (by decide) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) c5ready c5services
    (fun W d y _ h => by
      obtain ⟨W', he, hW'⟩ := h
      exact c5erase_inj he ▸ hW')
    (G := 4) (by decide)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hQ _ => (c5noProposal hQ).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ hQ => (c5noProposal hQ).elim)
    (fun _ _ _ _ _ _ _ _ _ hQ _ _ _ _ _ _ _ _ _ => (c5noProposal hQ).elim)
    c5start (c5allowance 1 le_rfl) (by decide)

-- Inspection: the selected exit is the first rise at index 10 (time 8, the closed
-- deadline); no phase stop and no saved seed exist.
private theorem c5contestExit :
    FirstRiseStopBy c5R c5env c5rho c5O 5 3 8 ∧
    ¬ FirstPhaseStopBy c5R c5env c5rho c5O 5 3 8 ∧
    ¬ (∃ t, StrongServed c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 3 t) ∧
    ¬ FirstEffectiveBy c5R c5env c5rho c5O 5 7 := by
  have hnoserve : ¬ (∃ t, StrongServed c5R c5S c5env c5rho c5O d5cTiming c5I
      Row.height_pair 4 1 3 t) := by
    rintro ⟨t, _, _, _, _, _, _, _, hQ, _⟩
    exact c5noProposal hQ
  have hnophase : ¬ FirstPhaseStopBy c5R c5env c5rho c5O 5 3 8 := by
    rintro ⟨j, ev, hj, hev, _, heff, hf, _⟩
    have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert heff hf; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
  refine ⟨?_, hnophase, hnoserve, ?_⟩
  · rcases c5contest with h | h | h
    · exact (hnophase h).elim
    · exact h
    · obtain ⟨t, _, _, hs⟩ := h
      exact (hnoserve ⟨t, hs⟩).elim
  · rintro ⟨j, ev, hj, hev, ht, heff, _⟩
    have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert heff; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
      | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))

-- Bad trace: with the repair allowance shortened to 0 (deadline 7), the phase still holds
-- through 7 with no honest proposal, so the local repair service fails and no result of
-- the consumer holds by 7. All other premises are those proved above.
private theorem c5shortened :
    ¬ FrontierRepairAllowance c5R c5env c5rho c5O d5cTiming c5I 4 1 4 0 7 ∧
    ¬ FrontierHG3Result c5R c5S c5env c5rho c5O d5cTiming c5I Row.height_pair 4 1 5 3 4 7 := by
  have hp7 : PhaseInterval c5R c5env c5rho c5O 7 7 3 none true := by
    refine ⟨le_rfl, by decide, by decide, ?_⟩
    intro i x hi hi' _
    cases x
    have h1 : V2.D.Run.idxBefore c5rho 7 = 8 := by decide
    have h2 : timeIdx c5rho 7 = 9 := by decide
    rw [h1] at hi
    rw [h2] at hi'
    interval_cases i <;> decide +kernel
  refine ⟨?_, ?_⟩
  · rintro ⟨_, l, _, hrep⟩
    obtain ⟨_, hex⟩ := hrep (by decide) 7 3 none true (by decide) hp7
    obtain ⟨s, Q, _, _, hQ, _⟩ := hex (by decide)
    exact c5noProposal hQ
  · rintro (⟨j, ev, hj, hev, ht, heff, _⟩ | ⟨j, ev, hj, hev, ht, heff, _⟩ | ⟨t, _, _, hs⟩)
    rotate_left 2
    · obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hs
      exact c5noProposal hQ
    all_goals
      have hlen : j < 11 := (List.getElem?_eq_some_iff.mp hev).1
      interval_cases j <;> first
        | omega
        | (revert heff; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
        | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))


/-! G0 (review): the generic row tail on an inhabited event-fold model.
One honest node ticks at every public time 0..18. It signs an entry-1 row at action 0
(time 6), proposes erase x1 for slot 2 at time 8 and signs an entry-2 row at action 1
(time 14). Deliveries at 7 and 15 raise the frontier to 2 and to 3. The saved seed is the
slot-2 proposal in the phase [8, 14] at height 2; its continuing service is proved for
each capped endpoint. This is an interface model, not an ExecutionValid run. -/

private def r6row1 : Row (Fin 1) := c5r 1 genesisRoot
private def r6row2 : Row (Fin 1) := c5r 2 ⟨1⟩

private abbrev r6P : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1) ⊕ Block
  Durable := Nat
  init := 0
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
  act _ d _ := if d = 6 then some (.inl r6row1) else if d = 14 then some (.inl r6row2)
    else if d = 8 then some (.inr (c5erase c5x1)) else none
  gossip _ _ := []
  process st _ := st + 1
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

private abbrev r6TF (st : Nat) : Finset (FGBlock (Fin 1)) :=
  if st = 0 then {.genesis} else if st = 1 then {.genesis, c5x1} else {.genesis, c5x1, c5y1}

private abbrev r6R : FGCoreReads r6P 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨r6TF st, .genesis, if st ≤ 1 then .genesis else c5x1,
    if st = 0 then 0 else if st = 1 then 1 else 2,
    if st = 0 then 1 else if st = 1 then 2 else 3⟩, [], []⟩
  erase := c5erase
  source st := if st = 0 then none else some c5x1
  headVote _ _ := c5erase c5x1
  finalityHead _ := none
  proposalFG _ _ := none

private abbrev r6O : FGObservationReads r6R where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (r6R.core nd).fg
  viable nd X := treeStoreFrameView c5H (r6R.core nd).fg X

private noncomputable abbrev r6S : FGSafetyReads r6P 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode a := ⟨.seat (if a = r6row1 then 6 else 14) 0, .inl a⟩
  decode := some
  decodeObject o := match o.payload with | .inl a => some a | .inr _ => none
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (none, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun _ => false
  finalizedOut := fun _ => .genesis

private def r6I : V2.D.Interface r6P where
  confirmed _ := .genesis
  stable _ := .genesis
  block p := match p with | .inr B => some B | .inl _ => none
  opening _ := False
  propLabel s := 4 * s
  propDuty s := 4 * s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective _ _ h := Nat.eq_of_mul_eq_mul_left (by decide) h

private noncomputable abbrev r6rho : V2.D.Run Unit r6P where
  honest := {()}
  horizon := 18
  events := [.tick () 0, .tick () 1, .tick () 2, .tick () 3, .tick () 4, .tick () 5,
    .tick () 6, .tick () 7, .deliver () ⟨.none, .inl (c5r 9 ⟨9⟩)⟩ 7, .tick () 8,
    .tick () 9, .tick () 10, .tick () 11, .tick () 12, .tick () 13, .tick () 14,
    .tick () 15, .deliver () ⟨.none, .inl (c5r 9 ⟨9⟩)⟩ 15, .tick () 16, .tick () 17,
    .tick () 18]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem r6nonneg : ∀ e ∈ r6rho.events, 0 ≤ e.time := by decide

private theorem r6schedule : V2.D.ScheduleWellFormed c5env r6rho where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    exact ⟨r6nonneg e he, by revert e; decide⟩
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h := r6nonneg _ ht
    refine ⟨t.toNat, ?_⟩
    simp only [V2.Event.time] at h
    change (t : Int) = ((t.toNat : Nat) : Int) * 1
    rw [Int.toNat_of_nonneg h, Int.mul_one]
  tick_total := by
    intro v _ t ht _ hh _
    obtain ⟨k, rfl⟩ := ht
    have hk : k ≤ 18 := by
      change ((k : Nat) : Int) * 1 ≤ 18 at hh
      omega
    cases v
    interval_cases k <;> decide

private theorem r6state (i : Nat) : r6rho.stateBefore c5env i () =
    if i ≤ 8 then 0 else if i ≤ 17 then 1 else 2 := by
  rcases Nat.lt_or_ge i 22 with h | h
  · interval_cases i <;> decide +kernel
  · have he : V2.D.Run.stateBefore c5env r6rho i () =
        V2.D.Run.stateBefore c5env r6rho 21 () := by
      unfold V2.D.Run.stateBefore
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    rw [he]
    simp only [show ¬ i ≤ 8 by omega, show ¬ i ≤ 17 by omega, ↓reduceIte]
    decide +kernel

private theorem r6state_le (i : Nat) : r6rho.stateBefore c5env i () ≤ 2 := by
  rw [r6state]; split_ifs <;> decide

private theorem r6state_mono {i j : Nat} (hij : i ≤ j) :
    r6rho.stateBefore c5env i () ≤ r6rho.stateBefore c5env j () := by
  rw [r6state, r6state]; split_ifs <;> first | decide | omega

private theorem r6store_inv (st : Nat) (hst : st ≤ 2) :
    FGStoreInvariant r6O.height r6O.finality (r6R.core st).fg := by
  interval_cases st
  all_goals
    constructor
    · intro B hB
      change B ∈ r6TF _ at hB
      simp only [r6TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
        show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide] at hB
      rcases hB with rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor
      · first
        | exact ⟨.genesis, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5x1, by decide +kernel, by decide +kernel, rfl, rfl⟩
        | exact ⟨c5y1, by decide +kernel, by decide +kernel, rfl, rfl⟩
      · intro B hB _
        change B ∈ r6TF _ at hB
        simp only [r6TF, ite_true, ite_false, Finset.mem_insert, Finset.mem_singleton,
          show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
          show (2 : Nat) ≠ 1 by decide] at hB
        rcases hB with rfl | rfl | rfl <;> decide +kernel
    · decide +kernel
    · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem r6inv (i : Nat) (x : Unit) : FGStoreInvariant r6O.height r6O.finality
    (r6R.core (r6rho.stateBefore c5env i x)).fg := by
  cases x
  exact r6store_inv _ (r6state_le i)

private theorem r6cert : FGCertificateLaws c5E r6O.height r6O.finality := c5cert

private theorem r6mono : FGRunOrderLaws c5env r6rho r6R := by
  constructor
  intro i j x _ hij
  cases x
  have hm := r6state_mono (i := i) (j := j) hij
  have hj := r6state_le j
  generalize r6rho.stateBefore c5env i () = a at hm
  generalize r6rho.stateBefore c5env j () = b at hm hj
  interval_cases b <;> interval_cases a <;> decide

private abbrev r6chain (_ : r6P.State) (_ : Block) : List (Row (Fin 1)) := [r6row1, r6row2]

private theorem r6row1At : HonestRowAt r6S c5env r6rho d5cTiming 6 () 0 r6row1 := by
  unfold HonestRowAt; decide +kernel

private theorem r6row2At : HonestRowAt r6S c5env r6rho d5cTiming 15 () 1 r6row2 := by
  unfold HonestRowAt; decide +kernel

private theorem r6cap : RCap r6R r6S c5env r6rho r6O d5cTiming
    (fun a => namedEntry (Row.height_pair a)) r6chain := by
  intro y i x W hW hy
  change y + 2 ≤ (c5H W).h at hy
  obtain ⟨hx, hW⟩ := hW
  cases x
  change W ∈ r6TF (r6rho.stateBefore c5env i ()) at hW
  rw [r6state] at hW
  split_ifs at hW with h1 h2
  · simp only [r6TF, ite_true, Finset.mem_singleton] at hW
    subst hW
    have : (c5H FGBlock.genesis).h = 1 := by decide +kernel
    simp only [Height] at *
    omega
  · simp only [r6TF, show (1 : Nat) ≠ 0 by decide, ite_true, ite_false, Finset.mem_insert,
      Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · have : (c5H FGBlock.genesis).h = 1 := by decide +kernel
      simp only [Height] at *
      omega
    · have hy0 : y = 0 := by
        have : (c5H c5x1).h = 2 := by decide +kernel
        simp only [Height] at *
        omega
      subst hy0
      exact ⟨6, (), 0, r6row1, genesisRoot, by omega, r6row1At, rfl, by simp⟩
  · simp only [r6TF, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false,
      Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl | rfl
    · have : (c5H FGBlock.genesis).h = 1 := by decide +kernel
      simp only [Height] at *
      omega
    · have hy0 : y = 0 := by
        have : (c5H c5x1).h = 2 := by decide +kernel
        simp only [Height] at *
        omega
      subst hy0
      exact ⟨6, (), 0, r6row1, genesisRoot, by omega, r6row1At, rfl, by simp⟩
    · have hy1 : y ≤ 1 := by
        have : (c5H c5y1).h = 3 := by decide +kernel
        simp only [Height] at *
        omega
      interval_cases y
      · exact ⟨6, (), 0, r6row1, genesisRoot, by omega, r6row1At, rfl, by simp⟩
      · exact ⟨15, (), 1, r6row2, ⟨1⟩, by simp only [Height] at *; omega, r6row2At, rfl, by simp⟩

private theorem r6proposal : HonestProposal c5env r6rho r6I 2 (c5erase c5x1) := by
  refine ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, .inr (c5erase c5x1)⟩, ⟨9, ?_, ?_⟩, rfl⟩
  · decide +kernel
  · decide +kernel

private theorem r6phase : PhaseInterval r6R c5env r6rho r6O 8 14 2 (some .genesis) false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro i x hi hi' _
  cases x
  have h1 : V2.D.Run.idxBefore r6rho 8 = 9 := by decide
  have h2 : timeIdx r6rho 14 = 16 := by decide
  rw [h1] at hi
  rw [h2] at hi'
  interval_cases i <;> decide +kernel

-- Continuing service of the saved seed: the cap holds only through 14, where every
-- clause is checked on the actual reads (HEAD at label 3, opening 1 with its signed
-- entry-2 row and source x1).
private theorem r6service : ∀ v, d5cTiming.gate 2 ≤ v → v ≤ r6rho.horizon →
    (∀ i x, timeIdx r6rho 8 ≤ i → i ≤ timeIdx r6rho v → x ∈ r6rho.honest →
      (r6R.core (r6rho.stateBefore c5env i x)).fg.h_max ≤ 2) →
    FrontierLocalService r6R r6S c5env r6rho r6O d5cTiming r6I Row.height_pair 2
      (c5erase c5x1) c5x1 2 v := by
  intro v hv hvh hcap
  have hv14 : v = 14 := by
    by_contra hne
    have hv15 : (15 : Time) ≤ v := by
      have hv' : (14 : Int) ≤ v := hv
      have hne' : (v : Int) ≠ 14 := hne
      simp only [Height, Time] at *
      omega
    have ht : 18 ≤ timeIdx r6rho v :=
      (show timeIdx r6rho 15 = 18 by decide) ▸ frontierSearch_timeIdx_mono r6rho hv15
    have h := hcap 18 () (by decide) ht (by decide)
    revert h
    decide +kernel
  subst hv14
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x s H _ hs hvs hH
    have hs3 : s = 3 := by
      have hvs' : 4 * ((s : Nat) : Int) + 1 ≤ 14 := hvs
      have hs' : 3 ≤ (s : Nat) := hs
      simp only [Slot, Height, Time] at *
      omega
    subst hs3
    cases x
    have : headAtLabel r6R c5env r6rho d5cTiming () 3 = some (c5erase c5x1) := by
      decide +kernel
    rw [this] at hH
    cases hH
    decide
  · intro s B hs hps _
    have hps' : 4 * ((s : Nat) : Int) ≤ 14 := hps
    have hs' : 4 ≤ (s : Nat) := hs
    simp only [Slot, Height, Time] at *
    omega
  · intro i x _ h
    exact absurd h (by decide)
  · intro s B hlt hg _
    have hlt' : 4 * (2 : Int) < 4 * ((s : Nat) : Int) := hlt
    have hg' : 4 * ((s : Nat) : Int) + 6 ≤ 14 := hg
    simp only [Height, Time] at *
    omega
  · intro r hr hrt
    have hr1 : r = 1 := by
      have hrt' : 8 * ((r : Nat) : Int) + 6 ≤ 14 := hrt
      have hr' : 2 ≤ (r : Nat) * 2 := hr
      simp only [Slot, Height, Time] at *
      omega
    subst hr1
    have hsrc : actionSourceFG r6R c5env r6rho d5cTiming () 1 = some (some c5x1) := by
      decide +kernel
    refine ⟨?_, ⟨⟨1⟩, fun x K _ hK => ?_⟩, fun x K _ hK => ?_, fun _ => by decide⟩
    · intro x _
      cases x
      exact ⟨c5x1, 1, 15, 1, r6row2, by decide +kernel, hsrc, by decide +kernel,
        by decide, le_rfl, r6row2At, by decide +kernel⟩
    · cases x
      rw [hsrc] at hK
      cases hK
      exact ⟨by decide +kernel, by decide +kernel⟩
    · cases x
      rw [hsrc] at hK
      cases hK
      rfl

private theorem r6row :
    FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2
      (14 + (FGCompose.P d5cTiming - 4 * d5cTiming.delta)) :=
  healing_frontierTail_row r6R r6S c5env r6rho r6O d5cTiming r6I Row.height_pair r6chain c5E
    r6cert r6inv d5cTimingLaws r6schedule r6mono r6cap r6phase r6proposal le_rfl r6service
    (by decide)


private theorem r6emits (j : Nat) : V2.D.Run.emitsAt c5env r6rho j =
    if j = 6 then [r6S.encode r6row1] else if j = 15 then [r6S.encode r6row2]
    else if j = 9 then [⟨.seat 8 0, .inr (c5erase c5x1)⟩] else [] := by
  rcases Nat.lt_or_ge j 21 with h | h
  · interval_cases j <;> decide +kernel
  · have hn : r6rho.events[j]? = none := List.getElem?_eq_none (by simp; omega)
    simp only [V2.D.Run.emitsAt, hn, show j ≠ 6 by omega, show j ≠ 15 by omega,
      show j ≠ 9 by omega, ↓reduceIte]

-- Every honest row of the model is the entry-1 row at action 0 or the entry-2 row at 1.
private theorem r6rows {j : Nat} {y : Unit} {r : Nat} {a : Row (Fin 1)}
    (h : HonestRowAt r6S c5env r6rho d5cTiming j y r a) :
    (j = 6 ∧ r = 0 ∧ a = r6row1) ∨ (j = 15 ∧ r = 1 ∧ a = r6row2) := by
  obtain ⟨_, hj, hem⟩ := h
  rw [r6emits] at hem
  have hl : j < 21 := (List.getElem?_eq_some_iff.mp hj).1
  cases y
  interval_cases j <;> simp [d5cTiming] at hem hj ⊢
  · exact ⟨hj, hem⟩
  · have h' : (14 : Int) = 8 * ((r : Nat) : Int) + 6 := hj
    exact ⟨by omega, hem.2⟩

-- Inspection: the row tail selects the entry-2 row of action 1 (time 14) as the first
-- height-2 row; the row deadline 14 + (P - 4Δ) = 18 is closed. Bad trace: the shortened
-- deadline 13 has no height-2 row, with every premise of the tail retained.
private theorem r6rowExit :
    FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2 18 ∧
    (∀ r, HeightRow r6S c5env r6rho d5cTiming (fun a => namedEntry (Row.height_pair a)) r 2 →
      r = 1) ∧
    ¬ FirstHeightRowBy r6S c5env r6rho d5cTiming Row.height_pair 2 13 := by
  have honly : ∀ r, HeightRow r6S c5env r6rho d5cTiming
      (fun a => namedEntry (Row.height_pair a)) r 2 → r = 1 := by
    rintro r ⟨j, y, a, e, hrow, he⟩
    rcases r6rows hrow with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
    · exact absurd he (by simp [r6row1, c5r, namedEntry])
    · rfl
  refine ⟨r6row, honly, ?_⟩
  rintro ⟨r, hr, _, ht⟩
  have := honly r hr
  subst this
  exact absurd ht (by decide)


-- Strongest proved partial for the top-J consumer (producer gap recorded in the report):
-- an inhabited top-J start at the delivery of time 7, and the exit its result selects,
-- the first rise at index 17 (time 15), within the exact top-J deadline 7 + E_jF = 23.
private theorem r6topExit :
    FrontierSearchStart r6R c5env r6rho r6O d5cTiming 4 8
      (.deliver () ⟨.none, .inl (c5r 9 ⟨9⟩)⟩ 7) 2 .topJ ∧
    (7 : Time) + E_jF d5cTiming 1 4 0 = 23 ∧
    FrontierHG3Result r6R r6S c5env r6rho r6O d5cTiming r6I Row.height_pair 4 1 8 2 7
      (7 + E_jF d5cTiming 1 4 0) ∧
    ¬ FirstEffectiveBy r6R c5env r6rho r6O 8 14 := by
  have hstart : FrontierSearchStart r6R c5env r6rho r6O d5cTiming 4 8
      (.deliver () ⟨.none, .inl (c5r 9 ⟨9⟩)⟩ 7) 2 .topJ := by
    refine ⟨rfl, by decide, Or.inl (Or.inl (by decide +kernel)), by decide +kernel,
      by decide, ?_, ?_⟩
    · exact ⟨(), by decide, by decide +kernel⟩
    · rintro ⟨x, _, hH, hc⟩
      cases x
      exact absurd hc (by decide +kernel)
  have hdl : (7 : Time) + E_jF d5cTiming 1 4 0 = 23 := by decide
  have hrise : FirstRiseStopBy r6R c5env r6rho r6O 8 2 15 := by
    refine ⟨17, _, by decide, rfl, le_rfl, Or.inl (by decide +kernel), by decide +kernel, ?_⟩
    intro k hk hk'
    interval_cases k <;>
      (unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
  refine ⟨hstart, hdl, Or.inr (Or.inl ?_), ?_⟩
  · obtain ⟨j, ev, hj, hev, ht, he, hm, hq⟩ := hrise
    exact ⟨j, ev, hj, hev, ht.trans (by rw [hdl]; decide), he, hm, hq⟩
  · rintro ⟨j, ev, hj, hev, ht, heff, _⟩
    have hlen : j < 21 := (List.getElem?_eq_some_iff.mp hev).1
    interval_cases j <;> first
      | omega
      | (revert heff; unfold EffectiveEvent TopEvidence ContestEvidence; decide +kernel)
      | (simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hev; subst hev; exact absurd ht (by decide))

#print axioms d5cMovingF
#print axioms d5cRiseExit
#print axioms d5cSeedArms
#print axioms d5cTails
#print axioms c5contest
#print axioms c5contestExit
#print axioms c5shortened
#print axioms r6row
#print axioms r6rowExit
#print axioms r6topExit
end AvailableChain.FGCompose.Tests.P0d5c
end
end
