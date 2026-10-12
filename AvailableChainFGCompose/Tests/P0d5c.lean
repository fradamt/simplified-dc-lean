module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRise

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

#print axioms d5cMovingF
#print axioms d5cRiseExit
#print axioms d5cSeedArms
#print axioms d5cTails
end AvailableChain.FGCompose.Tests.P0d5c
end
end
