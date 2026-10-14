module
import all AvailableChainFGCompose.Tests.PopulationSearchSeed
import all AvailableChainFGCompose.Tests.PopulationSearchPhase
import AvailableChainFGCompose.Proofs.Population.FrontierSearchRise

-- Standalone generic event-fold controls; exact accepted private fixture data are reused.
noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6aTail
open AvailableChain.SimplexFG AvailableChain.KitFG
open PopulationSearchSeed PopulationSearchSeed.Fixture
open PopulationSearchPhase.Fixture

private abbrev tailCore : FGCoreReads missingProtocol 1 Unit Unit (Row (Fin 1)) :=
  { missingCore with headVote := fun _ _ => .genesis }

private abbrev tailObs : FGObservationReads tailCore where
  height := c5H
  finality := c5F
  controls nd := treeStoreControlsView c5H (tailCore.core nd).fg
  viable nd X := treeStoreFrameView c5H (tailCore.core nd).fg X

private abbrev tailRows (_ : missingProtocol.State) (_ : Block) : List (Row (Fin 1)) := [row]

private theorem geometry_premises_sat {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V missingProtocol) :
    FGCertificateLaws c5E tailObs.height tailObs.finality ∧
    (∀ i x, FGStoreInvariant tailObs.height tailObs.finality
      (tailCore.core (rho.stateBefore E i x)).fg) ∧
    FGRunOrderLaws E rho tailCore ∧
    RCap tailCore missingReads E rho tailObs timing
      (fun a => namedEntry (Row.height_pair a)) tailRows ∧
    (∀ i x, (tailCore.core (rho.stateBefore E i x)).fg.h_max = 1) := by
  refine ⟨c5cert, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro i x
    change FGStoreInvariant c5H c5F Store.init
    constructor <;> decide +kernel
  · constructor
    intro i j x _ _
    exact ⟨show FGBlock.Preceq (FGBlock.genesis : FGBlock (Fin 1)) .genesis from rfl,
      le_rfl, le_rfl⟩
  · intro y i x W hW hy
    have hgen : W = .genesis := Finset.mem_singleton.mp hW.2
    subst W
    have hh : (tailObs.height FGBlock.genesis).h = 1 := by decide +kernel
    rw [hh] at hy
    exact (Nat.not_succ_le_self 1 ((Nat.le_add_left 2 y).trans hy)).elim

#print axioms geometry_premises_sat

private theorem mixed_premises_sat :
    V2.D.ScheduleWellFormed env missingRun ∧ FGTimingLaws timing ∧
    (FGHonestSeats missingReads missingRun).Nonempty ∧
    HonestProposal env missingRun missingIface 2 .genesis ∧
    PhaseInterval tailCore env missingRun tailObs 0 (timing.gate 2) 1
      (some .genesis) false ∧
    (∀ v, timing.gate 2 ≤ v → v ≤ missingRun.horizon →
      FrontierLocalServiceFG tailCore missingReads env missingRun tailObs timing missingIface
        Row.height_pair 2 .genesis .genesis 1 v) ∧
    HonestRowAt missingReads env missingRun timing 13 9 0 row ∧
    (∀ x ∈ missingRun.honest,
      actionSourceFG tailCore env missingRun timing x 1 = some (some .genesis)) ∧
    V2.D.proposerOf missingRun missingIface 2 = 7 ∧
    timing.action 0 = 6 ∧ timing.action 1 = 14 ∧
    14 + (FGCompose.P timing - 4 * timing.delta) ≤ missingRun.horizon := by
  have hrow : HonestRowAt missingReads env missingRun timing 13 9 0 row := by
    unfold HonestRowAt
    decide +kernel
  have hsource : ∀ x ∈ missingRun.honest,
      actionSourceFG tailCore env missingRun timing x 1 = some (some .genesis) := by
    intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  have hc : OpeningCoveredFG tailCore missingReads env missingRun c5H timing Row.height_pair
      (FGHonestSeats missingReads missingRun) 1 .genesis := by
    intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨.genesis, missingRun.stateBefore env 29 9, 13, 0, row,
      rfl, hsource 9 (by decide), by decide, by decide, by decide, hrow, rfl⟩
  refine ⟨missing_receiver_premises_sat.1, saved_seed_premises_sat.1,
    ⟨0, by decide⟩, missing_receiver_premises_sat.2.2.2.2.1, ?_, ?_, hrow, hsource,
    rfl, rfl, rfl, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro v _ hv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H _ _ _ hH
      obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hH
      change Block.genesis = H at he
      subst H
      rfl
    · intro s B _ _ hp
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      rfl
    · intro i x _ _ _ _
      rfl
    · intro s B _ _ hp ht x hx _
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      have hs : (s : Nat) ≤ 4 := by
        change 4 * (s : Int) + 1 ≤ 18 at ht
        simp only [Slot, Time] at *
        omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> interval_cases s <;> decide +kernel
    · intro r hqr ht
      have hrt := ht.trans hv
      change @LE.le Nat _ 2 (r * 2) at hqr
      change 8 * (r : Int) + 6 ≤ 18 at hrt
      have hr : @Eq Nat r 1 := by omega
      subst r
      refine ⟨hc, ⟨genesisRoot, ?_⟩, ?_, fun _ => by decide⟩
      · intro x K hx hK
        rw [hsource x hx] at hK
        cases hK
        exact ⟨rfl, rfl⟩
      · intro x K hx hK
        rw [hsource x hx] at hK
        cases hK
        rfl

#print axioms mixed_premises_sat

private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (hj : missingRun.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    missingReads.encode a ∉ V2.D.Run.emitsAt env missingRun j := by
  have table : ∀ k : Fin 38, missingRun.events[k.val]?.map V2.Event.node = some 7 →
      (V2.D.Run.emitsAt env missingRun k.val).all
        (fun o => decide (o.auth ≠ .seat 6 0)) = true := by
    decide +kernel
  have hlen : j < 38 := (List.getElem?_eq_some_iff.mp hj).1
  have hnode : missingRun.events[j]?.map V2.Event.node = some 7 := by rw [hj]; rfl
  have hsafe := table ⟨j, hlen⟩ hnode
  intro ha
  have hn := of_decide_eq_true ((List.all_eq_true.mp hsafe) (missingReads.encode a) ha)
  exact hn rfl

#print axioms nonholder_no_encoded

end AvailableChain.FGCompose.Tests.POP6aTail
end
