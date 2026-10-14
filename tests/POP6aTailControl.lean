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

end AvailableChain.FGCompose.Tests.POP6aTail
end
