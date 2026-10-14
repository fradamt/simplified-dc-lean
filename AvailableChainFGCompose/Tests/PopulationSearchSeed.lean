module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRepair
import all AvailableChainFGCompose.Tests.PopulationService

set_option linter.privateModule false

noncomputable section
namespace AvailableChain.FGCompose.Tests.PopulationSearchSeed
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGCompose.Tests.PopulationService

/-! Generic ordinary-event-fold control: the exact POP-4 mixed run, now consumed by
POP-5's saved-seed theorem. Its proposer is 7; only holder 9 releases an FG row. -/

private abbrev seedObs : FGObservationReads core where
  height := height
  finality := fun _ => ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView height (core.core nd).fg
  viable nd X := treeStoreFrameView height (core.core nd).fg X

private theorem saved_seed_premises_sat :
    FGTimingLaws timing ∧ FGObservationLaws core seedObs ∧
    HonestProposal env run interface 2 .genesis ∧
    V2.D.proposerOf run interface 2 = 7 ∧
    FrontierSeedQualification timing 1 env.t_GST 0 2 ∧
    PhaseInterval core env run seedObs 0 (timing.gate 2) 1 (some .genesis) false ∧
    FrontierProposalService core env run timing 2 .genesis ∧
    FrontierLocalServiceFG core reads env run seedObs timing interface Row.height_pair
      2 .genesis .genesis 1 (timing.gate 2) ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    (∀ x ∈ run.honest, actionSourceFG core env run timing x 1 = some (some .genesis)) := by
  obtain ⟨hp, hproposer, _, _, _, _, hqual, hphase, _⟩ := seed_premises_sat
  obtain ⟨_, _, _, _, _, _, _, hrow, hhead, _, hsource, _, _⟩ := service_premises_sat
  refine ⟨?_, ⟨fun _ => rfl, fun _ _ => rfl⟩, hp, hproposer, hqual, ?_, ?_, ?_, hrow,
    hsource⟩
  · constructor <;> first | decide | (intro s; dsimp only [timing] <;> push_cast <;> ring)
  · exact hphase
  · intro _ x hx _
    exact hhead x hx
  · obtain ⟨hhead, hparent, hstable, hlater, hopen⟩ := mixed_service
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H hx hs ht hh
      exact hhead x s H hx hs (ht.trans (by decide)) hh
    · intro s B hs ht hp
      exact hparent s B hs (ht.trans (by decide)) hp
    · intro i x hx ht hi hit
      exact hstable i x hx (ht.trans (by decide)) hi
        (hit.trans (frontierSearch_timeIdx_mono run (by decide)))
    · intro s B hs ht hp
      exact hlater s B hs (ht.trans (by decide)) hp
    · intro r hq ht
      exact hopen r hq (ht.trans (by decide))

#print axioms saved_seed_premises_sat

end AvailableChain.FGCompose.Tests.PopulationSearchSeed
end
