module
import all AvailableChainFGCompose.Tests.PopulationRows

set_option linter.privateModule false
noncomputable section

namespace AvailableChain.FGCompose.Tests.PopulationRowsControls
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGCompose.Tests.PopulationRows

private theorem client_premises_sat :
    (∀ nd, (reads.inputs nd).1 = core.source nd) ∧
    (∀ nd H, core.finalityHead nd = some H →
      (reads.inputs nd).2 = certificateHeadFields obs.height obs.finality H) ∧
    (∀ nd, HighRecordGuard_W (reads.record nd) 3 bBlock ∧
      HighRecordFresh 4 (reads.record nd)) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro nd H hH
    obtain rfl := Option.some.inj hH.symm
    change (⟨3, bBlock.root, 0⟩ : HeadFields) =
      certificateHeadFields obs.height obs.finality dBlock
    decide +kernel
  · intro nd
    simp [HighRecordGuard_W, HighRecordFresh, RecordOnce.initial, Record.initial]


#print axioms client_premises_sat

end AvailableChain.FGCompose.Tests.PopulationRowsControls
end
