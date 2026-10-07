module
public import AvailableChainFGCompose.Statements.SafetyStore
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- The FG-SA store laws: the reachable store, its invariant, and the one new block of a
delivery. -/
theorem fgsaSafetyStoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyStoreLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (heightView p) (finalityView p) (fun nd => Reachable p nd.st) := by
  rw [fgsaCoreReads_def, fgsaSafetyReads_def]
  refine
    { initial_good := Reachable.init
      clock_good := fun _ t h => Reachable.tick t h
      process_good := fun _ o h => Reachable.deliver (toWire p o) h
      own_good := fun _ _ h => h
      restart_good := fun _ _ => Reachable.init
      invariant := fun nd h => (storeBundle_of_reachable p nd.st h).cstore.fg
      initial_tf := fun _ hB => Finset.mem_singleton.mp hB
      restart_tf := fun _ _ _ hB => Finset.mem_singleton.mp hB
      process_new := fun nd o B _ hB hn => ?_ }
  change B ∈ (FGSA.process p nd.st (toWire p o)).fg.TF at hB
  obtain ⟨s, N, P, hw, hP, hacc, rfl⟩ := process_TF_new p nd.st (toWire p o) B hB hn
  have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
    apply toWire_injective
    rw [toWire_ofWire, hw]
  subst ho
  obtain ⟨hg, -⟩ := blockAccepted_facts hacc
  have he : eraseFG (fgBlock P N.erase N.rows) = N.erase :=
    eraseFG_fgBlock hg ((parentFG_spec nd.st N.erase P).1 hP).2 N.rows (blockAccepted_rowsOk hacc)
  constructor
  · change safetyProposalErase p (ofWire p ⟨.proposer s, .proposal N⟩) =
      some (eraseFG (fgBlock P N.erase N.rows))
    rw [he, fgsa_safetyProposalErase_def]
    rfl
  · change (fgBlock P N.erase N.rows).rows =
      (safetyProposalRows p (ofWire p ⟨.proposer s, .proposal N⟩)).filterMap RowWire.toRow?
    rw [fgsa_safetyProposalRows_def]
    rfl

/-- The FG-SA order laws: F moves forward and the output is the erased F. -/
theorem fgsaSafetyOrderLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (fgsaCoreReads p c) (fgsaSafetyReads p c) := by
  rw [fgsaCoreReads_def, fgsaSafetyReads_def]
  exact
    { process_F := fun nd o => process_F_mono p nd.st (toWire p o)
      erase_prefix := fun _ _ h => eraseFG_preceq h
      output_eq := fun _ => rfl }

end AvailableChain.FGSA.Run
end
