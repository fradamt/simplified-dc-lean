module
public import AvailableChainPCSAProofs.Proofs.PC.Export
public import AvailableChainPCSAProofs.Proofs.Clean.Export

public section

/-! The proved small claims. The full PCSAClaims record remains separate. -/

namespace AvailableChain.PCSA.Run

/-- C2, C4, and the snapshot claim, for every FG mode. -/
theorem pcsa_smallClaims (p : Params) :
    OneAckPerSlotClaim p ∧ OutputNestingClaim p ∧ PCSnapshotStampClaim p :=
  ⟨pcsa_oneAckPerSlot p, pcsa_outputNesting p, pcsa_snapshotStamp p⟩

end AvailableChain.PCSA.Run
end
