module
public import AvailableChainPCSAClaims.Claims.Clean
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Clean.Clock
public import AvailableChainPCSAProofs.Proofs.Clean.AckRun
public import AvailableChainPCSAProofs.Proofs.Clean.StepGate
public import AvailableChainPCSAProofs.Proofs.Clean.StepPC
public import AvailableChainPCSAProofs.Proofs.Shared.CleanPC

public section

/-! Clean store support and snapshot claim exports (pcsa34-r4.3; proof plan §5). -/

namespace AvailableChain.PCSA.Run

/-- The snapshot contains exactly the PCs held after the freeze ticks. -/
theorem pcsa_snapshotStamp (p : Params) : PCSnapshotStampClaim p := by
  intro V _ _ In c m E rho h y hy s hs
  exact snapshot_afterTicks E rho h.valid.toScheduleWellFormed h.delta y hy s hs

end AvailableChain.PCSA.Run
end
