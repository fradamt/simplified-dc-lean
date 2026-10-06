module
public import AvailableChainPCSAClaims.Claims.Clean
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun

public section

/-! The snapshot claim export (pcsa34-r4.3 §3.3; proof plan §5). -/

namespace AvailableChain.PCSA.Run

/-- The snapshot contains exactly the PCs held after the freeze ticks. -/
theorem pcsa_snapshotStamp (p : Params) : PCSnapshotStampClaim p := by
  intro V _ _ In c m E rho h y hy s hs
  exact snapshot_afterTicks E rho h.valid.toScheduleWellFormed h.delta y hy s hs

end AvailableChain.PCSA.Run
end
