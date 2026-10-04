module
public import AvailableChainFGSAProofs.Proofs.Healing.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum

public section

namespace AvailableChain.FGSA.Run

/-- ROOT-DIGEST W2b. Blueprint 21 H.10:1426–1495; plan item S5 PA-ASSEMBLY P2.
DC: SAME four attempt budgets and horizon after the actual start event.
HealingSet supplies recovery. Named producers discharge every standing port. -/
theorem healing_progressAttemptStatement (p : Params) (G ΔF : Time) :
    ProgressAttemptStatement p G ΔF := by
  intro hδ V _ _ In c E rho hset hbound k ev hvalid hstart hhor
  have faultQ := fgsa_faultQ_of_count p hset.fault
  exact healing_progressAttempt E rho hset
    (fgsa_rMono p c E rho)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
      (fgsa_rStore p c E rho))
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho hset.base hset.fault)
    hδ hbound
    (fgsa_tRowsReceipt p c E rho ΔF hset.base.delta hset.base.valid
      hset.base.noRestart hset.sync hset.deltaF)
    (fgsa_batchCoverage p ΔF .progress c E rho)
    (fgsa_foldTrichotomy_progress p) faultQ
    (kmid_honest_quorum p c rho hset.base.linked hset.fault) hvalid hstart hhor

end AvailableChain.FGSA.Run
end
