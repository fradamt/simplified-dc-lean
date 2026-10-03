module
public import AvailableChainFGSAProofs.Proofs.Healing.Export -- shake: keep (Healing claim boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (foundation supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (progress fold supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum -- shake: keep (honest quorum supplier boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

/-- Blueprint 21:1356–1425. Named producers supply all renewed promotion ports.
Recovery₂ supplies the execution, fault, and synchrony facts. -/
theorem fgsa_renewedPromotionClaim : RenewedPromotionClaim p := by
  exact healing_renewedPromotionClaim_of p
    (hmono := fun c E rho => fgsa_rMono p c E rho)
    (hcrossing := by
      intro V _ _ In c E rho G ΔF hrec
      exact fgsa_rXing p c E rho hrec.base.linked
        (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures)
    (hperm := by
      intro V _ _ In c E rho G ΔF hrec
      exact healing_tPerm E rho hrec (fgsa_rMono p c E rho)
        (fgsa_rXing p c E rho hrec.base.linked
          (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures)
        (fgsa_leaseOrigins_lastWrite p c E rho hrec.base.valid.toScheduleWellFormed))
    (hrowsReceipt := by
      intro V _ _ In c E rho G ΔF hrec
      exact fgsa_tRowsReceipt p c E rho ΔF hrec.base.delta hrec.base.valid
        hrec.base.noRestart hrec.sync hrec.deltaF)
    (hprogressCoverage := fun ΔF => fgsa_batchCoverage p ΔF .progress)
    (hfold := fgsa_foldTrichotomy_progress p)
    (hfaultQ := by
      intro V _ _ In c E rho G ΔF hrec
      exact fgsa_faultQ_of_count p hrec.fault)
    (hhonestQuorum := by
      intro V _ _ In c E rho G ΔF hrec
      exact kmid_honest_quorum p c rho hrec.base.linked hrec.fault)

/-- Blueprint 21:1120–1137 and SO-COV. The local producer supplies complete
row coverage at the current action or an earlier action. -/
theorem fgsa_rowPermissionClaim : RowPermissionClaim p := by
  exact healing_rowPermissionClaim_of p
    (hcovered := fun _c E rho => rowPermission_covered E rho)

end AvailableChain.FGSA.Run
end
