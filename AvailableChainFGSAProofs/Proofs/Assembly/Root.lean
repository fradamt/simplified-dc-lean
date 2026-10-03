module
public import AvailableChainFGSAClaims.FGSAClaims
public import AvailableChainFGSAProofs.Proofs.Assembly.Foundations -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Shared -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean
public import AvailableChainFGSAProofs.Proofs.Assembly.Outage -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality -- shake: keep (SYN L58 named assembly boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

/-- SYN L58: assemble the safety claims from the lane proofs and the head premise.
The unconditional form is fgsaSafetyClaims below. -/
theorem fgsaSafetyClaims_of_headReachesLo (h : HeadReachesLoClaim p) :
    FGSASafetyClaims p where
  carrier := fgsa_carrierClaim p
  chainCertificates := fgsa_chainCertificatesClaim p
  store := fgsa_storeClaim p
  activeView := fgsa_activeViewClaim p
  leaseOrigins := fgsa_leaseOriginsClaim p
  reconcile := fgsa_reconcileClaim p
  outputNesting := fgsa_outputNestingClaim p
  frame := fgsa_frameClaim p
  clientSafety := fgsa_clientSafetyClaim p
  clientSafetyBase := fgsa_clientSafetyBaseClaim p
  sourceDisciplineBase := fgsa_sourceDisciplineBaseClaim p
  sourceDiscipline := fgsa_sourceDisciplineClaim p
  sameLabel := fgsa_sameLabelClaim p
  releaseStore := fgsa_releaseStoreClaim p
  release := fgsa_releaseClaim p
  headReachesLo := h
  cleanCut := fgsa_cleanCutClaim p
  cleanHistory := fgsa_cleanHistoryClaim p
  cleanPrefixTruncation := fgsa_cleanPrefixTruncationClaim p
  cleanSafety := fgsa_cleanSafetyClaim p

/-- SYN L58: the unconditional safety claims. HeadReachesLoClaim is
fgsa_headReachesLoClaim (P3 F1b.5, Shared/HeadGeometry). -/
theorem fgsaSafetyClaims : FGSASafetyClaims p :=
  fgsaSafetyClaims_of_headReachesLo p (fgsa_headReachesLoClaim p)

/-- SYN L58: assemble all claims with a producer on the base.
The open fields are firstFinalityRecFE, firstFinalityRecF4,
finalityLivenessGSTRecFE, finalityLivenessGSTRecF4, proposalFinalGSTRecFE,
proposalFinalGSTRecF4, aboveFrontierGSTRecFE, aboveFrontierGSTRecF4,
availableGST, and availableGrowthGST. Each open field is a separate premise. -/
theorem fgsaClaims_of_open
    (hFirstFinalityRecFE : FirstFinalityRecFEClaim_W p)
    (hFirstFinalityRecF4 : FirstFinalityRecF4Claim_W p)
    (hFinalityLivenessGSTRecFE : FinalityLivenessGSTClaim_W p .recFE)
    (hFinalityLivenessGSTRecF4 : FinalityLivenessGSTClaim_W p .recF4)
    (hProposalFinalGSTRecFE : ProposalFinalGSTClaim_W p .recFE)
    (hProposalFinalGSTRecF4 : ProposalFinalGSTClaim_W p .recF4)
    (hAboveFrontierGSTRecFE : AboveFrontierGSTClaim_W p .recFE)
    (hAboveFrontierGSTRecF4 : AboveFrontierGSTClaim_W p .recF4)
    (hAvailableGST : AvailableGSTClaim p)
    (hAvailableGrowthGST : AvailableGrowthGSTClaim p) : FGSAClaims p where
  toFGSASafetyClaims := fgsaSafetyClaims p
  finality := {
    accountable := fgsa_pureAccountableClaim p
    agreement := fgsa_pureAgreementClaim p
    runAccountable := fgsa_wholeRunAccountableClaim p
    runAgreement := fgsa_wholeRunAgreementClaim p
    eventPrefixAgreement := fgsa_eventPrefixAgreementClaim p
    faultCountSlashableBound := fgsa_faultCountSlashableBoundClaim p
    finalizedMonotone := fgsa_finalizedMonotonicityClaim p
    honestNeverSlashed := fgsa_honestNeverSlashedClaim p
  }
  finalizedSafety := fgsa_finalizedSafetyClaim p
  finalLock := fgsa_finalLockClaim p
  outageCompat := fgsa_outageCompatClaim_of_clean p (fgsa_cleanCutClaim p)
  fastP1 := fgsa_fastP1Claim_of_clean p (fgsa_cleanCutClaim p)
  slowP1 := fgsa_slowP1Claim_of_clean p (fgsa_cleanCutClaim p)
  exactProposal := fgsa_exactProposalClaim_of_clean p (fgsa_cleanCutClaim p)
  cleanInclusionPostGate := fgsa_cleanInclusionPostGateClaim_of_clean p (fgsa_cleanCutClaim p)
  cleanInclusion := fgsa_cleanInclusionClaim_of_clean p (fgsa_cleanCutClaim p)
  firstFinalityRecFE := hFirstFinalityRecFE
  firstFinalityRecF4 := hFirstFinalityRecF4
  finalityLivenessGSTRecFE := hFinalityLivenessGSTRecFE
  finalityLivenessGSTRecF4 := hFinalityLivenessGSTRecF4
  proposalFinalGSTRecFE := hProposalFinalGSTRecFE
  proposalFinalGSTRecF4 := hProposalFinalGSTRecF4
  aboveFrontierGSTRecFE := hAboveFrontierGSTRecFE
  aboveFrontierGSTRecF4 := hAboveFrontierGSTRecF4
  availableGST := hAvailableGST
  availableGrowthGST := hAvailableGrowthGST
  cleanGrowth := fgsa_cleanGrowthClaim_of_clean p (fgsa_cleanCutClaim p)

end AvailableChain.FGSA.Run
end
