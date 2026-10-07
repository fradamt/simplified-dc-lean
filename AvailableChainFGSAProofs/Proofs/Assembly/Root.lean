module
public import AvailableChainFGSAClaims.FGSAClaims
public import AvailableChainFGSAProofs.Proofs.Assembly.Foundations -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Shared -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean
public import AvailableChainFGSAProofs.Proofs.Assembly.Outage -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival
public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation
-- shake: keep (SYN L58 named assembly boundary)

public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth
public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed

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
availableGST, and availableGrowthGST. Each open field is a separate premise.
All ten reduce to HTimeClaim through Shared/Claims; see `fgsaClaims_of_hTime`. -/
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
  weakContinuationLive := fgsa_weakContinuationLiveClaim_of_hTime (healing_hTimeClaim p)

/-- SYN L58: the root from HTimeClaim alone. The FirstFinality, GST liveness and
availability fields come from HTimeClaim and the closed local Rec claims
(Shared/Claims adapters); every other field is as in `fgsaClaims_of_open`. -/
theorem fgsaClaims_of_hTime (hH : HTimeClaim p) : FGSAClaims p :=
  fgsaClaims_of_open p
    (fgsa_firstFinality_recFE hH (fgsa_finalityLivenessRecFE_W p))
    (fgsa_firstFinality_recF4 hH (fgsa_finalityLivenessRecF4_W p))
    (fgsa_finalityLivenessGST_recFE hH (fgsa_finalityLivenessRecFE_W p)
      (fgsa_proposalFinalRecFE_W p) (healing_liveDCFromWindows p))
    (fgsa_finalityLivenessGST_recF4 hH (fgsa_finalityLivenessRecF4_W p)
      (fgsa_proposalFinalRecF4_W p) (healing_liveDCFromWindows p))
    (fgsa_proposalFinalGST_recFE hH (fgsa_proposalFinalRecFE_W p))
    (fgsa_proposalFinalGST_recF4 hH (fgsa_proposalFinalRecF4_W p))
    (fgsa_aboveFrontierGST_recFE hH (fgsa_aboveFrontierRecFE_W p))
    (fgsa_aboveFrontierGST_recF4 hH (fgsa_aboveFrontierRecF4_W p))
    (fgsa_availableGST hH) (fgsa_availableGrowthGST hH)

/-- Blueprint 21 H.18–H.22:3049–3176 and 22 §1; plan S5 NV7 L2.
WC plan §8 Job 4 and r2.1; DC: SAME source-witness order for weak continuation.
The closed HTimeClaim also supplies the ten existing liveness fields. -/
theorem fgsaClaims : FGSAClaims p := fgsaClaims_of_hTime p (healing_hTimeClaim p)

/-- The corruption-growth companion follows from one source witness and
both retained continuation branches. The frozen FGSAClaims field is unchanged. -/
theorem fgsa_weakContinuationGrowthClaim (p : Params) (G : Time) :
    WeakContinuationGrowthClaim p G := by
  intro V _ _ In c ΔF hδ E source hS
  obtain ⟨w, hcut, hseed⟩ := wcg_sourceWitness (healing_hTimeClaim p) hδ hS
  refine ⟨w.u, w.QStar, afterTicksIdx source (SA.gateTime p.toParams w.u), hcut, ?_⟩
  intro E' rho hc
  rcases hc.covered.lt_or_eq with hne | heq
  · exact wcg_nonemptyLive hS hc hne
      (wcg_retainedSeed hS hc hne hseed hcut.beforeEnd.le)
  · exact wcg_emptyLive hS hc heq.symm hseed hcut.beforeEnd.le

end AvailableChain.FGSA.Run
end
