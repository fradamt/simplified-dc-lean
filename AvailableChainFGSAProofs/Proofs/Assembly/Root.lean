module
public import AvailableChainFGSAClaims.FGSAClaims
public import AvailableChainFGSAProofs.Proofs.Assembly.Foundations -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Shared -- shake: keep (SYN L58 named assembly boundary)
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

/-- SYN L58: assemble the safety claims from the lane proofs and the head premise.
The proof of HeadReachesLoClaim (fgsa_headReachesLoClaim, fgsa-lean F1b.5)
is not on main yet. The unconditional fgsaSafetyClaims follows when it lands. -/
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

end AvailableChain.FGSA.Run
end
