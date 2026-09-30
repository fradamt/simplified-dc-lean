module
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Shared
public import AvailableChainFGSAClaims.Claims.Clean

@[expose] public section

/-! P3 §4.8: the exported safety claims. Only the Claims root imports this module.
The zero and positive Clean lane Props are not exported claims. The receipt
and suffix-walk rows cite their existing statements in their claim homes. -/

namespace AvailableChain.FGSA.Run

/-- The complete exported safety-claim aggregate, frozen at G-F0a. -/
structure FGSASafetyClaims (p : FGSA.Params) : Prop where
  carrier : CarrierClaim p
  chainCertificates : ChainCertificatesClaim p
  store : StoreClaim p
  activeView : ActiveViewClaim p
  leaseOrigins : LeaseOriginsClaim p
  reconcile : ReconcileClaim p
  outputNesting : OutputNestingClaim p
  frame : FrameClaim p
  clientSafety : ClientSafetyClaim p
  clientSafetyBase : ClientSafetyBaseClaim p
  sourceDisciplineBase : SourceDisciplineBaseClaim p
  sourceDiscipline : SourceDisciplineClaim p
  sameLabel : SameLabelClaim p
  releaseStore : ReleaseStoreClaim p
  release : ReleaseClaim p
  headReachesLo : HeadReachesLoClaim p
  cleanCut : CleanCutClaim p
  cleanHistory : CleanHistoryClaim p
  cleanPrefixTruncation : CleanPrefixTruncationClaim p
  cleanSafety : CleanSafetyClaim p

end AvailableChain.FGSA.Run
end
