module
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (GST theorem checks)

#check AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recFE
#check AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recF4
#check AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recFE
#check AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recF4
#check AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recFE
#check AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recF4
#check AvailableChain.FGSA.Run.acceptsFinalBefore_mono_deadline

namespace AvailableChain.FGSA.Run

-- Conditional composition checks: both results use the same H-time and local claims.
example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecFEClaim_W p) :
    FirstFinalityRecFEClaim_W p ∧ FinalityLivenessGSTClaim_W p .recFE :=
  ⟨fgsa_firstFinality_recFE hH hL, fgsa_finalityLivenessGST_recFE hH hL⟩

example {p : Params} (hH : HTimeClaim p) (hL : FinalityLivenessRecF4Claim_W p) :
    FirstFinalityRecF4Claim_W p ∧ FinalityLivenessGSTClaim_W p .recF4 :=
  ⟨fgsa_firstFinality_recF4 hH hL, fgsa_finalityLivenessGST_recF4 hH hL⟩

end AvailableChain.FGSA.Run
