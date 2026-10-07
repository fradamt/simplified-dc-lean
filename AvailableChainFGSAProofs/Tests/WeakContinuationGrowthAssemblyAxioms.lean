module
public import AvailableChainFGSAProofs.Proofs.Assembly.Root -- shake: keep (axiom audit)

public section

open AvailableChain.FGSA.Run

#print axioms wcg_sourceLive
#print axioms wcg_nonemptyLive
#print axioms wcg_emptyLive

#print axioms fgsa_weakContinuationGrowthClaim

end
