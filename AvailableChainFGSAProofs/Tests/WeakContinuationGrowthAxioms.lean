module
public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth -- shake: keep (axiom audit)

public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed -- shake: keep (seed axiom audit)

public section

open AvailableChain.FGSA.Run

#print axioms wcg_filtered_replay
#print axioms wcg_eventReplay
#print axioms wcg_beforeReplay
#print axioms wcg_tickEventReplay
#print axioms wcg_readReplay
#print axioms wcg_afterTicksReplay
#print axioms wcg_cut_storeReplay
#print axioms wcg_seed_state
#print axioms wcg_half_of_participation
#print axioms wcg_faultQ_of_half
#print axioms wcg_suffix_faultQ
#print axioms wcg_finalityBlock_of_scope
#print axioms wcg_scope_no_evidence
#print axioms wcg_lowFinalized_of_no_evidence
#print axioms wcg_lowFinalized
#print axioms wcg_init
#print axioms wcg_seededFrame
#print axioms wcg_seededFrameLive
#print axioms wcg_seededFramePath
#print axioms wcg_finalityTargetEarlier
#print axioms wcg_live_of_invariant_inclusion
#print axioms wcg_certifiedOrigin
#print axioms wcg_seedCertified
#print axioms wcg_retained_nonempty
#print axioms wcg_seedCarrier
#print axioms wcg_participation
end
