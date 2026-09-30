module
import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (axiom audit commands)
import AvailableChainFGSAProofs.Proofs.Shared.Recurrence -- shake: keep (axiom audit commands)
import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (axiom audit commands)

#print axioms AvailableChain.FGSA.Run.afterTicks_eq_stateBefore
#print axioms AvailableChain.FGSA.Run.afterTicks_node
#print axioms AvailableChain.FGSA.Run.afterTicks_eq_tick_preTick
#print axioms AvailableChain.FGSA.Run.preIdx_le_afterTicksIdx
#print axioms AvailableChain.FGSA.Run.afterTicksIdx_mono

#print axioms AvailableChain.FGSA.Run.fgsa_strongW_recF
#print axioms AvailableChain.FGSA.Run.fgsa_lit_recF
#print axioms AvailableChain.FGSA.Run.fgsa_recPat_restricted
#print axioms AvailableChain.FGSA.Run.fgsa_recPatAt_restricted
#print axioms AvailableChain.FGSA.Run.fgsa_restricted_of_unrestricted
#print axioms AvailableChain.FGSA.Run.fgsa_horizon_mono
#print axioms AvailableChain.FGSA.Run.fgsa_B_max

#print axioms AvailableChain.FGSA.Run.gateResult_eq_saved
#print axioms AvailableChain.FGSA.Run.isGateTime_iff
#print axioms AvailableChain.FGSA.Run.gateResultAt_eq_gateResult
#print axioms AvailableChain.FGSA.Run.vHead_eq_headAtIdx
#print axioms AvailableChain.FGSA.Run.actionSourceFG_eq_round
#print axioms AvailableChain.FGSA.Run.acceptsFinalBefore_of_idx
#print axioms AvailableChain.FGSA.Run.stable_afterTicks

#print axioms AvailableChain.FGSA.Run.card_eq_n_of_linked
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.toCleanCut
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.faultQ_of_pos
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.faultQ
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.batch
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.batchAt
#print axioms AvailableChain.FGSA.Run.Recovery₂.batch
#print axioms AvailableChain.FGSA.Run.fgsa_clean_delivery_iff
#print axioms AvailableChain.FGSA.Run.fgsa_seed_reachable
#print axioms AvailableChain.FGSA.Run.fgsa_seed_accepted
