module
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
