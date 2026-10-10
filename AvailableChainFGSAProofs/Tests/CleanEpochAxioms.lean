module
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate
public import AvailableChainFGSAProofs.Proofs.Clean.StateEpoch
public import AvailableChainFGSAProofs.Proofs.Clean.Frame

public section

#print axioms AvailableChain.FGSA.Run.clean_gate_enabled_of_result
#print axioms AvailableChain.FGSA.Run.clean_gate_executed
#print axioms AvailableChain.FGSA.Run.clean_gate_raw_enabled
#print axioms AvailableChain.FGSA.Run.clean_gate_nonempty_raw
#print axioms AvailableChain.FGSA.Run.clean_gate_unjoined
#print axioms AvailableChain.FGSA.Run.clean_restart_marker_after
#print axioms AvailableChain.FGSA.Run.clean_enabledGate_awakeClosed
#print axioms AvailableChain.FGSA.Run.clean_enabledGate_restartFreeTime
#print axioms AvailableChain.FGSA.Run.clean_enabledGate_of_joinedAt
#print axioms AvailableChain.FGSA.Run.clean_joined_witness
#print axioms AvailableChain.FGSA.Run.clean_joined_gate_witness
#print axioms AvailableChain.FGSA.Run.cleanResults_mono
#print axioms AvailableChain.FGSA.Run.belowLabel_mono_index
#print axioms AvailableChain.FGSA.Run.belowLabel_mono_label
#print axioms AvailableChain.FGSA.Run.belowLabel_of_preceq
#print axioms AvailableChain.FGSA.Run.belowLabel_genesis
#print axioms AvailableChain.FGSA.Run.belowLabel_of_mem
#print axioms AvailableChain.FGSA.Run.belowLabel_of_gateResultAt
#print axioms AvailableChain.FGSA.Run.cleanHist_restrict
#print axioms AvailableChain.FGSA.Run.cleanHist_results_compatible
#print axioms AvailableChain.FGSA.Run.cleanHist_belowLabel_compatible
#print axioms AvailableChain.FGSA.Run.cleanHist_belowLabel_preceq_result
#print axioms AvailableChain.FGSA.Run.cleanHist_zero
#print axioms AvailableChain.FGSA.Run.cleanResults_mem_succ_iff
#print axioms AvailableChain.FGSA.Run.clean_gate_raw
#print axioms AvailableChain.FGSA.Run.clean_gate_store
#print axioms AvailableChain.FGSA.Run.clean_state_gate_guard
#print axioms AvailableChain.FGSA.Run.clean_gate_passed
#print axioms AvailableChain.FGSA.Run.clean_gate_writes
#print axioms AvailableChain.FGSA.Run.clean_gate_lease_targets
#print axioms AvailableChain.FGSA.Run.clean_gate_fast_prefix
#print axioms AvailableChain.FGSA.Run.clean_gate_output_compatible
#print axioms AvailableChain.FGSA.Run.clean_gate_sExtends
#print axioms AvailableChain.FGSA.Run.clean_gate_sOrigin
#print axioms AvailableChain.FGSA.Run.clean_gate_leases
#print axioms AvailableChain.FGSA.Run.clean_gate_saved
#print axioms AvailableChain.FGSA.Run.clean_gate_savedOnly
#print axioms AvailableChain.FGSA.Run.clean_gate_fastAt
#print axioms AvailableChain.FGSA.Run.clean_gate_fastWrite
#print axioms AvailableChain.FGSA.Run.clean_gate_fields_all

#print axioms AvailableChain.FGSA.Run.clean_restart_fields
#print axioms AvailableChain.FGSA.Run.cleanHist_step_restart
#print axioms AvailableChain.FGSA.Run.clean_enabledGate_service_epoch
#print axioms AvailableChain.FGSA.Run.clean_gate_fg_before_time

#print axioms AvailableChain.FGSA.Run.cleanFrame_of_state

end
