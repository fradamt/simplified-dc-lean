module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGSAProofs.Proofs.Healing.RepairCover

public section

/-! Strict audit of the round-seven selected services and bounded consumers. -/

#print axioms AvailableChain.FGSA.Run.healing_selected_carriers_recovery
#print axioms AvailableChain.FGSA.Run.healing_self_proposal_service
#print axioms AvailableChain.FGSA.Run.repair_lease_cover_two_at
#print axioms AvailableChain.FGSA.Run.repair_lease_cover_one_at
#print axioms AvailableChain.FGSA.Run.frontier_gate_scope_of_cover
#print axioms AvailableChain.FGSA.Run.frontier_gate_fast_count
#print axioms AvailableChain.FGSA.Run.frontier_retained_reader_floor
#print axioms AvailableChain.FGSA.Run.frontier_service
#print axioms AvailableChain.FGSA.Run.healing_proposal_service_at_recovery_anchor
#print axioms AvailableChain.FGSA.Run.healing_target_receipt_at_event
#print axioms AvailableChain.FGSA.Run.healing_witness_receipt_at_event
#print axioms AvailableChain.FGSA.Run.healing_phase_witness_receipts_recovery
#print axioms AvailableChain.FGSA.Run.healing_phase_block_receipt_recovery
#print axioms AvailableChain.FGSA.Run.healing_evidence_spread_recovery
#print axioms AvailableChain.FGSA.Run.healing_rPhase_recovery

end
