module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationInduction
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationFrame
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationGate
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationReceipt

public section

namespace AvailableChain.FGSA.Run.Tests.OutageContinuationAxioms

-- Typed audit targets retain the imported proof dependencies in the compiled test.

theorem audit_outageV_iff_vote_bound :
    type_of% (@AvailableChain.FGSA.Run.outageV_iff_vote_bound) :=
  @AvailableChain.FGSA.Run.outageV_iff_vote_bound
#print axioms audit_outageV_iff_vote_bound
theorem audit_outageV_iff_restored_label :
    type_of% (@AvailableChain.FGSA.Run.outageV_iff_restored_label) :=
  @AvailableChain.FGSA.Run.outageV_iff_restored_label
#print axioms audit_outageV_iff_restored_label
theorem audit_outageV_vote_before_expiry :
    type_of% (@AvailableChain.FGSA.Run.outageV_vote_before_expiry) :=
  @AvailableChain.FGSA.Run.outageV_vote_before_expiry
#print axioms audit_outageV_vote_before_expiry
theorem audit_outageV_old_gate_before_expiry :
    type_of% (@AvailableChain.FGSA.Run.outageV_old_gate_before_expiry) :=
  @AvailableChain.FGSA.Run.outageV_old_gate_before_expiry
#print axioms audit_outageV_old_gate_before_expiry
theorem audit_outageV_boundary :
    type_of% (@AvailableChain.FGSA.Run.outageV_boundary) :=
  @AvailableChain.FGSA.Run.outageV_boundary
#print axioms audit_outageV_boundary
theorem audit_outageV_arming_prem :
    type_of% (@AvailableChain.FGSA.Run.outageV_arming_prem) :=
  @AvailableChain.FGSA.Run.outageV_arming_prem
#print axioms audit_outageV_arming_prem
theorem audit_outageV_source_relay_before_freeze :
    type_of% (@AvailableChain.FGSA.Run.outageV_source_relay_before_freeze) :=
  @AvailableChain.FGSA.Run.outageV_source_relay_before_freeze
#print axioms audit_outageV_source_relay_before_freeze
theorem audit_outageV_regression_relay_bound :
    type_of% (@AvailableChain.FGSA.Run.outageV_regression_relay_bound) :=
  @AvailableChain.FGSA.Run.outageV_regression_relay_bound
#print axioms audit_outageV_regression_relay_bound
theorem audit_outage_event_induction_le_expiry :
    type_of% (@AvailableChain.FGSA.Run.outage_event_induction_le_expiry) :=
  @AvailableChain.FGSA.Run.outage_event_induction_le_expiry
#print axioms audit_outage_event_induction_le_expiry
theorem audit_outageV_contest_top :
    type_of% (@AvailableChain.FGSA.Run.outageV_contest_top) :=
  @AvailableChain.FGSA.Run.outageV_contest_top
#print axioms audit_outageV_contest_top
theorem audit_outageV_contested_filter :
    type_of% (@AvailableChain.FGSA.Run.outageV_contested_filter) :=
  @AvailableChain.FGSA.Run.outageV_contested_filter
#print axioms audit_outageV_contested_filter
theorem audit_outageV_entry_above :
    type_of% (@AvailableChain.FGSA.Run.outageV_entry_above) :=
  @AvailableChain.FGSA.Run.outageV_entry_above
#print axioms audit_outageV_entry_above
theorem audit_outageV_taller_carrier :
    type_of% (@AvailableChain.FGSA.Run.outageV_taller_carrier) :=
  @AvailableChain.FGSA.Run.outageV_taller_carrier
#print axioms audit_outageV_taller_carrier
theorem audit_outageV_received_height :
    type_of% (@AvailableChain.FGSA.Run.outageV_received_height) :=
  @AvailableChain.FGSA.Run.outageV_received_height
#print axioms audit_outageV_received_height
theorem audit_outageV_contested_frame_from_rows :
    type_of% (@AvailableChain.FGSA.Run.outageV_contested_frame_from_rows) :=
  @AvailableChain.FGSA.Run.outageV_contested_frame_from_rows
#print axioms audit_outageV_contested_frame_from_rows
theorem audit_outageV_partition_rejects :
    type_of% (@AvailableChain.FGSA.Run.outageV_partition_rejects) :=
  @AvailableChain.FGSA.Run.outageV_partition_rejects
#print axioms audit_outageV_partition_rejects
theorem audit_outageV_result_majority :
    type_of% (@AvailableChain.FGSA.Run.outageV_result_majority) :=
  @AvailableChain.FGSA.Run.outageV_result_majority
#print axioms audit_outageV_result_majority
theorem audit_outageV_gate_compatible :
    type_of% (@AvailableChain.FGSA.Run.outageV_gate_compatible) :=
  @AvailableChain.FGSA.Run.outageV_gate_compatible
#print axioms audit_outageV_gate_compatible
theorem audit_outageV_write_and_normalize :
    type_of% (@AvailableChain.FGSA.Run.outageV_write_and_normalize) :=
  @AvailableChain.FGSA.Run.outageV_write_and_normalize
#print axioms audit_outageV_write_and_normalize

theorem audit_outageV_armed_to_expiry :
    type_of% (@AvailableChain.FGSA.Run.outageV_armed_to_expiry) :=
  @AvailableChain.FGSA.Run.outageV_armed_to_expiry
#print axioms audit_outageV_armed_to_expiry
theorem audit_outageV_marker_frame :
    type_of% (@AvailableChain.FGSA.Run.outageV_marker_frame) :=
  @AvailableChain.FGSA.Run.outageV_marker_frame
#print axioms audit_outageV_marker_frame

theorem audit_outageV_first_restored_exists :
    type_of% (@AvailableChain.FGSA.Run.outageV_first_restored_exists) :=
  @AvailableChain.FGSA.Run.outageV_first_restored_exists
#print axioms audit_outageV_first_restored_exists
theorem audit_outageV_contest_carrier :
    type_of% (@AvailableChain.FGSA.Run.outageV_contest_carrier) :=
  @AvailableChain.FGSA.Run.outageV_contest_carrier
#print axioms audit_outageV_contest_carrier
theorem audit_outageV_gate_of_compatible_batch :
    type_of% (@AvailableChain.FGSA.Run.outageV_gate_of_compatible_batch) :=
  @AvailableChain.FGSA.Run.outageV_gate_of_compatible_batch
#print axioms audit_outageV_gate_of_compatible_batch

theorem audit_outageV_source_path :
    type_of% (@AvailableChain.FGSA.Run.outageV_source_path) :=
  @AvailableChain.FGSA.Run.outageV_source_path
#print axioms audit_outageV_source_path
theorem audit_outageV_path_coverage :
    type_of% (@AvailableChain.FGSA.Run.outageV_path_coverage) :=
  @AvailableChain.FGSA.Run.outageV_path_coverage
#print axioms audit_outageV_path_coverage
theorem audit_outageV_active_path_of_coverage :
    type_of% (@AvailableChain.FGSA.Run.outageV_active_path_of_coverage) :=
  @AvailableChain.FGSA.Run.outageV_active_path_of_coverage
#print axioms audit_outageV_active_path_of_coverage

end AvailableChain.FGSA.Run.Tests.OutageContinuationAxioms
end
