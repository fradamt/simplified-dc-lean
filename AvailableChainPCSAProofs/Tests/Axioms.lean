module
public import AvailableChainPCSAProofs.Proofs.AcFrame.Height
public import AvailableChainPCSAProofs.Proofs.AcFrame.Rows
public import AvailableChainPCSAProofs.Proofs.AcFrame.Run
public import AvailableChainPCSAProofs.Proofs.AcFrame.Store
public import AvailableChainPCSAProofs.Proofs.Assembly.AcFrame
public import AvailableChainPCSAProofs.Proofs.Assembly.Small
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainPCSAProofs.Proofs.Foundations.Output
public import AvailableChainPCSAProofs.Proofs.Foundations.OutputState
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Snapshot
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotKeys
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Foundations.StampRun
public import AvailableChainPCSAProofs.Proofs.Foundations.Stamps
public import AvailableChainPCSAProofs.Proofs.Foundations.Store
public import AvailableChainPCSAProofs.Proofs.PC.AckOrigins
public import AvailableChainPCSAProofs.Proofs.PC.Certificates
public import AvailableChainPCSAProofs.Proofs.PC.HeadSupport
public import AvailableChainPCSAProofs.Proofs.PC.RunEvidence
public import AvailableChainPCSAProofs.Proofs.PC.StoreEvidence
public import AvailableChainPCSAProofs.Proofs.PC.Uniqueness

public section

/-! PC-SA proof axiom audit (proof plan §3). -/

#print axioms AvailableChain.PCSA.Run.pcsa_acOnlyFrame
#print axioms AvailableChain.PCSA.pcsa_faults_lt_fg_quorum
#print axioms AvailableChain.PCSA.pcsa_window_no_quorum
#print axioms AvailableChain.PCSA.Run.pcsa_ac_no_row_emission
#print axioms AvailableChain.PCSA.Run.pcsa_ac_carried_row_faulty
#print axioms AvailableChain.PCSA.Run.pcsa_ac_delivered_row_faulty
#print axioms AvailableChain.PCSA.Run.pcsa_ac_block_rows_faulty
#print axioms AvailableChain.PCSA.Run.pcsa_initial_acSafe
#print axioms AvailableChain.PCSA.Run.pcsa_ac_storeSafe
#print axioms AvailableChain.PCSA.Run.pcsa_ac_frame
#print axioms AvailableChain.PCSA.AcStoreSafe_def
#print axioms AvailableChain.PCSA.pcsa_normalizeS_fg
#print axioms AvailableChain.PCSA.pcsa_reconcile_fg
#print axioms AvailableChain.PCSA.pcsa_clock_fg
#print axioms AvailableChain.PCSA.pcsa_fold_admitRow_fg
#print axioms AvailableChain.PCSA.pcsa_fold_poolAckRaw_fg
#print axioms AvailableChain.PCSA.pcsa_admitBlock_fg_cases
#print axioms AvailableChain.PCSA.pcsa_on_block_acSafe
#print axioms AvailableChain.PCSA.pcsa_child_rows
#print axioms AvailableChain.PCSA.pcsa_process_acSafe
#print axioms AvailableChain.PCSA.pcsa_acSafe_frame
#print axioms AvailableChain.PCSA.Run.pcsa_acFrameClaim
#print axioms AvailableChain.PCSA.Run.pcsa_smallClaims
#print axioms AvailableChain.PCSA.Run.pcsa_snapshotStamp
#print axioms AvailableChain.PCSA.poolAckRaw_mono
#print axioms AvailableChain.PCSA.mem_poolAckRaw
#print axioms AvailableChain.PCSA.poolAckRaw_mem
#print axioms AvailableChain.PCSA.poolAckRaw_frame
#print axioms AvailableChain.PCSA.poolAck_mono
#print axioms AvailableChain.PCSA.mem_poolAck
#print axioms AvailableChain.PCSA.acksOn_subset
#print axioms AvailableChain.PCSA.mem_acksOn_iff
#print axioms AvailableChain.PCSA.Run.signLabel_ack_iff
#print axioms AvailableChain.PCSA.Run.pcsa_duties_early
#print axioms AvailableChain.PCSA.Run.earlyTime_succ_eq_gateTime
#print axioms AvailableChain.PCSA.Run.clock_early_succ
#print axioms AvailableChain.PCSA.Run.early_gate_duty_order
#print axioms AvailableChain.PCSA.Run.ack_emission_duty
#print axioms AvailableChain.PCSA.Run.ack_emission_unique
#print axioms AvailableChain.PCSA.installPC_frame
#print axioms AvailableChain.PCSA.installPC_duplicate
#print axioms AvailableChain.PCSA.installPC_pcs_new
#print axioms AvailableChain.PCSA.installPC_pcs_mono
#print axioms AvailableChain.PCSA.mem_installPC_pcs
#print axioms AvailableChain.PCSA.installPC_stamp_new
#print axioms AvailableChain.PCSA.assemblePC_some_iff
#print axioms AvailableChain.PCSA.pcsa_assemblePC_valid
#print axioms AvailableChain.PCSA.collectPCs_preserves
#print axioms AvailableChain.PCSA.collectPCs_invariant
#print axioms AvailableChain.PCSA.collectPCs_pcs_mono
#print axioms AvailableChain.PCSA.collectPCs_frame
#print axioms AvailableChain.PCSA.mem_deleteConflictingLeases
#print axioms AvailableChain.PCSA.deleteConflictingLeases_subset
#print axioms AvailableChain.PCSA.deleteConflictingLeases_keep
#print axioms AvailableChain.PCSA.deleteConflictingLeases_rank
#print axioms AvailableChain.PCSA.writeLease_rank
#print axioms AvailableChain.PCSA.writeLease_frame
#print axioms AvailableChain.PCSA.leaseWriteOK_iff
#print axioms AvailableChain.PCSA.confirmed_eq_pcFloor
#print axioms AvailableChain.PCSA.strong_preceq_confirmed
#print axioms AvailableChain.PCSA.finalized_preceq_confirmed
#print axioms AvailableChain.PCSA.normalizeS_outputSafe
#print axioms AvailableChain.PCSA.reconcile_outputSafe
#print axioms AvailableChain.PCSA.installPC_outputSafe
#print axioms AvailableChain.PCSA.collectPCs_outputSafe
#print axioms AvailableChain.PCSA.poolAckRaw_outputSafe
#print axioms AvailableChain.PCSA.poolAck_outputSafe
#print axioms AvailableChain.PCSA.admitRow_outputSafe
#print axioms AvailableChain.PCSA.fold_poolAckRaw_outputSafe
#print axioms AvailableChain.PCSA.fold_admitRow_outputSafe
#print axioms AvailableChain.PCSA.process_outputSafe
#print axioms AvailableChain.PCSA.clock_outputSafe
#print axioms AvailableChain.PCSA.reachable_outputSafe
#print axioms AvailableChain.PCSA.reachable_outputNesting
#print axioms AvailableChain.PCSA.pcsa_preferPC_isSome
#print axioms AvailableChain.PCSA.pcsa_preferPC_eq_or
#print axioms AvailableChain.PCSA.pcsa_preferPC_idem
#print axioms AvailableChain.PCSA.foldl_preferPC_mem
#print axioms AvailableChain.PCSA.bestPC_mem
#print axioms AvailableChain.PCSA.bestPC_nil
#print axioms AvailableChain.PCSA.bestPC_singleton
#print axioms AvailableChain.PCSA.Run.pcsa_reachable_stateBefore
#print axioms AvailableChain.PCSA.Run.reachable_storeAt
#print axioms AvailableChain.PCSA.Run.pcsa_tick_st
#print axioms AvailableChain.PCSA.Run.reachable_storeAfterTicks
#print axioms AvailableChain.PCSA.pcSnapshotAt_absent
#print axioms AvailableChain.PCSA.pcSnapshotAt_append
#print axioms AvailableChain.PCSA.pcSnapshotAt_eq_of_list_eq
#print axioms AvailableChain.PCSA.clockPre_pcs
#print axioms AvailableChain.PCSA.clockPre_pcStamps
#print axioms AvailableChain.PCSA.clockPre_output_fields
#print axioms AvailableChain.PCSA.gateFrom_pc_frame
#print axioms AvailableChain.PCSA.clockPre_freeze_snapshot
#print axioms AvailableChain.PCSA.freezeTime_ne_gateTime
#print axioms AvailableChain.PCSA.clock_freeze
#print axioms AvailableChain.PCSA.clock_freeze_snapshot
#print axioms AvailableChain.PCSA.gateRank_candidate_iff
#print axioms AvailableChain.PCSA.gateRank_empty
#print axioms AvailableChain.PCSA.gateRank_eq
#print axioms AvailableChain.PCSA.normalizeS_snapshot
#print axioms AvailableChain.PCSA.reconcile_snapshot_keys
#print axioms AvailableChain.PCSA.poolAckRaw_snapshot
#print axioms AvailableChain.PCSA.fold_poolAckRaw_snapshot
#print axioms AvailableChain.PCSA.admitRow_snapshot
#print axioms AvailableChain.PCSA.fold_admitRow_snapshot
#print axioms AvailableChain.PCSA.process_snapshot_keys
#print axioms AvailableChain.PCSA.gateFrom_snapshot
#print axioms AvailableChain.PCSA.gateStep_snapshot
#print axioms AvailableChain.PCSA.clockPre_snapshot
#print axioms AvailableChain.PCSA.clock_snapshot_origin
#print axioms AvailableChain.PCSA.Run.snapshot_key_origin
#print axioms AvailableChain.PCSA.Run.snapshot_absent_before_tick
#print axioms AvailableChain.PCSA.Run.snapshot_afterTicks
#print axioms AvailableChain.PCSA.Run.stampBound_before_tick
#print axioms AvailableChain.PCSA.Run.pcStamp_before_freeze_iff
#print axioms AvailableChain.PCSA.StampBound_def
#print axioms AvailableChain.PCSA.held_pcStamp
#print axioms AvailableChain.PCSA.installPC_stampBound
#print axioms AvailableChain.PCSA.normalizeS_stampBound
#print axioms AvailableChain.PCSA.reconcile_stampBound
#print axioms AvailableChain.PCSA.poolAckRaw_stampBound
#print axioms AvailableChain.PCSA.admitRow_stampBound
#print axioms AvailableChain.PCSA.process_stampBound
#print axioms AvailableChain.PCSA.gateFrom_stampBound
#print axioms AvailableChain.PCSA.clock_stampBound
#print axioms AvailableChain.PCSA.initial_pcs
#print axioms AvailableChain.PCSA.Run.AckOrigin_def
#print axioms AvailableChain.PCSA.Run.certSafe_stateBefore
#print axioms AvailableChain.PCSA.Run.certSafe_storeAt
#print axioms AvailableChain.PCSA.Run.ackOrigin_emits
#print axioms AvailableChain.PCSA.Run.fresh_faulty_card
#print axioms AvailableChain.PCSA.Run.held_pc_honest_ack
#print axioms AvailableChain.PCSA.pcsa_firstPerSeat_subset
#print axioms AvailableChain.PCSA.assemblePC_acks
#print axioms AvailableChain.PCSA.CertSafe_def
#print axioms AvailableChain.PCSA.collectPCs_certSafe
#print axioms AvailableChain.PCSA.poolAckRaw_certSafe
#print axioms AvailableChain.PCSA.normalizeS_certSafe
#print axioms AvailableChain.PCSA.reconcile_certSafe
#print axioms AvailableChain.PCSA.admitRow_certSafe
#print axioms AvailableChain.PCSA.process_certSafe
#print axioms AvailableChain.PCSA.gateFrom_certSafe
#print axioms AvailableChain.PCSA.clock_certSafe
#print axioms AvailableChain.PCSA.Run.pcsa_pcUniqueness
#print axioms AvailableChain.PCSA.Run.pcsa_oneAckPerSlot
#print axioms AvailableChain.PCSA.Run.pcsa_outputNesting
#print axioms AvailableChain.PCSA.Run.signLabel_head_iff
#print axioms AvailableChain.PCSA.Run.head_emission_duty
#print axioms AvailableChain.PCSA.Run.head_emission_unique
#print axioms AvailableChain.PCSA.Run.ack_emission_nTarget
#print axioms AvailableChain.PCSA.Run.nTarget_support
#print axioms AvailableChain.PCSA.Run.HeadAuthentic_def
#print axioms AvailableChain.PCSA.Run.pcsa_named_preceq_refl
#print axioms AvailableChain.PCSA.Run.pcsa_named_erase_root
#print axioms AvailableChain.PCSA.Run.pcsa_rootBlock_delivered
#print axioms AvailableChain.PCSA.Run.pcsa_rootBlock_eq
#print axioms AvailableChain.PCSA.Run.evidence_stateBefore
#print axioms AvailableChain.PCSA.Run.evidence_storeAt
#print axioms AvailableChain.PCSA.StoreEvidence_def
#print axioms AvailableChain.PCSA.grid_admitVote_evidence
#print axioms AvailableChain.PCSA.grid_admitProposal_evidence
#print axioms AvailableChain.PCSA.normalizeS_evidence
#print axioms AvailableChain.PCSA.reconcile_evidence
#print axioms AvailableChain.PCSA.installPC_evidence
#print axioms AvailableChain.PCSA.collectPCs_evidence
#print axioms AvailableChain.PCSA.poolAckRaw_evidence
#print axioms AvailableChain.PCSA.admitRow_evidence
#print axioms AvailableChain.PCSA.process_evidence
#print axioms AvailableChain.PCSA.gateFrom_evidence
#print axioms AvailableChain.PCSA.clock_evidence
#print axioms AvailableChain.PCSA.Run.held_pc_head_support
#print axioms AvailableChain.PCSA.Run.held_pc_root_unique
#print axioms AvailableChain.PCSA.Run.held_pc_target_unique

end

#print axioms AvailableChain.PCSA.pcsa_firstPerSeat_seats
#print axioms AvailableChain.PCSA.pcsa_assemblePC_quorum
#print axioms AvailableChain.PCSA.pcsa_collectPCs_quorum
#print axioms AvailableChain.PCSA.pcsa_collectPCs_saturated
#print axioms AvailableChain.PCSA.pcsa_collectPCs_eq_of_saturated
#print axioms AvailableChain.PCSA.Run.pcsa_saturated_stateBefore
#print axioms AvailableChain.PCSA.Run.pcsa_collectPCs_after_freeze

#print axioms AvailableChain.PCSA.pcsa_clock_now
#print axioms AvailableChain.PCSA.pcsa_process_now

#print axioms AvailableChain.PCSA.Run.pcsa_honest_ack_admitted

#print axioms AvailableChain.PCSA.Run.pcsa_clock_read
#print axioms AvailableChain.PCSA.pcsa_process_pool_pred
#print axioms AvailableChain.PCSA.Run.pcsa_pool_honest_emits
#print axioms AvailableChain.PCSA.pcsa_clean_clock_body_scope
#print axioms AvailableChain.PCSA.Run.pcsa_clean_body_scope
#print axioms AvailableChain.PCSA.Run.pcsa_clean_scoped_root_eq
#print axioms AvailableChain.PCSA.Run.pcsa_seat_roots
#print axioms AvailableChain.PCSA.pcsa_poolAck_one_root
#print axioms AvailableChain.PCSA.Run.pcsa_handled_ack_pool
#print axioms AvailableChain.PCSA.Run.pcsa_ack_emission_nTarget
#print axioms AvailableChain.PCSA.Run.pcsa_ack_root_slotOK
#print axioms AvailableChain.PCSA.Run.pcsa_ack_receiver_slot

#print axioms AvailableChain.PCSA.Run.pcsa_formation_ack_admit
#print axioms AvailableChain.PCSA.Run.pcsa_formation_freeze_keep

#print axioms AvailableChain.PCSA.pcsa_body_not_excluded
#print axioms AvailableChain.PCSA.pcsa_body_accepted
#print axioms AvailableChain.PCSA.Run.pcsa_lookup_held_target
#print axioms AvailableChain.PCSA.Run.pcsa_collect_held_target
#print axioms AvailableChain.PCSA.Run.pcsa_honestHead_extends_root
#print axioms AvailableChain.PCSA.Run.pcsa_clean_head_above_root_bound
#print axioms AvailableChain.PCSA.Run.pcsa_honestHead_zero
#print axioms AvailableChain.PCSA.Run.pcsa_honestAck_N_source
#print axioms AvailableChain.PCSA.Run.pcsa_honestAck_body_scope

#print axioms AvailableChain.PCSA.Run.pcsa_proposal_emitted_slot
#print axioms AvailableChain.PCSA.Run.pcsa_formation_collect_of_held_body

#print axioms AvailableChain.PCSA.pcsa_tree_correspondence
#print axioms AvailableChain.PCSA.pcsa_fullTree_of_frame
#print axioms AvailableChain.PCSA.pcsa_body_clock_fg
#print axioms AvailableChain.PCSA.pcsa_body_process_fg_mono
#print axioms AvailableChain.PCSA.Run.pcsa_body_stateBefore_mono
#print axioms AvailableChain.PCSA.pcsa_body_insert_data
#print axioms AvailableChain.PCSA.pcsa_admitBlock_body_mem
#print axioms AvailableChain.PCSA.pcsa_process_new_body
#print axioms AvailableChain.PCSA.Run.pcsa_body_receipt_origin
#print axioms AvailableChain.PCSA.Run.pcsa_body_handles_direct
#print axioms AvailableChain.PCSA.Run.pcsa_body_relay_before_deadline
#print axioms AvailableChain.PCSA.Run.pcsa_ack_target_body_before_freeze
#print axioms AvailableChain.PCSA.Run.pcsa_pcDissemination

#print axioms AvailableChain.PCSA.pcsa_generated_body_rows
#print axioms AvailableChain.PCSA.Run.pcsa_emitted_body_rows
#print axioms AvailableChain.PCSA.Run.pcsa_formation_body_before_freeze
#print axioms AvailableChain.PCSA.Run.pcsa_formation_collect

#print axioms AvailableChain.PCSA.Run.pcsa_run_common_head_resolution
#print axioms AvailableChain.PCSA.pcsa_clock_heads
#print axioms AvailableChain.PCSA.pcsa_process_heads_mono
#print axioms AvailableChain.PCSA.Run.pcsa_heads_stateBefore_mono

#print axioms AvailableChain.PCSA.pcsa_clock_headStamps
#print axioms AvailableChain.PCSA.pcsa_process_headStamps_prefix
#print axioms AvailableChain.PCSA.pcsa_stampVote_eq_of_prefix
#print axioms AvailableChain.PCSA.Run.pcsa_headStamps_stateBefore_prefix

#print axioms AvailableChain.PCSA.Run.pcsa_head_stamp_keys
#print axioms AvailableChain.PCSA.Run.pcsa_head_stamp_lookup
#print axioms AvailableChain.PCSA.Run.pcsa_head_stamp_stateBefore_eq
#print axioms AvailableChain.PCSA.Run.pcsa_process_head_stamp_origin
#print axioms AvailableChain.PCSA.Run.pcsa_head_stamp_source
#print axioms AvailableChain.PCSA.Run.pcsa_head_accepted_before

#print axioms AvailableChain.PCSA.Run.pcsa_handled_head_mem_or_cap
#print axioms AvailableChain.PCSA.Run.pcsa_head_receipt_window
#print axioms AvailableChain.PCSA.Run.pcsa_handled_head_stateBefore_mem_or_cap
#print axioms AvailableChain.PCSA.Run.pcsa_head_stamp_lt_of_index_cut
#print axioms AvailableChain.PCSA.Run.pcsa_head_stamp_lt_at_clocked_read
#print axioms AvailableChain.PCSA.Run.pcsa_head_before_cut_mem_late
#print axioms AvailableChain.PCSA.Run.pcsa_cap_before_cut_mem_late
#print axioms AvailableChain.PCSA.Run.pcsa_handled_head_late_or_cap

#print axioms AvailableChain.PCSA.pcsa_blockAccepted_slot
#print axioms AvailableChain.PCSA.Run.pcsa_head_accepting_slot
#print axioms AvailableChain.PCSA.Run.pcsa_head_acceptance_after_slot_start
#print axioms AvailableChain.PCSA.Run.pcsa_head_relay_late_or_cap
#print axioms AvailableChain.PCSA.Run.pcsa_head_before_public_cut_relay_late

#print axioms AvailableChain.PCSA.pcsa_clock_blocks
#print axioms AvailableChain.PCSA.pcsa_clock_bodyStamps
#print axioms AvailableChain.PCSA.pcsa_process_bodyStamps_prefix
#print axioms AvailableChain.PCSA.pcsa_stampBlock_eq_of_prefix
#print axioms AvailableChain.PCSA.Run.pcsa_bodyStamps_stateBefore_prefix
#print axioms AvailableChain.PCSA.Run.pcsa_body_stamp_keys
#print axioms AvailableChain.PCSA.Run.pcsa_body_stamp_lookup
#print axioms AvailableChain.PCSA.Run.pcsa_body_stamp_stateBefore_eq

#print axioms AvailableChain.PCSA.Run.pcsa_process_body_stamp_origin
#print axioms AvailableChain.PCSA.Run.pcsa_body_stamp_source
#print axioms AvailableChain.PCSA.Run.pcsa_body_admitted_before
#print axioms AvailableChain.PCSA.Run.pcsa_passed_body_accepts
#print axioms AvailableChain.PCSA.Run.pcsa_body_accepted_before
#print axioms AvailableChain.PCSA.Run.pcsa_body_stamp_lt_of_index_cut
#print axioms AvailableChain.PCSA.Run.pcsa_body_before_public_cut_relay

#print axioms AvailableChain.PCSA.pcsa_clock_headDomain
#print axioms AvailableChain.PCSA.Run.pcsa_headDomain_stateBefore_none
#print axioms AvailableChain.PCSA.Run.pcsa_resolved_head_of_held_body

-- C6 proposal-pool provenance and carried input validity.
#print axioms AvailableChain.PCSA.pcsa_clock_proposals
#print axioms AvailableChain.PCSA.pcsa_process_proposal_pred
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_receipt_origin
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_pool_wellFormed
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_support_raw
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_raw_label
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_raw_handled

-- C6 concrete voter input lists.
#print axioms AvailableChain.PCSA.pcsa_proposalsAt_mem
#print axioms AvailableChain.PCSA.pcsa_headVotes_mem
#print axioms AvailableChain.PCSA.pcsa_headSupport_mem
#print axioms AvailableChain.PCSA.pcsa_headVotes_of_frozen
#print axioms AvailableChain.PCSA.pcsa_headVotes_of_carried
#print axioms AvailableChain.PCSA.pcsa_frozen_support_data
#print axioms AvailableChain.PCSA.pcsa_headSupport_subset_headVotes
#print axioms AvailableChain.PCSA.Run.pcsa_headSupport_subset_at_read

-- C6 concrete backward receipt and cap transport.
#print axioms AvailableChain.PCSA.Run.pcsa_count_head_shape
#print axioms AvailableChain.PCSA.Run.pcsa_cap_before_public_cut_relay_late
#print axioms AvailableChain.PCSA.Run.pcsa_proposer_input_relay_late
#print axioms AvailableChain.PCSA.Run.pcsa_frozen_input_relay_late
#print axioms AvailableChain.PCSA.Run.pcsa_handled_input_relay_late
#print axioms AvailableChain.PCSA.Run.pcsa_proposer_tick_input_relay_late

-- C6 BackwardInputs.
#print axioms AvailableChain.PCSA.Run.pcsa_voter_tick_input_relay_late

-- C6 ForwardReceipt.
#print axioms AvailableChain.PCSA.Run.pcsa_genesis_body_stamp
#print axioms AvailableChain.PCSA.Run.pcsa_early_head_relay_frozen
#print axioms AvailableChain.PCSA.Run.pcsa_early_body_relay_frozen
#print axioms AvailableChain.PCSA.Run.pcsa_early_input_relay_support

-- C6 CountTransport.
#print axioms AvailableChain.PCSA.pcsa_clean_input_not_capped
#print axioms AvailableChain.PCSA.pcsa_clean_input_unique_late
#print axioms AvailableChain.PCSA.Run.pcsa_read_vote_support_body
#print axioms AvailableChain.PCSA.Run.pcsa_gate_voter_walk_counts
#print axioms AvailableChain.PCSA.Run.pcsa_gate_proposer_walk_counts

-- C6 GateCounts.
#print axioms AvailableChain.PCSA.Run.pcsa_early_input_gate_relay
#print axioms AvailableChain.PCSA.Run.pcsa_same_label_gate_results

-- C6 GateReads.
#print axioms AvailableChain.PCSA.pcsa_clock_confirmation_eq_pre
#print axioms AvailableChain.PCSA.Run.pcsa_gateResultAt_source
#print axioms AvailableChain.PCSA.Run.pcsa_clean_same_label_results

-- C6 BodyPaths.
#print axioms AvailableChain.PCSA.pcsa_body_prefix_mem
#print axioms AvailableChain.PCSA.pcsa_frame_subset_of_frame
#print axioms AvailableChain.PCSA.Run.pcsa_full_read_prefix_mem
#print axioms AvailableChain.PCSA.Run.pcsa_frozen_read_prefix_mem

-- C6 ResultPaths.
#print axioms AvailableChain.PCSA.Run.pcsa_result_early_support
#print axioms AvailableChain.PCSA.Run.pcsa_result_prefixes_retained

-- C6 VoteTransport.
#print axioms AvailableChain.PCSA.Run.pcsa_postClock_source
#print axioms AvailableChain.PCSA.Run.pcsa_next_head_above_result_of_root
#print axioms AvailableChain.PCSA.Run.pcsa_clean_next_head_above

-- C6 HeadEvidence.
#print axioms AvailableChain.PCSA.Run.pcsa_head_single_duty
#print axioms AvailableChain.PCSA.Run.pcsa_pool_head_handled
#print axioms AvailableChain.PCSA.Run.pcsa_pool_head_emission
#print axioms AvailableChain.PCSA.Run.pcsa_honest_pool_head_eq_emitted
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_pool_not_capped
#print axioms AvailableChain.PCSA.Run.pcsa_head_emission_time_awake
#print axioms AvailableChain.PCSA.Run.pcsa_handles_carried

-- C6 HeadBody.
#print axioms AvailableChain.PCSA.pcsa_liveRoot_body_mem
#print axioms AvailableChain.PCSA.pcsa_headVote_body_mem
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_body_before_vote
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_body_before_early
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_slot_le

-- C6 HonestReceipt.
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_emits
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_not_excluded_early
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_before_early

-- C6 HonestSupport.
#print axioms AvailableChain.PCSA.pcsa_early_uncapped_clean
#print axioms AvailableChain.PCSA.Run.pcsa_honest_late_not_capped
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_clean_support

-- C6 HonestBatch.
#print axioms AvailableChain.PCSA.Run.pcsa_honest_head_exists
#print axioms AvailableChain.PCSA.Run.pcsa_clean_head_batch
#print axioms AvailableChain.PCSA.Run.pcsa_late_participant_bound
#print axioms AvailableChain.PCSA.Run.pcsa_clean_gate_majority

-- C6 GateBatch.
#print axioms AvailableChain.PCSA.Run.pcsa_gateResultAt_at_tick
#print axioms AvailableChain.PCSA.Run.pcsa_clean_gate_covers_heads
#print axioms AvailableChain.PCSA.Run.pcsa_clean_result_exists
#print axioms AvailableChain.PCSA.Run.pcsa_clean_result_covers_heads
#print axioms AvailableChain.PCSA.Run.pcsa_clean_headsAbove_step
#print axioms AvailableChain.PCSA.Run.pcsa_clean_resultsChain_step

-- C6 ZeroResult.
#print axioms AvailableChain.PCSA.pcsa_body_positive_slot
#print axioms AvailableChain.PCSA.Run.pcsa_zero_result_eq_genesis
#print axioms AvailableChain.PCSA.Run.pcsa_clean_zero_result

-- C6 PCPool.
#print axioms AvailableChain.PCSA.CleanPCPool.pcsa_firstPerSeat_subset
#print axioms AvailableChain.PCSA.CleanPCPool.CertSafe
#print axioms AvailableChain.PCSA.CleanPCPool.CertSafe_def
#print axioms AvailableChain.PCSA.CleanPCPool.process_certSafe
#print axioms AvailableChain.PCSA.CleanPCPool.clock_certSafe

-- C6 PCScope.
#print axioms AvailableChain.PCSA.pcsa_clock_pcs
#print axioms AvailableChain.PCSA.pcsa_collect_pc_target_origin
#print axioms AvailableChain.PCSA.pcsa_process_pc_target_origin
#print axioms AvailableChain.PCSA.pcsa_pc_targets_held
#print axioms AvailableChain.PCSA.Run.pcsa_clean_pc_scope

-- C6 AckOrigins.
#print axioms AvailableChain.PCSA.Run.pcsa_pc_honest_emission_before
#print axioms AvailableChain.PCSA.Run.pcsa_pc_early_before

-- C6 AckDecisions.
#print axioms AvailableChain.PCSA.Run.pcsa_postClock_at_tick
#print axioms AvailableChain.PCSA.Run.pcsa_honest_ack_of_emission
#print axioms AvailableChain.PCSA.Run.pcsa_pc_honest_ack_before
#print axioms AvailableChain.PCSA.Run.pcsa_pc_slot_before_vote
#print axioms AvailableChain.PCSA.Run.pcsa_pcs_before_first_gate_empty
#print axioms AvailableChain.PCSA.Run.pcsa_readAt_index_before_cut
#print axioms AvailableChain.PCSA.Run.pcsa_pc_honest_ack_storeAt

-- C6 StoreOrigins.
#print axioms AvailableChain.PCSA.pcsa_process_record_origin
#print axioms AvailableChain.PCSA.pcsa_process_record_of_genesis
#print axioms AvailableChain.PCSA.pcsa_clock_record_before_first_gate

-- C6 LockOrigins.
#print axioms AvailableChain.PCSA.pcsa_admit_vote_locks
#print axioms AvailableChain.PCSA.pcsa_admit_proposal_locks
#print axioms AvailableChain.PCSA.pcsa_admit_row_locks
#print axioms AvailableChain.PCSA.pcsa_pool_raw_ack_locks
#print axioms AvailableChain.PCSA.pcsa_pool_ack_locks
#print axioms AvailableChain.PCSA.pcsa_admit_rows_locks
#print axioms AvailableChain.PCSA.pcsa_pool_raw_acks_locks
#print axioms AvailableChain.PCSA.pcsa_normalize_locks
#print axioms AvailableChain.PCSA.pcsa_process_locks_subset
#print axioms AvailableChain.PCSA.pcsa_clockPre_locks_subset
#print axioms AvailableChain.PCSA.pcsa_clock_locks_before_first_gate

-- C6 ZeroStores.
#print axioms AvailableChain.PCSA.Run.pcsa_zero_store_before_gate
#print axioms AvailableChain.PCSA.Run.pcsa_zero_storeAt_before_gate

-- C6 SnapshotContents.
#print axioms AvailableChain.PCSA.Run.pcsa_snapshot_row_origin
#print axioms AvailableChain.PCSA.Run.pcsa_snapshot_pc_origin
#print axioms AvailableChain.PCSA.Run.pcsa_snapshots_before_first_gate_empty

-- C6 CarriedPCs.
#print axioms AvailableChain.PCSA.Run.pcsa_carried_pc_early_le
#print axioms AvailableChain.PCSA.Run.pcsa_carriedPC_origin
#print axioms AvailableChain.PCSA.Run.pcsa_carriedPC_honest_ack_before
#print axioms AvailableChain.PCSA.Run.pcsa_carriedPC_early_before
#print axioms AvailableChain.PCSA.Run.pcsa_carriedPCs_before_first_gate_empty

-- C6 ZeroViews.
#print axioms AvailableChain.PCSA.Run.pcsa_no_honest_proposal_zero
#print axioms AvailableChain.PCSA.Run.pcsa_gateInAt_source
#print axioms AvailableChain.PCSA.Run.pcsa_zero_gate_pcs
#print axioms AvailableChain.PCSA.Run.pcsa_zero_next_root
#print axioms AvailableChain.PCSA.Run.pcsa_clean_invariant_zero

-- C6 RecordEvents.
#print axioms AvailableChain.PCSA.pcsa_clock_record_origin
#print axioms AvailableChain.PCSA.Run.pcsa_record_stateBefore_origin

-- C6 LockEvents.
#print axioms AvailableChain.PCSA.pcsa_gate_lock_origin
#print axioms AvailableChain.PCSA.pcsa_clock_lock_origin
#print axioms AvailableChain.PCSA.Run.pcsa_lock_stateBefore_origin

-- C6 RecordBounds.
#print axioms AvailableChain.PCSA.pcsa_gate_label_before_vote
#print axioms AvailableChain.PCSA.Run.pcsa_record_storeAt_origin
#print axioms AvailableChain.PCSA.Run.pcsa_lock_storeAt_origin
#print axioms AvailableChain.PCSA.Run.pcsa_record_storeAt_compatible

-- C6 RecordOrder.
#print axioms AvailableChain.PCSA.Run.pcsa_record_step_mono_at_limit
#print axioms AvailableChain.PCSA.Run.pcsa_record_step_mono
#print axioms AvailableChain.PCSA.Run.pcsa_record_indices_mono
#print axioms AvailableChain.PCSA.Run.pcsa_record_storeAt_mono
#print axioms AvailableChain.PCSA.Run.pcsa_record_indices_mono_at_limit

-- C6 ProposerInputs.
#print axioms AvailableChain.PCSA.pcsa_liftHead_baseVote
#print axioms AvailableChain.PCSA.pcsa_generated_proposal_inputs
#print axioms AvailableChain.PCSA.Run.pcsa_prop_single_duty
#print axioms AvailableChain.PCSA.Run.pcsa_emitted_proposal_inputs

-- C6 CommonInputs.
#print axioms AvailableChain.PCSA.Run.pcsa_proposer_late_eq
#print axioms AvailableChain.PCSA.Run.pcsa_frozen_input_in_proposer

-- Frozen pending-label declarations from pcsa-w3-outage.
#print axioms AvailableChain.PCSA.Run.CleanResultsNonemptyClaim_def
#print axioms AvailableChain.PCSA.Run.CleanResultsChainPendingClaim_def
#print axioms AvailableChain.PCSA.Run.CleanHeadsAbovePendingClaim_def
#print axioms AvailableChain.PCSA.Run.CleanDisseminationPendingClaim_def
#print axioms AvailableChain.PCSA.Run.CleanHeadsPastCutClaim_def
#print axioms AvailableChain.PCSA.Run.CleanBlockReceiptClaim_def

-- C6 ProposalEvidence.
#print axioms AvailableChain.PCSA.Run.pcsa_decoded_proposal_object
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_pool_eq_emitted
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_decoded_eq_emitted

-- C6 ProposalStore.
#print axioms AvailableChain.PCSA.pcsa_admitBlock_proposals
#print axioms AvailableChain.PCSA.pcsa_process_proposals_mono
#print axioms AvailableChain.PCSA.Run.pcsa_proposals_stateBefore_mono

-- C6 ProposalDelivery.
#print axioms AvailableChain.PCSA.Run.pcsa_honest_proposal_before_vote

-- C6 CommonRaw.
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_pool_slot
#print axioms AvailableChain.PCSA.Run.pcsa_honest_headVotes_source
#print axioms AvailableChain.PCSA.Run.pcsa_emitted_raw_in_headVotes
#print axioms AvailableChain.PCSA.Run.pcsa_common_raw_transfer

-- C6 CommonBodies.
#print axioms AvailableChain.PCSA.Run.pcsa_proposer_body_before_vote
#print axioms AvailableChain.PCSA.Run.pcsa_frozen_body_in_proposer

-- C6 CommonSupport.
#print axioms AvailableChain.PCSA.pcsa_active_base_resolution
#print axioms AvailableChain.PCSA.pcsa_headSupport_of_carried
#print axioms AvailableChain.PCSA.Run.pcsa_proposer_support_in_voter
#print axioms AvailableChain.PCSA.Run.pcsa_honest_headSupport_source
#print axioms AvailableChain.PCSA.Run.pcsa_frozen_support_in_proposer
#print axioms AvailableChain.PCSA.Run.pcsa_honest_support_backward
#print axioms AvailableChain.PCSA.pcsa_headSupport_resolution

-- C6 CommonScores.
#print axioms AvailableChain.PCSA.Run.pcsa_read_vote_support_iff
#print axioms AvailableChain.PCSA.Run.pcsa_common_walk_counts

-- C6 CommonTree.
#print axioms AvailableChain.PCSA.Run.pcsa_honest_slot_body_unique
#print axioms AvailableChain.PCSA.Run.pcsa_voter_tree_source
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_prefix_voter_mem

-- C6 NCounts.
#print axioms AvailableChain.PCSA.Run.pcsa_N_same_label_result
#print axioms AvailableChain.PCSA.Run.pcsa_honestAck_same_label_result

-- C6 NWalkCounts.
#print axioms AvailableChain.PCSA.pcsa_N_score_dominance
#print axioms AvailableChain.PCSA.Run.pcsa_proposer_honest_not_capped
#print axioms AvailableChain.PCSA.Run.pcsa_voter_honest_not_capped

-- C6 NReadTransport.
#print axioms AvailableChain.PCSA.pcsa_N_head_witness
#print axioms AvailableChain.PCSA.Run.pcsa_N_read_transport

-- C6 NNextHead.
#print axioms AvailableChain.PCSA.Run.pcsa_N_next_head_of_root
#print axioms AvailableChain.PCSA.Run.pcsa_honestAck_next_head_of_root

-- C6 NHeads.
#print axioms AvailableChain.PCSA.Run.pcsa_honest_pool_head_source
#print axioms AvailableChain.PCSA.Run.pcsa_early_honest_head_source
#print axioms AvailableChain.PCSA.Run.pcsa_N_has_honest_head
#print axioms AvailableChain.PCSA.Run.pcsa_N_targets_unique

-- C6 ViewOrigins.
#print axioms AvailableChain.PCSA.pcsa_vote_ne_freeze
#print axioms AvailableChain.PCSA.pcsa_vote_snapshot
#print axioms AvailableChain.PCSA.pcsa_clock_carriedPCs
#print axioms AvailableChain.PCSA.Run.pcsa_voterPC_honest_ack_before

-- C6 RootSources.
#print axioms AvailableChain.PCSA.pcsa_vote_ne_gate
#print axioms AvailableChain.PCSA.pcsa_vote_locks_subset
#print axioms AvailableChain.PCSA.pcsa_gate_label_lt_next_vote
#print axioms AvailableChain.PCSA.Run.pcsa_next_root_source

-- C6 NRoot.
#print axioms AvailableChain.PCSA.Run.pcsa_ack_has_honest_head
#print axioms AvailableChain.PCSA.Run.pcsa_ack_targets_unique
#print axioms AvailableChain.PCSA.Run.pcsa_ack_next_root_below

-- C6 PCChain.
#print axioms AvailableChain.PCSA.pcsa_early_label_before_vote
#print axioms AvailableChain.PCSA.Run.pcsa_pc_storeAt_ack_slot
#print axioms AvailableChain.PCSA.Run.pcsa_pc_storeAt_chain
#print axioms AvailableChain.PCSA.Run.pcsa_pc_storeAt_result

-- C6 NDissemination.
#print axioms AvailableChain.PCSA.Run.pcsa_ack_dissemination_step

-- C6 ReleaseCount.
#print axioms AvailableChain.PCSA.Run.pcsa_release_count_fault_bound

-- C6 LockRetention.
#print axioms AvailableChain.PCSA.pcsa_collect_keep_lock
#print axioms AvailableChain.PCSA.pcsa_write_lock_keep_target

-- C6 ViewRank.
#print axioms AvailableChain.PCSA.pcsa_bestPC_slot_ge
#print axioms AvailableChain.PCSA.pcsa_bestPC_target_of_max_slot
#print axioms AvailableChain.PCSA.pcsa_bestPC_isSome_of_mem

-- C6 RelayFrames.
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_compatible_genesis
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_activeCompatible_genesis
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_normalizeS_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_reconcile_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_reconcile_genesis
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_admitRow_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_fold_admitRow_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_poolAckRaw_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_fold_poolAckRaw_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_collectPCs_proposals
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_gateFrom_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_clockPre_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_clock_frame
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_admitVote_blocks
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_foldVotes_blocks
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_admitProposal_blocks
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_poolAck_frame

-- C6 RelayCollect.
#print axioms AvailableChain.PCSA.CleanPCRelay.KeyHeld
#print axioms AvailableChain.PCSA.CleanPCRelay.KeyHeld_def
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_keyHeld_iff_any
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_keyHeld_mono
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_pc_wellFormed_parts
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_assemblePC_congr
#print axioms AvailableChain.PCSA.CleanPCRelay.CollectClosed
#print axioms AvailableChain.PCSA.CleanPCRelay.CollectClosed_def
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_mem_collectPCs
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_assemblePC_of_parts
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_acksOn_append
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_new_key_ack
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_firstPerSeat_append
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_new_key_single
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_saturated_collectClosed
#print axioms AvailableChain.PCSA.Run.pcsa_clean_collectClosed

-- C6 RelayStore.
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_poolAck_pool
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_fold_poolAckRaw_extra
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_collect_new_key
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_ack_new_key
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_admitBlock_new_key
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_tail_pool
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_ite_reconcile_pool
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_process_pool_mono
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_admitPC_pool

-- C6 RelayCarrier.
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_relay_decoded_ack
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_relay_decoded_pc
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_relay_decoded_proposal
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_handles_pc_store
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_install_carries

-- C6 RelayPersistence.
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_admitBlock_tail_genesis
#print axioms AvailableChain.PCSA.CleanPCRelay.pcsa_process_stageOne
#print axioms AvailableChain.PCSA.Run.pcsa_clean_pc_indices_mono

-- C6 RelayOrigin.
#print axioms AvailableChain.PCSA.Run.pcsa_clean_processed_pc
#print axioms AvailableChain.PCSA.Run.pcsa_clean_tick_step
#print axioms AvailableChain.PCSA.Run.pcsa_clean_deliver_succ
#print axioms AvailableChain.PCSA.Run.pcsa_clean_keyHeld_accepted

-- C6 RelayReceipt.
#print axioms AvailableChain.PCSA.Run.pcsa_clean_pc_from_pool
#print axioms AvailableChain.PCSA.Run.pcsa_pc_before_public_cut_relay

-- C6 FrozenPCTransport.
#print axioms AvailableChain.PCSA.Run.pcsa_clock_target_active
#print axioms AvailableChain.PCSA.Run.pcsa_frozen_pc_in_proposer

-- C6 CarriedView.
#print axioms AvailableChain.PCSA.pcsa_carriedPC_of_proposal
#print axioms AvailableChain.PCSA.Run.pcsa_carriedPC_eq_emitted

-- C6 CommonViews.
#print axioms AvailableChain.PCSA.Run.pcsa_common_view_targets

-- C6 BodySlotBounds.
#print axioms AvailableChain.PCSA.pcsa_admission_slot_bounds
#print axioms AvailableChain.PCSA.Run.pcsa_body_parent_slot_lt
#print axioms AvailableChain.PCSA.Run.pcsa_body_slot_before_next_proposal

-- C6 ProposalPaths.
#print axioms AvailableChain.PCSA.Run.pcsa_getHead_body_at_read
#print axioms AvailableChain.PCSA.Run.pcsa_proposal_proper_prefix_source

-- C6 CommonEligibility.
#print axioms AvailableChain.PCSA.pcsa_eligible_zero_floor
#print axioms AvailableChain.PCSA.pcsa_eligible_equal_counts
#print axioms AvailableChain.PCSA.pcsa_eligible_current_slot
#print axioms AvailableChain.PCSA.pcsa_proposal_clock_slot
#print axioms AvailableChain.PCSA.pcsa_vote_clock_slot

-- C6 RetainedProposal.
#print axioms AvailableChain.PCSA.pcsa_retained_proposal_walk

-- C6 ProposerReads.
#print axioms AvailableChain.PCSA.pcsa_proposal_ne_gate
#print axioms AvailableChain.PCSA.pcsa_proposal_locks_subset
#print axioms AvailableChain.PCSA.Run.pcsa_strict_read_eq_previous
#print axioms AvailableChain.PCSA.Run.pcsa_pre_tick_storeAt
#print axioms AvailableChain.PCSA.Run.pcsa_clean_proposer_root_compatible
#print axioms AvailableChain.PCSA.Run.pcsa_clean_proposer_head_above_result

-- C6 RootAgreement.
#print axioms AvailableChain.PCSA.pcsa_selected_walk_bases_eq
#print axioms AvailableChain.PCSA.pcsa_proposal_root_geometry
#print axioms AvailableChain.PCSA.Run.pcsa_clean_pre_vote_lock_below_result

-- C6 HonestProposal.
#print axioms AvailableChain.PCSA.Run.pcsa_honest_proposal_named
#print axioms AvailableChain.PCSA.pcsa_named_parent_prefix
#print axioms AvailableChain.PCSA.pcsa_named_parent_of_positive
#print axioms AvailableChain.PCSA.Run.pcsa_clean_emitted_heads_equal
#print axioms AvailableChain.PCSA.Run.pcsa_clean_headsEqual_step

-- C6 AckResults.
#print axioms AvailableChain.PCSA.Run.pcsa_ack_result_compatible
