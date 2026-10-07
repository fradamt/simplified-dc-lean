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
