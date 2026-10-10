module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentTiming
public import AvailableChainFGSAProofs.Proofs.Healing.Frame
public import AvailableChainFGSAProofs.Proofs.Healing.FramePaths
public import AvailableChainFGSAProofs.Proofs.Healing.FrameRelay
public import AvailableChainFGSAProofs.Proofs.Healing.FrameSource
public import AvailableChainFGSAProofs.Proofs.Healing.FrameZero
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchAge
public import AvailableChainFGSAProofs.Proofs.Healing.LiveDC
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows
public import AvailableChainFGSAProofs.Proofs.Healing.SupportFrame
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRelay
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRelease
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSaved
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTicks
public import AvailableChainFGSAProofs.Proofs.Healing.SupportWrite
public import AvailableChainFGSAProofs.Proofs.Healing.Time

public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle

public import AvailableChainFGSAProofs.Proofs.Healing.PromotionPhase

public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportFrame

public import AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle

public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAdvance
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot

public import AvailableChainFGSAProofs.Proofs.Healing.SupportGate

public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAge
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionTerminal

set_option linter.privateModule false

#print axioms AvailableChain.FGSA.Run.healing_row_delivery
#print axioms AvailableChain.FGSA.Run.healing_receipt_before_tick
#print axioms AvailableChain.FGSA.Run.healing_action_period
#print axioms AvailableChain.FGSA.Run.healing_delivery_clock
#print axioms AvailableChain.FGSA.Run.healing_justification_timed
#print axioms AvailableChain.FGSA.Run.healing_finality_source_clock
#print axioms AvailableChain.FGSA.Run.healing_justified_source_clock
#print axioms AvailableChain.FGSA.Run.healing_proposal_full_witness
#print axioms AvailableChain.FGSA.Run.healing_full_witness
#print axioms AvailableChain.FGSA.Run.healing_proposer_floor
#print axioms AvailableChain.FGSA.Run.healing_tGeom
#print axioms AvailableChain.FGSA.Run.healing_retained_path
#print axioms AvailableChain.FGSA.Run.healing_carried_path
#print axioms AvailableChain.FGSA.Run.healing_frozen_path
#print axioms AvailableChain.FGSA.Run.healing_witness_relay
#print axioms AvailableChain.FGSA.Run.healing_witness_relay_phase
#print axioms AvailableChain.FGSA.Run.healing_source_slot
#print axioms AvailableChain.FGSA.Run.healing_full_witness_all
#print axioms AvailableChain.FGSA.Run.frontierSearch_age_service
#print axioms AvailableChain.FGSA.Run.healing_liveDCFromWindows
#print axioms AvailableChain.FGSA.Run.healing_phase_idx_le_time
#print axioms AvailableChain.FGSA.Run.healing_phase_block_receipt
#print axioms AvailableChain.FGSA.Run.healing_evidence_spread
#print axioms AvailableChain.FGSA.Run.healing_phase_rows_spread
#print axioms AvailableChain.FGSA.Run.healing_phase_idxBefore_mono
#print axioms AvailableChain.FGSA.Run.healing_phase_lt_timeIdx
#print axioms AvailableChain.FGSA.Run.healing_frontier_mono
#print axioms AvailableChain.FGSA.Run.healing_phase_held_receipt
#print axioms AvailableChain.FGSA.Run.PostResetConeAt_def
#print axioms AvailableChain.FGSA.Run.postResetRetainedCone_iff_at
#print axioms AvailableChain.FGSA.Run.postResetRetainedCone_iff
#print axioms AvailableChain.FGSA.Run.postReset_source_label_le_sub_two
#print axioms AvailableChain.FGSA.Run.postReset_release_before_proposal
#print axioms AvailableChain.FGSA.Run.postReset_proposal_horizon
#print axioms AvailableChain.FGSA.Run.postReset_head_horizon
#print axioms AvailableChain.FGSA.Run.postReset_synchronous_window
#print axioms AvailableChain.FGSA.Run.postResetRetainedCone_of_horizon_lt
#print axioms AvailableChain.FGSA.Run.healing_postReset_retainedReads_at
#print axioms AvailableChain.FGSA.Run.healing_postReset_retainedReads
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap_remainder
#print axioms AvailableChain.FGSA.Run.healing_promotion_held_mono
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_deadline
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_deadline_strict
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_receipt_strict
#print axioms AvailableChain.FGSA.Run.healing_promotion_maturity
#print axioms AvailableChain.FGSA.Run.healing_promotion_maturity_of_action
#print axioms AvailableChain.FGSA.Run.healing_promotion_age_gap
#print axioms AvailableChain.FGSA.Run.healing_promotion_proposal_read
#print axioms AvailableChain.FGSA.Run.healing_promotion_carrier
#print axioms AvailableChain.FGSA.Run.healing_promotion_slot_proposal
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap_proposal
#print axioms AvailableChain.FGSA.Run.healing_promotion_same_rows
#print axioms AvailableChain.FGSA.Run.healing_settled_frame_strict
#print axioms AvailableChain.FGSA.Run.healing_support_idxBefore_le
#print axioms AvailableChain.FGSA.Run.healing_witness_relay_settled
#print axioms AvailableChain.FGSA.Run.healing_head_witness_relay
#print axioms AvailableChain.FGSA.Run.healing_support_gate_late
#print axioms AvailableChain.FGSA.Run.healing_support_vote_backward
#print axioms AvailableChain.FGSA.Run.healing_support_prefreeze_path
#print axioms AvailableChain.FGSA.Run.healing_support_target_path
#print axioms AvailableChain.FGSA.Run.healing_support_release_rows
#print axioms AvailableChain.FGSA.Run.healing_saved_origin
#print axioms AvailableChain.FGSA.Run.healing_clockPre_live
#print axioms AvailableChain.FGSA.Run.healing_support_vote_tick
#print axioms AvailableChain.FGSA.Run.healing_support_honest_emits
#print axioms AvailableChain.FGSA.Run.healing_support_key_cases
#print axioms AvailableChain.FGSA.Run.healing_support_gate_reads
#print axioms AvailableChain.FGSA.Run.healing_support_fastWrite
#print axioms AvailableChain.FGSA.Run.healing_support_phaseBody_of_write
#print axioms AvailableChain.FGSA.Run.healing_last_write_support
#print axioms AvailableChain.FGSA.Run.healing_support_deadline_le_vote
#print axioms AvailableChain.FGSA.Run.healing_support_vote_before_proposal
#print axioms AvailableChain.FGSA.Run.healing_last_write_two_lease
#print axioms AvailableChain.FGSA.Run.healing_last_write_one_lease
#print axioms AvailableChain.FGSA.Run.HealingInputOfH0Statement_def
#print axioms AvailableChain.FGSA.Run.healing_resetF_budget_eq
#print axioms AvailableChain.FGSA.Run.healing_resetFull_horizon
#print axioms AvailableChain.FGSA.Run.healing_time_strict_of_reset
#print axioms AvailableChain.FGSA.Run.healing_hTime_of

#print axioms AvailableChain.FGSA.Run.healing_phase_top_persist_all
#print axioms AvailableChain.FGSA.Run.healing_phase_contest_persist_of_crossing_all
#print axioms AvailableChain.FGSA.Run.healing_phase_order_of_crossing_all
#print axioms AvailableChain.FGSA.Run.healing_frontier_mono_all
#print axioms AvailableChain.FGSA.Run.healing_phase_window_all
#print axioms AvailableChain.FGSA.Run.healing_settle_start_on
#print axioms AvailableChain.FGSA.Run.healing_promotion_quiet_window
#print axioms AvailableChain.FGSA.Run.healing_phase_extend_of_no_effective
#print axioms AvailableChain.FGSA.Run.healing_recovery_restart_bound
#print axioms AvailableChain.FGSA.Run.healing_recovery_epoch
#print axioms AvailableChain.FGSA.Run.healing_recovery_durable
#print axioms AvailableChain.FGSA.Run.healing_recovery_stamps
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined
#print axioms AvailableChain.FGSA.Run.healing_recovery_receiverService
#print axioms AvailableChain.FGSA.Run.repair_head_exact
#print axioms AvailableChain.FGSA.Run.frontier_relay
#print axioms AvailableChain.FGSA.Run.frontier_head_relay

#print axioms AvailableChain.FGSA.Run.healing_recovery_frame_metadata

#print axioms AvailableChain.FGSA.Run.healing_recovery_readyTrigger

#print axioms AvailableChain.FGSA.Run.healing_settle_start
#print axioms AvailableChain.FGSA.Run.healing_settle_event
#print axioms AvailableChain.FGSA.Run.healing_rPhase
#print axioms AvailableChain.FGSA.Run.healing_attempt_settle_start
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_other_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_other_settle

#print axioms AvailableChain.FGSA.Run.frontier_F_below_all
#print axioms AvailableChain.FGSA.Run.frontier_F_below
#print axioms AvailableChain.FGSA.Run.healing_promotion_first_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_first_receipt_of_frontierCap
#print axioms AvailableChain.FGSA.Run.healing_promotion_block_held_mono
#print axioms AvailableChain.FGSA.Run.promotion_age_advance_of_source
#print axioms AvailableChain.FGSA.Run.healing_promotion_advance
#print axioms AvailableChain.FGSA.Run.boot_not_effective_one

#print axioms AvailableChain.FGSA.Run.healing_recovery_joinedHonest
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined_counts
#print axioms AvailableChain.FGSA.Run.repair_exact_service_on
#print axioms AvailableChain.FGSA.Run.healing_postReset_retainedReads_at_on

#print axioms AvailableChain.FGSA.Run.healing_recovery_gate_scope
#print axioms AvailableChain.FGSA.Run.healing_head_witness_relay_on
#print axioms AvailableChain.FGSA.Run.healing_support_prefreeze_path_on
#print axioms AvailableChain.FGSA.Run.healing_support_gate_cover
#print axioms AvailableChain.FGSA.Run.healing_support_emitted_head

#print axioms AvailableChain.FGSA.Run.healing_phase_top_persist
#print axioms AvailableChain.FGSA.Run.healing_phase_contest_persist_of_crossing
#print axioms AvailableChain.FGSA.Run.healing_phase_order_of_crossing

#print axioms AvailableChain.FGSA.Run.healing_promotion_age_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_age_service
#print axioms AvailableChain.FGSA.Run.healing_renewedPromotion
#print axioms AvailableChain.FGSA.Run.healing_renewedPromotion_terminal
