#!/usr/bin/env bash
# P3 F0.0b: Claims, Proofs and Inhabit guard. The compiled auditors below
# adapt the CURRENT T7.1 auditors, including their generated-owner rules.
# No baseline is written. Fixtures and audit logs stay under .lake.
# SOURCE_ONLY=1 runs source findings and facade/F4 coverage, without controls or Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PY'
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
sys.path.insert(0, 'scripts')
import check_common as C
spec = importlib.util.spec_from_file_location('layers', 'scripts/check-layers.py')
L = importlib.util.module_from_spec(spec)
sys.modules['layers'] = L
spec.loader.exec_module(L)
ROOT = Path.cwd()
SOURCE_ONLY = os.environ.get('SOURCE_ONLY', '0') == '1'
LIBS = ('AvailableChainFGSAClaims', 'AvailableChainFGSAProofs', 'AvailableChainFGSAInhabit')
CLAIMS, PROOFS, INHABIT = LIBS
# Required declarations: later tasks add their principal outputs here.
EXPECTED = (
    # S5 H-ATTEMPT: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_progressAttempt_of',
    'AvailableChain.FGSA.Run.healing_attempt_raise_contest_budget',
    'AvailableChain.FGSA.Run.healing_attempt_raise_other_budget',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_budget',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_other_budget',
    'AvailableChain.FGSA.Run.healing_attempt_raise_contest_cost',
    'AvailableChain.FGSA.Run.healing_attempt_raise_other_cost',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_cost',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_other_cost',
    'AvailableChain.FGSA.Run.healing_attempt_high_source_cost',
    'AvailableChain.FGSA.Run.healing_attempt_terminal_horizon_gap',
    'AvailableChain.FGSA.Run.healing_attempt_ends_of_event',
    'AvailableChain.FGSA.Run.healing_attempt_ends_of_row',
    'AvailableChain.FGSA.Run.healing_attempt_ends_mono',
    'AvailableChain.FGSA.Run.healing_attempt_no_event',
    'AvailableChain.FGSA.Run.healing_attempt_inclusive_start',

    # S5 HG.1: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.frontier_service',
    'AvailableChain.FGSA.Run.frontierSeedQualification_iff',
    'AvailableChain.FGSA.Run.frontier_proposals_cover',
    'AvailableChain.FGSA.Run.frontier_output_cover',
    'AvailableChain.FGSA.Run.frontier_gate_guard_of_receipts',
    'AvailableChain.FGSA.Run.frontier_gate_geometry',
    'AvailableChain.FGSA.Run.frontier_gate_guard_of_cover',
    'AvailableChain.FGSA.Run.frontier_opening_gateService_of_cover',
    'AvailableChain.FGSA.Run.frontier_exactService_of_heads',
    'AvailableChain.FGSA.Run.frontier_seed_qSucc_exactService',
    'AvailableChain.FGSA.Run.frontier_later_head',
    'AvailableChain.FGSA.Run.frontier_later_exactService',
    'AvailableChain.FGSA.Run.frontier_service_core',
    'AvailableChain.FGSA.Run.frontier_seed_qSucc_input',
    'AvailableChain.FGSA.Run.frontier_seed_qSucc_head',
    'AvailableChain.FGSA.Run.tfSeed_two_from_tRepair',
    'AvailableChain.FGSA.Run.tfSeed_one_from_tRepair',
    'AvailableChain.FGSA.Run.tfSeed_later',
    'AvailableChain.FGSA.Run.tfSeed_qSucc_lease_cover',
    # H-EXPORT-2: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.fgsa_renewedPromotionClaim',
    'AvailableChain.FGSA.Run.fgsa_rowPermissionClaim',
    # H-EXPORT-1: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_renewedPromotionClaim_of',
    'AvailableChain.FGSA.Run.healing_rowPermissionClaim_of',
    # F-ABOVE-B: --expect DATA only.
    'AvailableChain.FGSA.Run.above_frontier_FE_W_of',
    'AvailableChain.FGSA.Run.above_frontier_F4_W_of',
    'AvailableChain.FGSA.Run.fgsa_aboveFrontierRecFE_W_of',
    'AvailableChain.FGSA.Run.fgsa_aboveFrontierRecF4_W_of',
    'AvailableChain.FGSA.Run.fgsa_aboveFrontierRecFE_W',
    'AvailableChain.FGSA.Run.fgsa_aboveFrontierRecF4_W',
    # O-EXPORT-3: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.outage_outageCompatClaim_of',
    'AvailableChain.FGSA.Run.outage_fastP1Claim_of',
    'AvailableChain.FGSA.Run.outage_slowP1Claim_of',
    'AvailableChain.FGSA.Run.outage_compat_body_of_cut',
    'AvailableChain.FGSA.Run.fgsa_outageCompatClaim_of_clean',
    'AvailableChain.FGSA.Run.fgsa_fastP1Claim_of_clean',
    'AvailableChain.FGSA.Run.fgsa_slowP1Claim_of_clean',
    # S5 M5b: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_rise_one_of_receipt',
    'AvailableChain.FGSA.Run.healing_rise_one_advance',
    'AvailableChain.FGSA.Run.healing_rise_one_of_effective',
    'AvailableChain.FGSA.Run.healing_rise_one_receipt_all',
    'AvailableChain.FGSA.Run.healing_rise_one_accept',
    'AvailableChain.FGSA.Run.healing_rise_one_rise',
    # S5 M5: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_rise_one_rows_received',
    'AvailableChain.FGSA.Run.RiseOneBy',
    'AvailableChain.FGSA.Run.boot_height_one',
    'AvailableChain.FGSA.Run.boot_phase_one',
    'AvailableChain.FGSA.Run.boot_not_effective_one',
    'AvailableChain.FGSA.Run.healing_rise_one_of_frontier',
    'AvailableChain.FGSA.Run.healing_rise_one_frontier',
    'AvailableChain.FGSA.Run.healing_rise_one_phase',
    'AvailableChain.FGSA.Run.healing_rise_one_split',
    'AvailableChain.FGSA.Run.healing_rise_one_entry',
    'AvailableChain.FGSA.Run.healing_rise_one_gate_copy',
    'AvailableChain.FGSA.Run.healing_rise_one_height',
    'AvailableChain.FGSA.Run.healing_rise_one_grid',
    'AvailableChain.FGSA.Run.healing_rise_one_repair',
    'AvailableChain.FGSA.Run.healing_rise_one_repair_synchronous',
    'AvailableChain.FGSA.Run.healing_rise_one_first_opening',
    'AvailableChain.FGSA.Run.healing_rise_one_later_opening',
    'AvailableChain.FGSA.Run.healing_rise_one_repair_opening',
    # H-FRONT-OPEN: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.FrontierOpeningServed',
    'AvailableChain.FGSA.Run.frontier_open_indices',
    'AvailableChain.FGSA.Run.frontier_open_domain',
    'AvailableChain.FGSA.Run.frontier_open_plateau',
    'AvailableChain.FGSA.Run.frontier_open_of_served',
    'AvailableChain.FGSA.Run.frontier_open_q_eq',
    'AvailableChain.FGSA.Run.frontier_open_later',
    'AvailableChain.FGSA.Run.frontier_open_time',
    'AvailableChain.FGSA.Run.frontier_openings',
    # F-ABOVE-A: --expect DATA only.
    'AvailableChain.FGSA.Run.honestFrontier_le_opening',
    'AvailableChain.FGSA.Run.opening_height_succ_eq_middle',
    # O-EXPORT-2: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.outage_cleanGrowthClaim_of',
    'AvailableChain.FGSA.Run.fgsa_cleanGrowthClaim_of_clean',
    # O-EXPORT-1b: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.fgsa_exactProposalClaim_of_clean',
    'AvailableChain.FGSA.Run.fgsa_cleanInclusionPostGateClaim_of_clean',
    'AvailableChain.FGSA.Run.fgsa_cleanInclusionClaim_of_clean',
    # O-EXPORT-1: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.outage_exactProposalClaim_of',
    'AvailableChain.FGSA.Run.outage_cleanInclusionPostGateClaim_of',
    'AvailableChain.FGSA.Run.outage_cleanInclusionClaim_of',
    # post-freeze additive _def batch 2: --expect DATA only.
    'AvailableChain.FGSA.Run.finHeight_def',
    'AvailableChain.FGSA.Run.HealSuffix_def',
    'AvailableChain.FGSA.Run.healStart_def',
    'AvailableChain.FGSA.Run.tstar_def',
    'AvailableChain.FGSA.Run.S_at_def',
    'AvailableChain.FGSA.Run.outputS_def',
    # S5 GROWTH: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.fgsa_timeIdx_now_le',
    'AvailableChain.FGSA.Run.fgsa_output_noFuture_of_slot',
    'AvailableChain.FGSA.Run.fgsa_proposal_emission_exists_of_awake_slot',
    'AvailableChain.FGSA.Run.fgsa_honestProposal_exists_of_awake_slot',
    'AvailableChain.FGSA.Run.jointGrowthAt_of_inclusion',
    'AvailableChain.FGSA.Run.fgsa_outputAt_eq_S_at',
    'AvailableChain.FGSA.Run.fgsa_healSuffix_timeIdx',
    'AvailableChain.FGSA.Run.fgsa_healed_output_mono',
    'AvailableChain.FGSA.Run.clean_growth_body',
    'AvailableChain.FGSA.Run.fgsa_availableGrowthGST',
    # S5 I-GATE/I-READ: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.inclusion_headAtLabel',
    'AvailableChain.FGSA.Run.inclusion_prior_results_below',
    'AvailableChain.FGSA.Run.inclusion_preGate_bounds',
    'AvailableChain.FGSA.Run.inclusion_awake_seat_batch',
    'AvailableChain.FGSA.Run.inclusion_gate_exact',
    'AvailableChain.FGSA.Run.clean_inclusion_post_gate_body',
    'AvailableChain.FGSA.Run.clean_inclusion_body',
    # H-FRAME: --expect additions only.
    'AvailableChain.FGSA.Run.healing_proposal_full_witness',
    'AvailableChain.FGSA.Run.healing_full_witness',
    'AvailableChain.FGSA.Run.healing_held_block_receipt',
    'AvailableChain.FGSA.Run.healing_witness_relay',
    'AvailableChain.FGSA.Run.healing_proposer_floor',
    'AvailableChain.FGSA.Run.healing_source_slot',
    'AvailableChain.FGSA.Run.healing_tGeom',
    'AvailableChain.FGSA.Run.healing_retained_path',
    'AvailableChain.FGSA.Run.healing_frozen_path',
    'AvailableChain.FGSA.Run.healing_carried_path',
    'AvailableChain.FGSA.Run.healing_full_witness_all',
    'AvailableChain.FGSA.Run.healing_witness_relay_phase',
    # H-PROMOTE helpers: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_promotion_gap_remainder',
    'AvailableChain.FGSA.Run.healing_promotion_gap',
    'AvailableChain.FGSA.Run.healing_promotion_row_deadline',
    'AvailableChain.FGSA.Run.healing_promotion_row_receipt',
    'AvailableChain.FGSA.Run.healing_promotion_maturity',
    'AvailableChain.FGSA.Run.healing_promotion_age_gap',
    'AvailableChain.FGSA.Run.healing_promotion_fixed_rows',
    'AvailableChain.FGSA.Run.healing_promotion_source_body',
    'AvailableChain.FGSA.Run.healing_promotion_source_parent',
    'AvailableChain.FGSA.Run.healing_promotion_continuing_service',
    # H-PROMOTE r2: --expect additions only.
    'AvailableChain.FGSA.Run.healing_promotion_entry_slot',
    'AvailableChain.FGSA.Run.healing_promotion_bounded_rows',
    'AvailableChain.FGSA.Run.healing_promotion_carrier',
    'AvailableChain.FGSA.Run.healing_promotion_slot_proposal',
    'AvailableChain.FGSA.Run.healing_promotion_gap_proposal',
    'AvailableChain.FGSA.Run.healing_promotion_same_rows',
    # H-PROMOTE r3: --expect additions only.
    'AvailableChain.FGSA.Run.healing_promotion_proposal_read',
    'AvailableChain.FGSA.Run.healing_promotion_proposal_reachable',
    'AvailableChain.FGSA.Run.healing_rows_above_entry_at_height',
    'AvailableChain.FGSA.Run.healing_promotion_quiet_window',
    'AvailableChain.FGSA.Run.healing_phase_extend_of_no_effective',
    'AvailableChain.FGSA.Run.healing_promotion_event_split',
    'AvailableChain.FGSA.Run.healing_promotion_advance',
    'AvailableChain.FGSA.Run.healing_promotion_first_receipt',
    'AvailableChain.FGSA.Run.healing_renewedPromotion',
    'AvailableChain.FGSA.Run.healing_promotion_age_service',
    # H-PROMOTE fix pass: --expect additions only.
    'AvailableChain.FGSA.Run.healing_promotion_row_deadline_strict',
    'AvailableChain.FGSA.Run.healing_promotion_row_receipt_strict',
    'AvailableChain.FGSA.Run.healing_promotion_maturity_of_action',
    'AvailableChain.FGSA.Run.healing_promotion_held_mono',
    # H-SUPPORT: --expect additions only.
    'AvailableChain.FGSA.Run.healing_settled_frame_strict',
    'AvailableChain.FGSA.Run.healing_witness_relay_settled',
    'AvailableChain.FGSA.Run.healing_head_witness_relay',
    'AvailableChain.FGSA.Run.healing_support_vote_backward',
    'AvailableChain.FGSA.Run.healing_support_target_path',
    'AvailableChain.FGSA.Run.healing_support_phaseBody_of_write',
    'AvailableChain.FGSA.Run.healing_last_write_support',
    'AvailableChain.FGSA.Run.healing_last_write_two_lease',
    'AvailableChain.FGSA.Run.healing_last_write_one_lease',
    'AvailableChain.FGSA.Run.healing_support_release_compat',
    'AvailableChain.FGSA.Run.healing_first_transfer_core',
    'AvailableChain.FGSA.Run.healing_first_transfer_fast',
    'AvailableChain.FGSA.Run.healing_next_transfer_core',
    'AvailableChain.FGSA.Run.healing_heads_transfer',
    'AvailableChain.FGSA.Run.healing_fast_heads_transfer',
    'AvailableChain.FGSA.Run.healing_support_gate_cover',
    'AvailableChain.FGSA.Run.healing_fast_lease_at',
    'AvailableChain.FGSA.Run.healing_fast_heads',
    'AvailableChain.FGSA.Run.healing_output_cover',
    'AvailableChain.FGSA.Run.healing_fast_output',
    'AvailableChain.FGSA.Run.healing_proposals_cover',
    'AvailableChain.FGSA.Run.healing_fast_proposals',
    'AvailableChain.FGSA.Run.healing_saved_origin',
    'AvailableChain.FGSA.Run.healing_slow_honest_seat',
    'AvailableChain.FGSA.Run.healing_slow_lease_at',
    'AvailableChain.FGSA.Run.healing_slow_first_transfer',
    'AvailableChain.FGSA.Run.healing_slow_heads',
    'AvailableChain.FGSA.Run.healing_slow_proposals',
    'AvailableChain.FGSA.Run.healing_slow_output',
    'AvailableChain.FGSA.Run.healing_phase_transfers',
    'AvailableChain.FGSA.Run.healing_tPerm',
    # H-REPAIR: --expect additions only.
    'AvailableChain.FGSA.Run.retainedH6Input_on_repaired_reads',
    'AvailableChain.FGSA.Run.repair_head_two',
    'AvailableChain.FGSA.Run.retainedH6Input_on_synchronous_reads',
    'AvailableChain.FGSA.Run.repair_head_one',
    'AvailableChain.FGSA.Run.repair_h6c_window',
    'AvailableChain.FGSA.Run.repair_gate_geometry',
    'AvailableChain.FGSA.Run.repair_two_lease',
    'AvailableChain.FGSA.Run.repair_synchronous',
    'AvailableChain.FGSA.Run.healing_tRepair',
    # S5 G-HG1: --expect additions only.
    'AvailableChain.FGSA.Run.frontier_Q_heads',
    'AvailableChain.FGSA.Run.frontier_seed_leases',
    'AvailableChain.FGSA.Run.frontier_lease_cover',
    'AvailableChain.FGSA.Run.frontier_prior_support',
    'AvailableChain.FGSA.Run.frontier_target_scores',
    'AvailableChain.FGSA.Run.retainedHG1Input_through',
    'AvailableChain.FGSA.Run.retainedHG1Input_before_first_rise',
    # H-COMMON: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.common_first_opening_labels',
    'AvailableChain.FGSA.Run.common_first_time_bound',
    'AvailableChain.FGSA.Run.common_source_tick',
    'AvailableChain.FGSA.Run.common_source_height_le',
    'AvailableChain.FGSA.Run.common_source_below_raw',
    'AvailableChain.FGSA.Run.common_sources_compatible',
    'AvailableChain.FGSA.Run.common_entry_of_plateau',
    'AvailableChain.FGSA.Run.common_low_or_high',
    'AvailableChain.FGSA.Run.common_sources_extend_and_cap',
    'AvailableChain.FGSA.Run.common_entry_at_high',
    'AvailableChain.FGSA.Run.common_next_sources_extend_and_cap',
    'AvailableChain.FGSA.Run.common_next_entry',
    'AvailableChain.FGSA.Run.common_entry_at_low',
    'AvailableChain.FGSA.Run.common_opening_covered',
    'AvailableChain.FGSA.Run.healing_tCommon',
    'AvailableChain.FGSA.Run.common_height_one',
    # H-GATE: --expect additions only.
    'AvailableChain.FGSA.Run.opening_gate_guard',
    'AvailableChain.FGSA.Run.opening_gateService_of_cover',
    'AvailableChain.FGSA.Run.later_opening_service',
    'AvailableChain.FGSA.Run.later_opening_gateService_domain',
    'AvailableChain.FGSA.Run.opening_transfer',
    'AvailableChain.FGSA.Run.later_opening_source_extends',
    'AvailableChain.FGSA.Run.next_opening_body_service',
    'AvailableChain.FGSA.Run.later_opening_covered',
    'AvailableChain.FGSA.Run.opening_height_one',
    # S5 I-EXACT r2: G1 producer and E1/E2 theorems; --expect additions only.
    'AvailableChain.FGSA.Run.inclusion_retained_reads',
    'AvailableChain.FGSA.Run.inclusion_exact_compat',
    'AvailableChain.FGSA.Run.inclusion_exact_receipt',
    'AvailableChain.FGSA.Run.inclusion_exact_head',
    # S5 O-INDUCT/O-CLOSE: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.outage_disclosed_crossing',
    'AvailableChain.FGSA.Run.outage_disclosed_justification',
    'AvailableChain.FGSA.Run.outage_disclosed_finalization',
    'AvailableChain.FGSA.Run.outage_delivery_frame',
    'AvailableChain.FGSA.Run.outage_liveRoot_covers',
    'AvailableChain.FGSA.Run.outage_release_bound',
    'AvailableChain.FGSA.Run.outage_armed_induction',
    'AvailableChain.FGSA.Run.outage_source_history',
    'AvailableChain.FGSA.Run.lease_or_F_persists',
    'AvailableChain.FGSA.Run.duties_and_outputs',
    'AvailableChain.FGSA.Run.outage_compat_body',
    'AvailableChain.FGSA.Run.fast_p1_body',
    'AvailableChain.FGSA.Run.slow_p1_body',
    # S5 O-ARM: --expect additions only.
    'AvailableChain.FGSA.Run.ArmingData_def',
    'AvailableChain.FGSA.Run.fast_arming',
    'AvailableChain.FGSA.Run.slow_arming',
    'AvailableChain.FGSA.Run.pending_gate_lease_or_F',
    # S5 I-EXACT: --expect additions only; G1 remains open.
    'AvailableChain.FGSA.Run.inclusion_acceptance_of_stored',
    'AvailableChain.FGSA.Run.inclusion_receipt_of_compatible',
    'AvailableChain.FGSA.Run.inclusion_proposal_receipt',
    'AvailableChain.FGSA.Run.inclusion_head_read',
    'AvailableChain.FGSA.Run.inclusion_sleep_silence',
    'AvailableChain.FGSA.Run.inclusion_comparison_prefix',
    # FF2-INV: --expect DATA only.
    'AvailableChain.FGSA.Run.high_source_entry_eq',
    'AvailableChain.FGSA.Run.high_record_target_choice',
    'AvailableChain.FGSA.Run.high_entry_record_invariant',
    'AvailableChain.FGSA.Run.high_record_fresh_at_cut',
    'AvailableChain.FGSA.Run.high_record_reset_fresh',
    'AvailableChain.FGSA.Run.high_record_guards_and_fresh',
    'AvailableChain.FGSA.Run.high_target_row_covered',
    'AvailableChain.FGSA.Run.high_target_first_row',
    'AvailableChain.FGSA.Run.high_target_honest_quorum',
    'AvailableChain.FGSA.Run.high_target_quorum_covered',
    # FF2-INV r2: --expect DATA only.
    'AvailableChain.FGSA.Run.high_action_target_choice',
    'AvailableChain.FGSA.Run.high_record_guards_and_fresh_at_action',
    'AvailableChain.FGSA.Run.ff2_stored_high_qc_identity',
    'AvailableChain.FGSA.Run.ff2_high_qc_identity',
    'AvailableChain.FGSA.Run.ff2_no_high_contest',
    'AvailableChain.FGSA.Run.HighRecordGuard_W',
    'AvailableChain.FGSA.Run.HighRecordGuard_W_def',
    'AvailableChain.FGSA.Run.ff2_high_record_guards',
    # K-ROWS-PREM: --expect DATA only.
    'AvailableChain.FGSA.Run.pending_action_domain_cap',
    'AvailableChain.FGSA.Run.rowsPrem_postClock_store',
    'AvailableChain.FGSA.Run.rowsPrem_F_below_D_at_gate',
    'AvailableChain.FGSA.Run.rowsPrem_action_frame',
    'AvailableChain.FGSA.Run.rowsPrem_full_domain',
    'AvailableChain.FGSA.Run.rowsPrem_liveRoot_compatible',
    'AvailableChain.FGSA.Run.rowsPrem_action_pools',
    'AvailableChain.FGSA.Run.rowsPrem_earlier_height',
    'AvailableChain.FGSA.Run.rowsPrem_action_record',
    # K-ROWS-PREM P3: --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_action_walk_batch',
    'AvailableChain.FGSA.Run.finality_action_time_bounds',
    'AvailableChain.FGSA.Run.rowsPrem_action_walk_batch',
    'AvailableChain.FGSA.Run.pending_action_head_capped',
    'AvailableChain.FGSA.Run.rowsPrem_pending_head',
    'AvailableChain.FGSA.Run.rowsPrem_action_source',
    'AvailableChain.FGSA.Run.rowsPrem_fresh_rows',
    'AvailableChain.FGSA.Run.rowsPrem_anchor_cap',
    'AvailableChain.FGSA.Run.rowsPrem_anchor_retained_or_covered',
    # K-MID: --expect DATA only.
    'AvailableChain.FGSA.Run.kernel_opening_and_middle',
    'AvailableChain.FGSA.Run.kernel_middle_fresh_U',
    'AvailableChain.FGSA.Run.kernel_middle_early_justification',
    'AvailableChain.FGSA.Run.kernel_middle_source_cap',
    'AvailableChain.FGSA.Run.kmid_source_held_at_tick',
    # K-TAIL: --expect DATA only.
    'AvailableChain.FGSA.Run.TailOpeningWitness_W',
    'AvailableChain.FGSA.Run.tail_opening_and_witness',
    'AvailableChain.FGSA.Run.ktail_retained_or_covered',
    'AvailableChain.FGSA.Run.ktail_plateau_action_head',
    'AvailableChain.FGSA.Run.ktail_fresh_rows',
    'AvailableChain.FGSA.Run.ktail_record_guards_at_action',
    'AvailableChain.FGSA.Run.ktail_action_frame',
    'AvailableChain.FGSA.Run.ktail_gate_finality',
    'AvailableChain.FGSA.Run.ktail_action_source',
    'AvailableChain.FGSA.Run.ktail_witness_split',
    'AvailableChain.FGSA.Run.ktail_finalized_propagates',
    'AvailableChain.FGSA.Run.ktail_pending_rows',
    'AvailableChain.FGSA.Run.ktail_terminal_key',
    'AvailableChain.FGSA.Run.ktail_acceptPrem_W',
    # K-TAIL r2: --expect DATA only.
    'AvailableChain.FGSA.Run.ktail_jPath',
    'AvailableChain.FGSA.Run.ktail_hj_floor',
    'AvailableChain.FGSA.Run.ktail_acceptPrem_two_W',
    'AvailableChain.FGSA.Run.ktail_terminal_path',
    'AvailableChain.FGSA.Run.ktail_rows_through_next',
    'AvailableChain.FGSA.Run.ktail_terminal_final',
    'AvailableChain.FGSA.Run.tail_kernel_W_of',
    # K-TAIL r3: --expect DATA only.
    'AvailableChain.FGSA.Run.ktail_entry_bits',
    'AvailableChain.FGSA.Run.ktail_final_quorum',
    'AvailableChain.FGSA.Run.ktail_r6w_transfer',
    'AvailableChain.FGSA.Run.ktail_head_delivered',
    'AvailableChain.FGSA.Run.ktail_mixed_final',
    'AvailableChain.FGSA.Run.ktail_hmixed_of_relay',
    'AvailableChain.FGSA.Run.tail_kernel_W_of_relay',
    # K-TAIL r4: --expect DATA only.
    'AvailableChain.FGSA.Run.ktail_action_walk_batch',
    'AvailableChain.FGSA.Run.tail_kernel_W_full_of',
    'AvailableChain.FGSA.Run.fgsa_tailKernel_W_of',
    'AvailableChain.FGSA.Run.fgsa_tailKernel_W',
    # HBEST STATEMENT: companion --expect DATA additions only.
    'AvailableChain.FGSA.Run.HTimeBestConcl',
    'AvailableChain.FGSA.Run.HTimeBestConcl_def',
    'AvailableChain.FGSA.Run.HTimeBestClaim',
    'AvailableChain.FGSA.Run.HTimeSearchClaim',
    # B33 WC-LIVE additive: --expect DATA additions only.
    'AvailableChain.FGSA.Run.ServedFromGateAt',
    'AvailableChain.FGSA.Run.ServedFromGateAt_def',
    'AvailableChain.FGSA.Run.JointGrowthAt',
    'AvailableChain.FGSA.Run.JointGrowthAt_def',
    'AvailableChain.FGSA.Run.WeakContinuationLiveAt₂',
    'AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk',
    'AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety',
    'AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion',
    'AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth',
    'AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂',
    'AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def',
    'AvailableChain.FGSA.Run.WeakContinuationLiveClaim',
    # C-CORE: --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_tStart',
    'AvailableChain.FGSA.Run.fgsa_tWalk',
    'AvailableChain.FGSA.Run.fgsa_tVote',
    'AvailableChain.FGSA.Run.fgsa_coreServices',
    # B30 Finality Export: --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_kernelACSide_W',
    # A-KERNEL B34: --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_finalityKernel_W_of',
    'AvailableChain.FGSA.Run.fgsa_finalityKernel_W',
    # K-FWD: --expect DATA only.
    'AvailableChain.FGSA.Run.finality_kernel_W_of',
    # F-LOCAL: --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_finalityLivenessRecFE_W_of',
    'AvailableChain.FGSA.Run.fgsa_finalityLivenessRecF4_W_of',
    'AvailableChain.FGSA.Run.fgsa_finalityLivenessRecFE_W',
    'AvailableChain.FGSA.Run.fgsa_finalityLivenessRecF4_W',
    'AvailableChain.FGSA.Run.ForwardWitness_W',
    'AvailableChain.FGSA.Run.ForwardWitness_W_def',
    'AvailableChain.FGSA.Run.forward_witness_FE_of',
    'AvailableChain.FGSA.Run.finality_liveness_of_forward_W',
    'AvailableChain.FGSA.Run.finality_liveness_FE_W_of',
    'AvailableChain.FGSA.Run.finality_liveness_F4_W_of',
    # F-PROP: --expect DATA only.
    'AvailableChain.FGSA.Run.proposal_final_of_forward_W',
    'AvailableChain.FGSA.Run.proposal_final_FE_W_of',
    'AvailableChain.FGSA.Run.proposal_final_F4_W_of',
    'AvailableChain.FGSA.Run.fgsa_proposalFinalRecFE_W_of',
    'AvailableChain.FGSA.Run.fgsa_proposalFinalRecF4_W_of',
    'AvailableChain.FGSA.Run.fgsa_proposalFinalRecFE_W',
    'AvailableChain.FGSA.Run.fgsa_proposalFinalRecF4_W',
    # K-JOIN: --expect DATA only.
    'AvailableChain.FGSA.Run.finality_kernel_prem_W_of_joined',
    'AvailableChain.FGSA.Run.finality_kernel_joined_W_of',
    'AvailableChain.FGSA.Run.fgsa_finalityKernelJoined_W_of',
    'AvailableChain.FGSA.Run.fgsa_finalityKernelJoined_W',
    # K-HISTORY: run-level history bodies; --expect DATA only.
    'AvailableChain.FGSA.Run.noMixedPreBatchParent',
    'AvailableChain.FGSA.Run.justifyFresh_W',
    'AvailableChain.FGSA.Run.raw_causal_cap_before',
    'AvailableChain.FGSA.Run.raw_causal_cap_at_tick',
    'AvailableChain.FGSA.Run.raw_causal_cap_through_action',
    # K-HEIGHT: height adapters; --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_foldTrichotomy_target',
    'AvailableChain.FGSA.Run.fgsa_foldTrichotomy_progress',
    'AvailableChain.FGSA.Run.fgsa_storedProgressConsume',
    'AvailableChain.FGSA.Run.fgsa_noMixedMaturity',
    'AvailableChain.FGSA.Run.fgsa_justifyAt',
    # K-RECEIPT: --expect DATA only; fields and the terminal receipt producer.
    'AvailableChain.FGSA.Run.receipt_kernel_fields',
    'AvailableChain.FGSA.Run.receipt_finalized_of_carriage',
    'AvailableChain.FGSA.Run.receipt_finCmp',
    'AvailableChain.FGSA.Run.receipt_cap',
    'AvailableChain.FGSA.Run.receipt_receiver_finalityLag',
    'AvailableChain.FGSA.Run.receipt_jPath_of_cached_anchor',
    'AvailableChain.FGSA.Run.receipt_finCmp_of_block',
    'AvailableChain.FGSA.Run.receipt_ready_of_delivery',
    'AvailableChain.FGSA.Run.receipt_delivery',
    'AvailableChain.FGSA.Run.receipt_jPath',
    'AvailableChain.FGSA.Run.receipt_acceptPrem_W',
    # K-ROWS: --expect DATA only.
    'AvailableChain.FGSA.Run.pending_action_head',
    'AvailableChain.FGSA.Run.finality_action_source',
    'AvailableChain.FGSA.Run.fresh_unanimous_rows',
    'AvailableChain.FGSA.Run.actual_anchor_cap',
    'AvailableChain.FGSA.Run.actual_anchor_retained_or_covered',
    # K-CARRY: --expect DATA only.
    'AvailableChain.FGSA.Run.terminalCarriage_general_W',
    'AvailableChain.FGSA.Run.terminalCarriage_W_of_tRowsSelect',
    # K-BATCH: --expect DATA only.
    'AvailableChain.FGSA.Run.finalityRow_bit_or_carried_W',
    'AvailableChain.FGSA.Run.finalityBatchCoverage_W_of_tRowsSelect',
    # K-ACCEPT: --expect data only.
    'AvailableChain.FGSA.Run.fgsa_acceptBefore_W',
    'AvailableChain.FGSA.Run.fgsa_finalizePending_W',
    # S4.6c: --expect DATA only.
    'AvailableChain.FGSA.Run.fgsa_availableGST',
    'AvailableChain.FGSA.Run.AvailableFromConcl',
    'AvailableChain.FGSA.Run.AvailableGrowthConcl',
    'AvailableChain.FGSA.Run.AvailableGSTClaim',
    'AvailableChain.FGSA.Run.AvailableGrowthGSTClaim',
    'AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecFE',
    'AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecF4',
    'AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecFE',
    'AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecF4',
    'AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecFE',
    'AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecF4',
    'AvailableChain.FGSA.Run.FGSAClaims.availableGST',
    'AvailableChain.FGSA.Run.FGSAClaims.availableGrowthGST',
    # S4.7 Opus P1: clean growth (DC confirmedLive/stableLive under LiveSleepyRegime).
    'AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom',
    'AvailableChain.FGSA.Run.CleanGrowthClaim',
    'AvailableChain.FGSA.Run.FGSAClaims.cleanGrowth',
    'AvailableChain.FGSA.Run.fgsa_apiHonestNeverSlashedClaim_body',
    'AvailableChain.FGSA.Run.fgsa_pureAccountableClaim',
    'AvailableChain.FGSA.Run.fgsa_pureAgreementClaim',
    'AvailableChain.FGSA.Run.fgsa_wholeRunAccountableClaim',
    'AvailableChain.FGSA.Run.fgsa_wholeRunAgreementClaim',
    'AvailableChain.FGSA.Run.fgsa_eventPrefixAgreementClaim',
    'AvailableChain.FGSA.Run.fgsa_faultCountSlashableBoundClaim',
    'AvailableChain.FGSA.Run.fgsa_finalizedMonotonicityClaim',
    'AvailableChain.FGSA.Run.fgsa_honestNeverSlashedClaim',
    'AvailableChain.FGSA.Run.fgsa_finalizedSafetyClaim',
    'AvailableChain.FGSA.Run.fgsa_finalLockClaim',
    # S4.6b GST forms: --expect DATA only.
    'AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W',
    'AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk',
    'AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set',
    'AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late',
    'AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor',
    'AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W',
    'AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W',
    'AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk',
    'AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set',
    'AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop',
    'AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late',
    'AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor',
    'AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W',
    'AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W',
    'AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk',
    'AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set',
    'AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late',
    'AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor',
    'AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W',
    'AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recFE',
    'AvailableChain.FGSA.Run.fgsa_firstFinality_recFE',
    'AvailableChain.FGSA.Run.fgsa_firstFinality_recF4',
    'AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recF4',
    'AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recFE',
    'AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recF4',
    'AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recFE',
    'AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recF4',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.mk',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.accountable',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.agreement',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.runAccountable',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.runAgreement',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.eventPrefixAgreement',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.faultCountSlashableBound',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.finalizedMonotone',
    'AvailableChain.FGSA.Run.FGSAFinalityClaims.honestNeverSlashed',
    'AvailableChain.FGSA.Run.FGSAClaims',
    'AvailableChain.FGSA.Run.FGSAClaims.mk',
    'AvailableChain.FGSA.Run.FGSAClaims.toFGSASafetyClaims',
    'AvailableChain.FGSA.Run.FGSAClaims.finality',
    'AvailableChain.FGSA.Run.FGSAClaims.finalizedSafety',
    'AvailableChain.FGSA.Run.FGSAClaims.finalLock',
    'AvailableChain.FGSA.Run.FGSAClaims.outageCompat',
    'AvailableChain.FGSA.Run.FGSAClaims.fastP1',
    'AvailableChain.FGSA.Run.FGSAClaims.slowP1',
    'AvailableChain.FGSA.Run.FGSAClaims.exactProposal',
    'AvailableChain.FGSA.Run.FGSAClaims.cleanInclusionPostGate',
    'AvailableChain.FGSA.Run.FGSAClaims.cleanInclusion',
    'AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecFE',
    'AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecF4',
    # S5 F-EXPORT: Foundations producers and the active-height cap adapter.
    'AvailableChain.FGSA.Run.fgsa_rXing',
    'AvailableChain.FGSA.Run.fgsa_rCap_heightView',
    'AvailableChain.FGSA.Run.fgsa_rCap_channel',
    # H-PHASE: --expect additions only.
    'AvailableChain.FGSA.Run.healing_phaseWitness',
    'AvailableChain.FGSA.Run.healing_phase_initial_frontier',
    'AvailableChain.FGSA.Run.healing_phase_height_le',
    'AvailableChain.FGSA.Run.healing_phase_justified_lt',
    'AvailableChain.FGSA.Run.healing_phase_finality_le',
    'AvailableChain.FGSA.Run.healing_phase_frontier_witness',
    'AvailableChain.FGSA.Run.healing_phase_frontier_root',
    'AvailableChain.FGSA.Run.healing_frontier_mem',
    'AvailableChain.FGSA.Run.healing_phase_frame',
    'AvailableChain.FGSA.Run.healing_settled_frame',
    'AvailableChain.FGSA.Run.healing_phase_local_le_frontier',
    'AvailableChain.FGSA.Run.healing_phase_top_persist',
    'AvailableChain.FGSA.Run.healing_phase_contest_persist',
    'AvailableChain.FGSA.Run.healing_phase_order',
    'AvailableChain.FGSA.Run.healing_phase_block_receipt',
    'AvailableChain.FGSA.Run.healing_evidence_spread',
    'AvailableChain.FGSA.Run.healing_phase_rows_spread',
    # H-PHASE r2: --expect additions only.
    'AvailableChain.FGSA.Run.healing_phase_idx_le_time',
    'AvailableChain.FGSA.Run.healing_phase_lt_timeIdx',
    'AvailableChain.FGSA.Run.healing_phase_idxBefore_mono',
    'AvailableChain.FGSA.Run.healing_frontier_mono',
    'AvailableChain.FGSA.Run.healing_phase_held_receipt',
    'AvailableChain.FGSA.Run.healing_phase_entries_eq',
    'AvailableChain.FGSA.Run.healing_phase_window',
    'AvailableChain.FGSA.Run.healing_phase_top_node',
    'AvailableChain.FGSA.Run.healing_settle_event',
    'AvailableChain.FGSA.Run.healing_rPhase',
    'AvailableChain.FGSA.Run.healing_phase_first_rise',
    'AvailableChain.FGSA.Run.healing_attemptValid_of_event',
    # W1b: bounded positive execution facts; --expect additions.
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positivePrefix',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.firstHead',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.firstProposal',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_tick',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_output',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_receive_zero',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_receive_one',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_receive_two',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_receive_three',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_tick',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_output',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_receive_zero',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_receive_one',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_receive_two',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_receive_three',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_accepted',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.firstRow',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_row_tick',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_row_output',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_row_receive',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_row_admitted',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_six_zero',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_six_one',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_six_two',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_six_three',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_head_length',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_proposal_length',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_accept_length',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_row_length',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_prefix',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_get_extend',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_get',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_get',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_state',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_state',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_output',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_output',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_head',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_head',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_proposal',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_proposal',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_accepted',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_accepted',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_row',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_row',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_pool',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_pool',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_signer_honest',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_early_row_time',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_no_earlier_row',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_first_row',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_head_receipts',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_head_receipts',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_proposal_receipts',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_proposal_receipts',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_source_row_receipt',
    'AvailableChain.FGSA.Run.Tests.WitnessPositive.positive_continuation_row_receipt',
    # D4b timing: --expect additions only.
    'AvailableChain.FGSA.Run.cap_finality_head',
    'AvailableChain.FGSA.Run.healing_finality_source_clock',
    'AvailableChain.FGSA.Run.healing_rFProv_finality',
    # D4 timing: --expect additions only.
    'AvailableChain.FGSA.Run.healing_low_finality_at_reset',
    'AvailableChain.FGSA.Run.healing_row_delivery',
    'AvailableChain.FGSA.Run.healing_receipt_before_tick',
    'AvailableChain.FGSA.Run.healing_action_period',
    'AvailableChain.FGSA.Run.healing_delivery_clock',
    'AvailableChain.FGSA.Run.healing_justification_timed',
    'AvailableChain.FGSA.Run.healing_justified_source_clock',
    'AvailableChain.FGSA.Run.healing_action_source_held',
    # H-DESCENT: --expect additions only.
    'AvailableChain.FGSA.Run.healing_source_gate',
    'AvailableChain.FGSA.Run.healing_source_read',
    'AvailableChain.FGSA.Run.healing_descent',
    'AvailableChain.FGSA.Run.healing_entry_pair_incompatible',
    'AvailableChain.FGSA.Run.healing_descent_pair',
    'AvailableChain.FGSA.Run.healing_high_pair_compat',
    'AvailableChain.FGSA.Run.healing_high_source_first_failure',
    'AvailableChain.FGSA.Run.healing_finality_source',
    'AvailableChain.FGSA.Run.healing_justified_source',
    'AvailableChain.FGSA.Run.healing_rExcl',
    # H-DESCENT D2: --expect additions only.
    'AvailableChain.FGSA.Run.SrcN_def',
    'AvailableChain.FGSA.Run.HighSrcN_def',
    'AvailableChain.FGSA.Run.Lost_def',
    'AvailableChain.FGSA.Run.healing_srcN_of_source',
    'AvailableChain.FGSA.Run.healing_headAtIdx_tick',
    'AvailableChain.FGSA.Run.healing_idx_lt_of_time_lt',
    'AvailableChain.FGSA.Run.healing_source_decode',
    'AvailableChain.FGSA.Run.healing_high_source_sync',
    'AvailableChain.FGSA.Run.healing_high_source_labelSync',
    'AvailableChain.FGSA.Run.healing_loss_same',
    'AvailableChain.FGSA.Run.healing_source_supporter',
    'AvailableChain.FGSA.Run.healing_loss_of_supporter',
    'AvailableChain.FGSA.Run.healing_loss_support',
    'AvailableChain.FGSA.Run.healing_first_transfer_domain',
    'AvailableChain.FGSA.Run.healing_block_receipt_sync',
    'AvailableChain.FGSA.Run.healing_block_path_sync',
    'AvailableChain.FGSA.Run.healing_block_stamp_le_now',
    'AvailableChain.FGSA.Run.healing_batch_seat_sync',
    'AvailableChain.FGSA.Run.healing_next_transfer_domain',
    'AvailableChain.FGSA.Run.healing_loss_lease_late',
    'AvailableChain.FGSA.Run.healing_head_covers_root',
    'AvailableChain.FGSA.Run.healing_loss_late_source',
    'AvailableChain.FGSA.Run.healing_loss_single_cause',
    'AvailableChain.FGSA.Run.healing_loss_cause_of_view',
    'AvailableChain.FGSA.Run.healing_noLoss_heads',
    'AvailableChain.FGSA.Run.healing_loss_F_below',
    'AvailableChain.FGSA.Run.healing_source_receipt',
    'AvailableChain.FGSA.Run.healing_loss_domain',
    'AvailableChain.FGSA.Run.healing_loss_cause',
    'AvailableChain.FGSA.Run.healing_high_source_compat',
    'AvailableChain.FGSA.Run.healing_high_source_compat_reset',
    'AvailableChain.FGSA.Run.emittedName_window',
    # H-BASE: --expect additions only.
    'AvailableChain.FGSA.Run.healing_rXing',
    'AvailableChain.FGSA.Run.healing_rCap',
    'AvailableChain.FGSA.Run.healing_phase_receipt',
    'AvailableChain.FGSA.Run.healing_source_time',
    # W1-PORT: concrete window-model source and continuation; --expect additions.
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.params',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.Validator',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.Event',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.World',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.strongEnv',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.weakEnv',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.seatOf',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.runData',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.nodes',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tickBatch',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.deliverOne',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.buildPrefix',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.buildSuffix',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.design_numbers',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.delta_ratio',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.bounds',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.witness_window_bounds',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.horizons',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.endpoint',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.covered',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.environments',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.honest_sets',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.faulty_sets',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.fault_bound',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.strong_awake',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.weak_awake_iff',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.awake_agreement',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.strong_awake_set',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.weak_awake_set_before',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.weak_awake_set_after',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.awake_counts',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.witness_participation',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.strict_drop',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.later_sleep',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.cstar',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.linked',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gap_positive',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gap_aligned',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_gap',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.boundary_duties',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.delivery_fold_mem',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_shape',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_time',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_no_restart',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.nodes_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_tick',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.witness_prefix_times',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_times',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_no_restart',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_no_restart',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.no_restart',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.event_prefix',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_after_endpoint',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.agreement_of_suffix',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.agreement',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.committees',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.recovery_awake',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_tick',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_tick',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_horizon_nonneg',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_horizon_nonneg',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_in_horizon',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_in_horizon',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_honest_only',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_honest_only',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_tick_public',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_tick_public',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_tick_total',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_tick_total',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_has_ticks',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.phase_le_two',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.key_le_delivery',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.delivery_fold_sorted',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_sorted',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_sorted',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_sorted',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_sorted',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_sorted',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.replay_of_agreement',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_replay',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genFold',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenFresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genFold_append',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genFresh_append',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tick_fold_replay',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tickBatch_replay',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tick_list_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.delivery_fold_replay_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_replay_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_replay_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_replay_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genFresh_get',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genFold_runData',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genFresh_join',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.runData_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_events_eq',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_genFresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_fresh',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenEmits',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenOrigin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genEmits_cons',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genEmits_append_left',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genEmits_append_right',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genOrigin_append',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tick_fold_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tickBatch_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.delivery_fold_sublist',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_block',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_blocks',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_blocks',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genEmits_runData',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_holder',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genOrigin_unforgeable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_genOrigin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_unforgeable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_emits_weak_to_strong',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_unforgeable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tick_nodup_without_gossip',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tick_fold_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.tickBatch_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.prefix_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.suffix_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_nodup',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_schedule',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_schedule',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.runData_stateBefore',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genOrigin_runData',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_delivery_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_delivery_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_nonproposal_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_derive_positive',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_attest_valid',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_seat',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_nonproposal_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.delivery_fold_offered',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.timeBatch_offered',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genOrigin_nonproposal_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_nonproposal_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_nonproposal_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_admitRow_duplicate',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_clock_fields',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_clock_proposals',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_clock_rowPool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_reconcile_fields',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_admitRow_eq',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_foldl_admitRow_eq',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_tick_st',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenStoredRows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_proposalRows_origin',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_storedRows_clock',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_storedRows_fold',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_storedRows_process',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_process_pool_mono',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenPoolWitness',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_proposal_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_pool_fields',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_fold_pool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_deliver_pool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_delivery_fold_pool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_timeBatch_pool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_prefix_pool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_suffix_pool',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_prefix_selected_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_suffix_selected_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_clock_votes',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenKnown',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_mono',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_clock',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_row',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_vote',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_lift_baseVote',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_base_proposal',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_decode_vote',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_decode_row',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_decode_proposal',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_reconcile',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_known_process',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_children_known',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_tick_fold_known',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_delivery_fold_known',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_timeBatch_known',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_timeBatch_delivered',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenPast',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenCarried',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_past_append',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_past_bound',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_batch_carried',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_prefix_carried',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_suffix_carried',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.genCarried_runData',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_carried',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_carried',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.source_signatures',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.continuation_signatures',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_tick_fold_pool_eq',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_batch_emitted_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_prefix_emitted_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_suffix_emitted_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_past_row_valid',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_prefix_rows_valid',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.gen_suffix_rows_valid',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_prefix_proposal_rows_valid',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_suffix_proposal_rows_valid',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.i7_eight_in_both_runs',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_rows',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_votes',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_wf',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_known_fold',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_rows_at_index',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_emit_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_schedule',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_continuation_wire',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_process_inert',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deliver_st',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_offer_st',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_tickBatch_st',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenUniformStores',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_offer_uniform',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_objects_uniform',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_uniform',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_uniform',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_suffix_uniform',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_tickBatch_emits',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_reachable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_tick_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_deps_start',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deps_mono',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deliver_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenDeps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deps_append',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_delivery_fold_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_ticks_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_suffix_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deps_get',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_continuation_genDeps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_continuation_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_deps',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_execution',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_continuation_execution',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_suffix_eq',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_schedule',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.GenSingleDutyUnique',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_emits_unique',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_head_accept',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_row_accept',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_processed_mono',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_process_processed',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deliver_processed',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_fold_processed',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_deliver_now',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_fold_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_nonproposal_accept',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_nonproposal_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_only',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_singleton',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_accept',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_proposal_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_emits',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_suffix_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_emission_time',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_not_past',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_clock_processed',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_known_fold_local',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_known_receipt',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_nonproposal_receipt',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_fold_no_local',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_tick_zero',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_fresh_start',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_proposal_receipt',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_receipt',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_batch_tick_state',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_locate_emission',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_broadcast',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_fold_stable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_prefix',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_stable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_past_complete',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_index_after',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_index_stable',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_handles_carries',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_child_processed',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_relay',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_direct_handle',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_prefix_sync',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_state',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_emits',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_source_sync',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_continuation_eq',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_continuation_sync',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_strongRecovery',
    'AvailableChain.FGSA.Run.Tests.WeakContinuationWitness.w1_cleanContinuation',
    # S4.5b restore: --expect DATA only.
    'AvailableChain.FGSA.Run.FGFinalizedAt_def',
    'AvailableChain.FGSA.Run.FinalityRunBlock_def',
    'AvailableChain.FGSA.Run.finalityStoreRows_def',
    'AvailableChain.FGSA.Run.FinalityCarriage_def',
    'AvailableChain.FGSA.Run.fgsa_apiPureAccountableClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiPureAgreementClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiWholeRunAccountableClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiWholeRunAgreementClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiEventPrefixAgreementClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiFaultCountSlashableBoundClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiFinalizedMonotonicityClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiFinalizedSafetyClaim_body',
    'AvailableChain.FGSA.Run.fgsa_apiFinalLockClaim_body',
    'AvailableChain.FGSA.Run.FinalityFinalizedAt',
    'AvailableChain.FGSA.Run.FinalityFinalizedAt_def',
    'AvailableChain.FGSA.Run.FinalityBlock',
    'AvailableChain.FGSA.Run.FinalityBlock_def',
    'AvailableChain.FGSA.Run.finalityRows',
    'AvailableChain.FGSA.Run.finalityRows_def',
    'AvailableChain.FGSA.Run.FinalitySlashableBound',
    'AvailableChain.FGSA.Run.FinalitySlashableBound_def',
    'AvailableChain.FGSA.Run.FinalityExecution',
    'AvailableChain.FGSA.Run.FinalityExecution_def',
    'AvailableChain.FGSA.Run.WholeRunAccountable',
    'AvailableChain.FGSA.Run.WholeRunAccountable_def',
    'AvailableChain.FGSA.Run.WholeRunAgreement',
    'AvailableChain.FGSA.Run.WholeRunAgreement_def',
    'AvailableChain.FGSA.Run.CleanInclusionPrem',
    'AvailableChain.FGSA.Run.CleanInclusionPrem.mk',
    'AvailableChain.FGSA.Run.CleanInclusionPrem.set',
    'AvailableChain.FGSA.Run.CleanInclusionPrem.prop',
    'AvailableChain.FGSA.Run.CleanInclusionPrem.hhor',
    'AvailableChain.FGSA.Run.ExactProposalPrem',
    'AvailableChain.FGSA.Run.ExactProposalPrem.mk',
    'AvailableChain.FGSA.Run.ExactProposalPrem.set',
    'AvailableChain.FGSA.Run.ExactProposalPrem.prop',
    'AvailableChain.FGSA.Run.ExactProposalPrem.hhor',
    'AvailableChain.FGSA.Run.PureAccountableClaim',
    'AvailableChain.FGSA.Run.PureAgreementClaim',
    'AvailableChain.FGSA.Run.WholeRunAccountableClaim',
    'AvailableChain.FGSA.Run.WholeRunAgreementClaim',
    'AvailableChain.FGSA.Run.EventPrefixAgreementClaim',
    'AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim',
    'AvailableChain.FGSA.Run.FinalizedMonotonicityClaim',
    'AvailableChain.FGSA.Run.HonestNeverSlashedClaim',
    'AvailableChain.FGSA.Run.FinalizedSafetyConcl',
    'AvailableChain.FGSA.Run.FinalizedSafetyClaim',
    'AvailableChain.FGSA.Run.FinalLockClaim',
    'AvailableChain.FGSA.Run.ExactProposalAt',
    'AvailableChain.FGSA.Run.ExactProposalClaim',
    'AvailableChain.FGSA.Run.InclusionPostGateAt',
    'AvailableChain.FGSA.Run.InclusionAt',
    'AvailableChain.FGSA.Run.CleanInclusionPostGateClaim',
    'AvailableChain.FGSA.Run.CleanInclusionClaim',
    'AvailableChain.FGSA.Run.DutiesExtendOn',
    'AvailableChain.FGSA.Run.FCompatBefore',
    'AvailableChain.FGSA.Run.P1Concl',
    'AvailableChain.FGSA.Run.LeaseOrFFrom',
    'AvailableChain.FGSA.Run.OutageCompatAt',
    'AvailableChain.FGSA.Run.OutageCompatClaim',
    'AvailableChain.FGSA.Run.FastP1Claim',
    'AvailableChain.FGSA.Run.SlowP1Claim',

    'AvailableChain.FGSA.Run.RetainedTargetScores',
    'AvailableChain.FGSA.Run.RetainedConeInput',
    'AvailableChain.FGSA.Run.RetainedL2Input',
    'AvailableChain.FGSA.Run.fgsa_retainedReads_H17',
    'AvailableChain.FGSA.Run.fgsa_retainedReads_L4R',
    'AvailableChain.FGSA.Run.fgsa_retainedReads_HG1',
    'AvailableChain.FGSA.Run.fgsa_retainedReads_L2',
    'AvailableChain.FGSA.Run.RetainedPriorSupport',
    'AvailableChain.FGSA.Run.RetainedH6Frame',
    'AvailableChain.FGSA.Run.RetainedH6Input',
    'AvailableChain.FGSA.Run.fgsa_retainedReads_H6',
    'AvailableChain.FGSA.Run.fgsa_retainedReads_H6S',
    # S4.3b W kernels and FF5–FF7: --expect DATA only.
    'AvailableChain.FGSA.Run.KernelJoinedPrem.window',
    'AvailableChain.FGSA.Run.FinFormW',
    'AvailableChain.FGSA.Run.FinFormW.recFE',
    'AvailableChain.FGSA.Run.FinFormW.recF4',
    'AvailableChain.FGSA.Run.FinFormW.rec',
    'AvailableChain.FGSA.Run.FinFormW.recOn',
    'AvailableChain.FGSA.Run.FinFormW.casesOn',
    'AvailableChain.FGSA.Run.FinFormW.holdsW',
    'AvailableChain.FGSA.Run.FinFormW.holdsW_def',
    'AvailableChain.FGSA.Run.FinalitySet_W',
    'AvailableChain.FGSA.Run.FinalitySet_W.mk',
    'AvailableChain.FGSA.Run.FinalitySet_W.core',
    'AvailableChain.FGSA.Run.FinalitySet_W.bound',
    'AvailableChain.FGSA.Run.FinalitySet_W.recur',
    'AvailableChain.FGSA.Run.OpeningCarrier_W',
    'AvailableChain.FGSA.Run.OpeningCarrier_W_def',
    'AvailableChain.FGSA.Run.KernelConclusion_W',
    'AvailableChain.FGSA.Run.KernelConclusion_W_def',
    'AvailableChain.FGSA.Run.KernelPrem_W',
    'AvailableChain.FGSA.Run.KernelPrem_W.mk',
    'AvailableChain.FGSA.Run.KernelPrem_W.set',
    'AvailableChain.FGSA.Run.KernelPrem_W.bound',
    'AvailableChain.FGSA.Run.KernelPrem_W.window',
    'AvailableChain.FGSA.Run.KernelPrem_W.start',
    'AvailableChain.FGSA.Run.KernelPrem_W.hhor',
    'AvailableChain.FGSA.Run.KernelPrem_W.input',
    'AvailableChain.FGSA.Run.KernelPrem_W.services',
    'AvailableChain.FGSA.Run.TailKernelPt',
    'AvailableChain.FGSA.Run.TailKernelPt.mk',
    'AvailableChain.FGSA.Run.TailKernelPt.w',
    'AvailableChain.FGSA.Run.TailKernelPt.r',
    'AvailableChain.FGSA.Run.TailKernelPt.carrier',
    'AvailableChain.FGSA.Run.TailKernelPt.U',
    'AvailableChain.FGSA.Run.TailKernelPrem_W',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.mk',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.set',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.bound',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.input',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.start',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.window',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.carrier',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.high',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.cover',
    'AvailableChain.FGSA.Run.TailKernelPrem_W.hhor',
    'AvailableChain.FGSA.Run.finalityWindow_W',
    'AvailableChain.FGSA.Run.finalityWindow_W_def',
    'AvailableChain.FGSA.Run.FirstFinalityPrem_W',
    'AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk',
    'AvailableChain.FGSA.Run.FirstFinalityPrem_W.set',
    'AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem_W',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W.set',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W.input',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W.start',
    'AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W.set',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W.input',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W.start',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon',
    'AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor',
    'AvailableChain.FGSA.Run.FinalityKernelClaim_W',
    'AvailableChain.FGSA.Run.KernelACSideClaim_W',
    'AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W',
    'AvailableChain.FGSA.Run.TailKernelClaim_W',
    'AvailableChain.FGSA.Run.FinalityLivenessConcl_W',
    'AvailableChain.FGSA.Run.FirstFinalityConcl_W',
    'AvailableChain.FGSA.Run.ProposalFinalConcl_W',
    'AvailableChain.FGSA.Run.AboveFrontierConcl_W',
    'AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W',
    'AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W',
    'AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W',
    'AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W',
    'AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W',
    'AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W',
    'AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W',
    'AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W',
    'AvailableChain.FGSA.Run.fgsa_headRead_block_slots',
    'AvailableChain.FGSA.Run.fgsa_headRead_child_slot',
    'AvailableChain.FGSA.Run.fgsa_exactHeadGeometry_of_retained_endpoint',
    'AvailableChain.FGSA.Run.fgsa_headVote_covers_parent_of_retained_geometry',
    'AvailableChain.FGSA.Run.fgsa_retainedEndpoint_geometry_on_run',
    'AvailableChain.FGSA.Run.RetainedExactHeadRunGeometry',
    'AvailableChain.FGSA.Run.fgsa_retainedExactHead_geometry_on_run',
    'AvailableChain.FGSA.Run.fgsa_retained_source_stop',
    'AvailableChain.FGSA.Run.exactService_head_of_retained_proposal',
    'AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_clean',
    'AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_recovery',
    'AvailableChain.FGSA.Run.fgsa_domainR_eq_storeFrameView',
    'AvailableChain.FGSA.Run.fgsa_walk_domain_of_witness_view',
    'AvailableChain.FGSA.Run.fgsa_score_geometry_of_retained_cuts',
    'AvailableChain.FGSA.Run.fgsa_retained_path_mem',
    'AvailableChain.FGSA.Run.fgsa_retained_proposal_mem',
    'AvailableChain.FGSA.Run.fgsa_retained_persists_of_path',
    'AvailableChain.FGSA.Run.fgsa_retained_proposal_mem_on_run',
    'AvailableChain.FGSA.Run.fgsa_retained_path_persists_on_run',
    'AvailableChain.FGSA.Run.fgsa_retainedWalk_geometry_on_run',
    'AvailableChain.FGSA.Run.retainedBand_def',
    'AvailableChain.FGSA.Run.ReflectedDomainWitness_def',
    'AvailableChain.FGSA.Run.retainedBand',
    'AvailableChain.FGSA.Run.ReflectedDomainWitness',
    'AvailableChain.FGSA.Run.RetainedReadPremises',
    'AvailableChain.FGSA.Run.fgsa_domain_witness_of_mem',
    'AvailableChain.FGSA.Run.fgsa_walkRun_full_domain_view',
    'AvailableChain.FGSA.Run.fgsa_walkRun_path_domain_view',
    'AvailableChain.FGSA.Run.fgsa_walkRun_eligible_iff_view',
    'AvailableChain.FGSA.Run.fgsa_eligible_eq_of_retainedBand_score',
    'AvailableChain.FGSA.Run.fgsa_walkRun_reflected_old_child',
    'AvailableChain.FGSA.Run.fgsa_retained_old_child_reflects_on_run',
    'AvailableChain.FGSA.Run.fgsa_eligible_eq_of_same_floor',
    'AvailableChain.FGSA.Run.fgsa_eligible_eq_of_parent_height',
    'AvailableChain.FGSA.Run.fgsa_score_geometry_of_domains',
    'AvailableChain.FGSA.Run.fgsa_score_eq_on_candidates_on_run',
    'AvailableChain.FGSA.Run.fgsa_retained_scores_of_candidates',
    'AvailableChain.FGSA.Run.RetainedWalkRunGeometry',
    'AvailableChain.FGSA.Run.RetainedEndpointGeometry',
    'AvailableChain.FGSA.Run.fgsa_retained_prefix_of_trunk_or_support',
    'AvailableChain.FGSA.Run.fgsa_walk_domain_of_witness',
    # J7 W row permission and SO-COV producers.
    'AvailableChain.FGSA.Run.openingCovered_frontier_gate',
    'AvailableChain.FGSA.Run.openingCovered_lower_gate',
    'AvailableChain.FGSA.Run.rowPermission_own_lock',
    'AvailableChain.FGSA.Run.rowPermission_pair',
    'AvailableChain.FGSA.Run.rowPermission_covered',
    'AvailableChain.FGSA.Run.rowPermission_at',

    # S4.2b: terminal retention contract (F8-W).
    'AvailableChain.FGSA.Run.TerminalRetention_W',
    'AvailableChain.FGSA.Run.TerminalRetention_W_def',
    # S4.3 W surface: --expect DATA only.
    'AvailableChain.FGSA.Run.FinalityCoveredByChild_W',
    'AvailableChain.FGSA.Run.FinRowNames',
    'AvailableChain.FGSA.Run.FinalityNames',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.base',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.after',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered',
    'AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch',
    'AvailableChain.FGSA.Run.FinalityBatchCoverage_W',
    'AvailableChain.FGSA.Run.PendingFold_W',
    'AvailableChain.FGSA.Run.PendingFold_W.mk',
    'AvailableChain.FGSA.Run.PendingFold_W.child',
    'AvailableChain.FGSA.Run.PendingFold_W.cover',
    'AvailableChain.FGSA.Run.FinalityCoveredByChild_W_def',
    'AvailableChain.FGSA.Run.FinRowNames_def',
    'AvailableChain.FGSA.Run.FinalityNames_def',
    'AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def',
    'AvailableChain.FGSA.Run.FreshFinalityRows_W',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry',
    'AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt',
    'AvailableChain.FGSA.Run.TerminalCarriage_W',
    'AvailableChain.FGSA.Run.FreshFinalityRows_W_def',
    'AvailableChain.FGSA.Run.TerminalCarriage_W_def',
    'AvailableChain.FGSA.Run.JustifyAt',
    'AvailableChain.FGSA.Run.JustifyFresh_W',
    'AvailableChain.FGSA.Run.Ready_W',
    'AvailableChain.FGSA.Run.receiptInsert_W',
    'AvailableChain.FGSA.Run.ReceiptWitness_W',
    'AvailableChain.FGSA.Run.ReceiptWitness_W.mk',
    'AvailableChain.FGSA.Run.ReceiptWitness_W.index',
    'AvailableChain.FGSA.Run.ReceiptWitness_W.time',
    'AvailableChain.FGSA.Run.BlockDelivery_W',
    'AvailableChain.FGSA.Run.BlockDelivery_W.mk',
    'AvailableChain.FGSA.Run.BlockDelivery_W.selected',
    'AvailableChain.FGSA.Run.BlockDelivery_W.witness',
    'AvailableChain.FGSA.Run.AcceptGuards_W',
    'AvailableChain.FGSA.Run.AcceptGuards_W.mk',
    'AvailableChain.FGSA.Run.AcceptGuards_W.finCmp',
    'AvailableChain.FGSA.Run.AcceptGuards_W.jPath',
    'AvailableChain.FGSA.Run.AcceptGuards_W.cap',
    'AvailableChain.FGSA.Run.AcceptPrem_W',
    'AvailableChain.FGSA.Run.AcceptPrem_W.mk',
    'AvailableChain.FGSA.Run.AcceptPrem_W.base',
    'AvailableChain.FGSA.Run.AcceptPrem_W.faultBound',
    'AvailableChain.FGSA.Run.AcceptPrem_W.finalized',
    'AvailableChain.FGSA.Run.AcceptPrem_W.deliver',
    'AvailableChain.FGSA.Run.AcceptPrem_W.guards',
    'AvailableChain.FGSA.Run.AcceptPrem_W.horizon',
    'AvailableChain.FGSA.Run.AcceptBefore_W',
    'AvailableChain.FGSA.Run.FinalizePrem_W',
    'AvailableChain.FGSA.Run.FinalizePrem_W.mk',
    'AvailableChain.FGSA.Run.FinalizePrem_W.fold',
    'AvailableChain.FGSA.Run.FinalizePrem_W.base',
    'AvailableChain.FGSA.Run.FinalizePrem_W.faultBound',
    'AvailableChain.FGSA.Run.FinalizePrem_W.deliver',
    'AvailableChain.FGSA.Run.FinalizePrem_W.guards',
    'AvailableChain.FGSA.Run.FinalizePrem_W.horizon',
    'AvailableChain.FGSA.Run.FinalizePending_W',
    'AvailableChain.FGSA.Run.JustifyAt_def',
    'AvailableChain.FGSA.Run.JustifyFresh_W_def',
    'AvailableChain.FGSA.Run.Ready_W_def',
    'AvailableChain.FGSA.Run.receiptInsert_W_def',
    'AvailableChain.FGSA.Run.AcceptBefore_W_def',
    'AvailableChain.FGSA.Run.FinalizePending_W_def',
    'AvailableChain.FGSA.Run.JustifiedCross_def',
    'AvailableChain.FGSA.Run.MixedCross_def',
    'AvailableChain.FGSA.Run.foldTrichotomy_def',
    'AvailableChain.FGSA.Run.StoredProgressConsume_def',
    'AvailableChain.FGSA.Run.pendingFold_consume_W',
    'AvailableChain.FGSA.Run.covered_parent_W',
    'AvailableChain.FGSA.Run.finalityBatch_covered_W',
    'AvailableChain.FGSA.Run.finalizePending_of_acceptBefore_W',
    'AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂',
    'AvailableChain.FGSA.Run.AgreesThrough₂',
    'AvailableChain.FGSA.Run.CleanContinuation₂',
    'AvailableChain.FGSA.Run.BoundedHealingCut₂',
    'AvailableChain.FGSA.Run.SSafeFromCut₂',
    'AvailableChain.FGSA.Run.BoundedSafetyRecovery₂',
    'AvailableChain.FGSA.Run.WeakContinuationClaim',
    # S4.4a: row-delay liveness binding and actual-event finite horizon.
    'AvailableChain.FGSA.Run.HealingPrem.bound',
    'AvailableChain.FGSA.Run.KernelJoinedPrem.bound',
    'AvailableChain.FGSA.Run.HealingAttemptPrem.hhor',
    'AvailableChain.FGSA.Run.FE_W',
    'AvailableChain.FGSA.Run.F4_W',
    'AvailableChain.FGSA.Run.FGoodE_Wp',
    'AvailableChain.FGSA.Run.FGood4_Wp',
    'AvailableChain.FGSA.Run.Tail_Wp',
    'AvailableChain.FGSA.Run.B_FW',
    'AvailableChain.FGSA.Run.FE_W_def',
    'AvailableChain.FGSA.Run.F4_W_def',
    'AvailableChain.FGSA.Run.FGoodE_Wp_def',
    'AvailableChain.FGSA.Run.FGood4_Wp_def',
    'AvailableChain.FGSA.Run.Tail_Wp_def',
    'AvailableChain.FGSA.Run.B_FW_def',
    # S4.2b: the named terminal-retention contract is proved.
    'AvailableChain.FGSA.Run.fgsa_terminalRetentionW',
    # S4.5: UniformHealing corollary (B9) and the shared HEAD tick index (B8).
    'AvailableChain.FGSA.Run.uniformHealing_of_hTimeConcl',
    'AvailableChain.FGSA.Run.fgsa_tickIdx_of_event',
    'AvailableChain.FGSA.Run.fgsa_grid_carrier_timeW',
    'AvailableChain.FGSA.Run.fgsa_grid_kernel_deadlineW',
    'AvailableChain.FGSA.Run.F4_W_implies_FE_W',
    'AvailableChain.FGSA.Run.betaF_eq_eight_delta',
    'AvailableChain.FGSA.Run.epsF_eq_zero',
    'AvailableChain.FGSA.Run.carrierTimeW_eq_carrierTime2',
    'AvailableChain.FGSA.Run.kernelDeadlineW_eq_kernelDeadline',
    'AvailableChain.FGSA.Run.W_W_eq_W_F',
    'AvailableChain.FGSA.Run.B_HF_eq_B_H',
    'AvailableChain.FGSA.Run.B_HF_numeric_295',
    'AvailableChain.FGSA.Run.B_HF_numeric_343',
    # S4.1 W bounds: definitions, equations, and pure arithmetic.
    'AvailableChain.FGSA.Run.kappaF',
    'AvailableChain.FGSA.Run.betaF',
    'AvailableChain.FGSA.Run.epsF',
    'AvailableChain.FGSA.Run.carrierTimeW',
    'AvailableChain.FGSA.Run.kernelDeadlineW',
    'AvailableChain.FGSA.Run.W_W',
    'AvailableChain.FGSA.Run.E_gF',
    'AvailableChain.FGSA.Run.E_jF',
    'AvailableChain.FGSA.Run.B_cF',
    'AvailableChain.FGSA.Run.D_cF',
    'AvailableChain.FGSA.Run.B_resetF',
    'AvailableChain.FGSA.Run.BF',
    'AvailableChain.FGSA.Run.B_H2F',
    'AvailableChain.FGSA.Run.B_H1F',
    'AvailableChain.FGSA.Run.B_HF',
    'AvailableChain.FGSA.Run.B\'_resetF',
    'AvailableChain.FGSA.Run.B_bestF',
    'AvailableChain.FGSA.Run.ActionDeliveryBoundsW',
    'AvailableChain.FGSA.Run.KernelBeforeNextActionW',
    'AvailableChain.FGSA.Run.LivenessBoundW',
    'AvailableChain.FGSA.Run.kappaF_def',
    'AvailableChain.FGSA.Run.betaF_def',
    'AvailableChain.FGSA.Run.epsF_def',
    'AvailableChain.FGSA.Run.carrierTimeW_def',
    'AvailableChain.FGSA.Run.kernelDeadlineW_def',
    'AvailableChain.FGSA.Run.W_W_def',
    'AvailableChain.FGSA.Run.E_gF_def',
    'AvailableChain.FGSA.Run.E_jF_def',
    'AvailableChain.FGSA.Run.B_cF_def',
    'AvailableChain.FGSA.Run.D_cF_def',
    'AvailableChain.FGSA.Run.B_resetF_def',
    'AvailableChain.FGSA.Run.BF_def',
    'AvailableChain.FGSA.Run.B_H2F_def',
    'AvailableChain.FGSA.Run.B_H1F_def',
    'AvailableChain.FGSA.Run.B_HF_def',
    'AvailableChain.FGSA.Run.B\'_resetF_def',
    'AvailableChain.FGSA.Run.B_bestF_def',
    'AvailableChain.FGSA.Run.ActionDeliveryBoundsW_def',
    'AvailableChain.FGSA.Run.KernelBeforeNextActionW_def',
    'AvailableChain.FGSA.Run.kappaF_ceiling',
    'AvailableChain.FGSA.Run.kappaF_ge_two',
    'AvailableChain.FGSA.Run.kappaF_eq_two_iff',
    'AvailableChain.FGSA.Run.betaF_bounds',
    'AvailableChain.FGSA.Run.betaF_le_period',
    'AvailableChain.FGSA.Run.epsF_nonneg',
    'AvailableChain.FGSA.Run.epsF_bounds',
    'AvailableChain.FGSA.Run.actionTime_periodW',
    'AvailableChain.FGSA.Run.action_delivery_boundsW',
    'AvailableChain.FGSA.Run.kernel_before_next_actionW',
    'AvailableChain.FGSA.Run.E_gF_eq',
    'AvailableChain.FGSA.Run.B_cF_eq',
    'AvailableChain.FGSA.Run.E_jF_bounds',
    'AvailableChain.FGSA.Run.BF_bounds',
    'AvailableChain.FGSA.Run.B_HF_bounds',
    'AvailableChain.FGSA.Run.B_bestF_le_healing',
    'AvailableChain.FGSA.Run.BF_max',
    'AvailableChain.FGSA.Run.resetF_healing_eq',
    'AvailableChain.FGSA.Run.B_HF_numeric_351',
    # fgsa-f1b4b producer line (main 73d0ea7): ScoreRun, GateReceipt, ExactService, ExactHead, regime wrappers.
    'AvailableChain.FGSA.Run.ScoreRunGeometry',
    'AvailableChain.FGSA.Run.fgsa_score_eq_on_run',
    'AvailableChain.FGSA.Run.WalkRunGeometry',
    'AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_run',
    'AvailableChain.FGSA.Run.GateReceiptGeometry',
    'AvailableChain.FGSA.Run.fgsa_gateReceipt',
    'AvailableChain.FGSA.Run.ExactServiceGateGeometry',
    'AvailableChain.FGSA.Run.exactService_gate_of_head',
    'AvailableChain.FGSA.Run.exactService_of_head_and_gate',
    'AvailableChain.FGSA.Run.exactService_participation_of_card',
    'AvailableChain.FGSA.Run.ExactHeadGeometry',
    'AvailableChain.FGSA.Run.ExactHeadRunGeometry',
    'AvailableChain.FGSA.Run.fgsa_headVote_best_ancestry_of_cover',
    'AvailableChain.FGSA.Run.fgsa_headVote_exact_of_covered_parent',
    'AvailableChain.FGSA.Run.exactHead_of_proposal_on_run',
    'AvailableChain.FGSA.Run.exactService_head_of_proposal',
    'AvailableChain.FGSA.Run.fgsa_score_eq_on_clean',
    'AvailableChain.FGSA.Run.fgsa_score_eq_on_recovery',
    'AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_clean',
    'AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_recovery',
    'AvailableChain.FGSA.Run.fgsa_gateReceipt_clean',
    'AvailableChain.FGSA.Run.fgsa_gateReceipt_recovery',
    'AvailableChain.FGSA.Run.exactService_of_head_clean',
    'AvailableChain.FGSA.Run.exactService_of_head_recovery',
    'AvailableChain.FGSA.Run.exactService_head_of_proposal_clean',
    'AvailableChain.FGSA.Run.exactService_head_of_proposal_recovery',
    # fgsa-f1b8 step 3 (main b83d8f3): unconditional safety and its exact-head chain.
    'AvailableChain.FGSA.Run.fgsaSafetyClaims',
    'AvailableChain.FGSA.Run.fgsaClaims_of_open',
    'AvailableChain.FGSA.Run.fgsaClaims_of_hTime',
    'AvailableChain.FGSA.Run.fgsa_headReachesLoClaim',
    'AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry',
    'AvailableChain.FGSA.Run.exactHead_of_pivot',
    'AvailableChain.FGSA.Run.kept_or_conflict',
    'AvailableChain.FGSA.Run.kept_or_cause',
    'AvailableChain.FGSA.Run.fgsa_domain_anchorClosed_mono',
    'AvailableChain.FGSA.Run.openingSource_firstOpening',
    'AvailableChain.FGSA.Run.openingSource_firstOpening_exact',
    'AvailableChain.FGSA.Run.openingSource_exact_of_gateService',
    'AvailableChain.FGSA.Run.openingSource_candidate_of_gateService',
    'AvailableChain.FGSA.Run.openingSource_domain_of_kept_or_cause',
    'AvailableChain.FGSA.Run.fgsa_headReachesLo',
    'AvailableChain.FGSA.Run.fgsaSafetyClaims_of_headReachesLo',
    'AvailableChain.FGSA.Run.openingSource_eq_of_no_strict_extension',
    'AvailableChain.FGSA.Run.FGFinalizedAt',
    'AvailableChain.FGSA.Run.FinalityRunBlock',
    'AvailableChain.FGSA.Run.finalityStoreRows',
    'AvailableChain.FGSA.Run.FinalityCarriage',
    'AvailableChain.FGSA.Run.fgsa_pureAccountable',
    'AvailableChain.FGSA.Run.fgsa_pureAgreement',
    'AvailableChain.FGSA.Run.FGWholeRunAccountable',
    'AvailableChain.FGSA.Run.fgsa_wholeRunAccountable',
    'AvailableChain.FGSA.Run.FGSASlashableBound',
    'AvailableChain.FGSA.Run.fgsa_wholeRunAgreement',
    'AvailableChain.FGSA.Run.fgsa_eventPrefixAgreement',
    'AvailableChain.FGSA.Run.fgsa_storeSlashableBound_of_faults',
    'AvailableChain.FGSA.Run.fgsa_slashableBound_of_faults',
    'AvailableChain.FGSA.Run.fgsa_finalLock_faulty_count',
    'AvailableChain.FGSA.Run.fgsa_accountable_base',
    'AvailableChain.FGSA.Run.fgsa_unforgeable_of_base',
    'AvailableChain.FGSA.Run.held_chain_row_origin_delivery',
    'AvailableChain.FGSA.Run.held_chain_row_origin_before',
    'AvailableChain.FGSA.Run.fgsa_outputNestingAt',
    'AvailableChain.FGSA.Run.fgsa_outputNestingClaim',
    'AvailableChain.FGSA.Run.fgsa_tSrc',
    'AvailableChain.FGSA.Run.fgsa_labelBound',
    'AvailableChain.FGSA.Run.fgsa_timingContract',
    'AvailableChain.FGSA.Run.clean_gate_sOrigin',
    'AvailableChain.FGSA.Run.clean_gate_fastWrite',

    'AvailableChain.FGSA.Run.clean_gate_fastAt',
    'AvailableChain.FGSA.Run.cleanResults_eq_of_noGate',
    'AvailableChain.FGSA.Run.cleanHist_step_of_noGate',
    'AvailableChain.FGSA.Run.cleanHist_step_delivery',
    'AvailableChain.FGSA.Run.cleanHist_step_noGateTick',
    'AvailableChain.FGSA.Run.clean_delivery_fields',
    'AvailableChain.FGSA.Run.clean_block_reconcile',
    'AvailableChain.FGSA.Run.clean_noGate_fields',
    'AvailableChain.FGSA.Run.cleanState_index_facts',
    'AvailableChain.FGSA.Run.clean_gate_raw',
    'AvailableChain.FGSA.Run.clean_gate_store',
    'AvailableChain.FGSA.Run.clean_state_gate_guard',
    'AvailableChain.FGSA.Run.clean_gate_passed',
    'AvailableChain.FGSA.Run.clean_gate_writes',
    'AvailableChain.FGSA.Run.clean_gate_lease_targets',
    'AvailableChain.FGSA.Run.clean_gate_fast_prefix',
    'AvailableChain.FGSA.Run.clean_gate_output_compatible',
    'AvailableChain.FGSA.Run.clean_gate_sExtends',
    'AvailableChain.FGSA.Run.clean_gate_leases',
    'AvailableChain.FGSA.Run.clean_gate_saved',
    'AvailableChain.FGSA.Run.clean_gate_savedOnly',

    'AvailableChain.FGSA.Run.fgsa_fgFoundationClaim',
    'AvailableChain.FGSA.Run.fgsa_leaseOrigins_writeLabel',
    'AvailableChain.FGSA.Run.fgsa_leaseOrigins_lastWrite',
    'AvailableChain.FGSA.Run.fgsa_leaseOrigins_origins',
    'AvailableChain.FGSA.Run.fgsa_leaseOriginsAt',
    'AvailableChain.FGSA.Run.fgsa_leaseOriginsClaim',
    'AvailableChain.FGSA.Run.fgsa_sourceDisciplineBaseClaim',
    'AvailableChain.FGSA.Run.fgsa_sourceDisciplineClaim',
    'AvailableChain.FGSA.Run.fgsa_srcFrameAboveClaim',
    'AvailableChain.FGSA.Run.fgsa_faultX_count_rec',
    'AvailableChain.FGSA.Run.fgsa_faultQ_of_count',
    'AvailableChain.FGSA.Run.fgsa_target_exact_quorum',
    'AvailableChain.FGSA.Run.Recovery₂.faultX_count_rec',
    'AvailableChain.FGSA.Run.Recovery₂.faultQ',
    # F1 lane Foundations public declarations (f1-dfix-full.md:119–137).
    'AvailableChain.FGSA.Run.fgsa_finalityStoreRows_contains',
    'AvailableChain.FGSA.Run.FGSASlashableBound_def',
    'AvailableChain.FGSA.Run.fgsa_eventPrefixAgreement_of_bound',
    'AvailableChain.FGSA.Run.fgsa_storeSlashableBound_of_base',
    'AvailableChain.FGSA.Run.carried_rows_carriage',
    'AvailableChain.FGSA.Run.delivered_runBlock_carriage',
    'AvailableChain.FGSA.Run.proposalRows_source',
    'AvailableChain.FGSA.Run.store_wire_origin',
    'AvailableChain.FGSA.Run.emitted_runBlock_carriage',
    'AvailableChain.FGSA.Run.fgsa_runBlock_carriage',
    'AvailableChain.FGSA.Run.fgsa_slashableBound_of_base',
    'AvailableChain.FGSA.Run.stored_block_wire_delivery',
    'AvailableChain.FGSA.Run.stored_chain_row_origin_delivery',
    'AvailableChain.FGSA.Run.fgsa_finalLock_of_bound',
    'AvailableChain.FGSA.Run.fgsa_finalizedMonotone',

    'AvailableChain.FGSA.Run.fgsa_rCap',
    'AvailableChain.FGSA.Run.fgsa_finalityCap',
    'AvailableChain.FGSA.Run.fgsa_rCap_time',
    'AvailableChain.FGSA.Run.fgsa_rCap_before',
    'AvailableChain.FGSA.Run.fgsa_finalityLag',
    'AvailableChain.FGSA.Run.fgsa_leaseOrigins_chain',
    'AvailableChain.FGSA.Run.fgsa_leaseOrigins_ancestorDeadlines',
    'AvailableChain.FGSA.Run.fgsa_leaseOrigins_fastWrites',
    'AvailableChain.FGSA.Run.cleanResults_mono',
    'AvailableChain.FGSA.Run.belowLabel_mono_index',
    'AvailableChain.FGSA.Run.belowLabel_mono_label',
    'AvailableChain.FGSA.Run.belowLabel_of_preceq',
    'AvailableChain.FGSA.Run.belowLabel_genesis',
    'AvailableChain.FGSA.Run.belowLabel_of_mem',
    'AvailableChain.FGSA.Run.belowLabel_of_gateResultAt',
    'AvailableChain.FGSA.Run.cleanHist_restrict',
    'AvailableChain.FGSA.Run.cleanHist_results_compatible',
    'AvailableChain.FGSA.Run.cleanHist_belowLabel_compatible',
    'AvailableChain.FGSA.Run.cleanHist_belowLabel_preceq_result',
    'AvailableChain.FGSA.Run.cleanHist_zero',
    'AvailableChain.FGSA.Run.cleanResults_mem_succ_iff',
    'AvailableChain.FGSA.Run.HealAC.tsMono',
    'AvailableChain.FGSA.Run.HealAC.tExact',
    'AvailableChain.FGSA.Run.H2A',
    'AvailableChain.FGSA.Run.H2Prime',
    'AvailableChain.FGSA.Run.H3',
    'AvailableChain.FGSA.Run.H4',
    'AvailableChain.FGSA.Run.H5RawTransfer',
    'AvailableChain.FGSA.Run.H6GateService',
    'AvailableChain.FGSA.Run.HealT',
    'AvailableChain.FGSA.Run.HealAC',
    'AvailableChain.FGSA.Run.HealingInput',
    'AvailableChain.FGSA.Run.HTimeStatement',
    'AvailableChain.FGSA.Run.HTimeStatement_def',
    'AvailableChain.FGSA.Run.TStart',
    'AvailableChain.FGSA.Run.FullVoteService',
    'AvailableChain.FGSA.Run.TVote',
    'AvailableChain.FGSA.Run.WalkBatch',
    'AvailableChain.FGSA.Run.TWalk',
    'AvailableChain.FGSA.Run.CoreServices',
    'AvailableChain.FGSA.Run.PhaseKind',
    'AvailableChain.FGSA.Run.AttemptTask',
    'AvailableChain.FGSA.Run.AttemptKey',
    'AvailableChain.FGSA.Run.ResetArrivalStatement',
    'AvailableChain.FGSA.Run.ResetArrivalStatement_def',
    'AvailableChain.FGSA.Run.ResetArrivalFullStatement',
    'AvailableChain.FGSA.Run.ResetArrivalFullStatement_def',
    'AvailableChain.FGSA.Run.KernelPt',
    'AvailableChain.FGSA.Run.kernelStart',
    'AvailableChain.FGSA.Run.HealTContract',
    'AvailableChain.FGSA.Run.frontierAtIdx',
    'AvailableChain.FGSA.Run.TopEvidence',
    'AvailableChain.FGSA.Run.ContestEvidence',
    'AvailableChain.FGSA.Run.EffectiveEvent',
    'AvailableChain.FGSA.Run.AttemptPhaseAt',
    'AvailableChain.FGSA.Run.ServedFrontier',
    'AvailableChain.FGSA.Run.AttemptValid',
    'AvailableChain.FGSA.Run.attemptBudget',
    'AvailableChain.FGSA.Run.AttemptEndsBy',
    'AvailableChain.FGSA.Run.rowHeld',
    'AvailableChain.FGSA.Run.proposalStateAt',
    'AvailableChain.FGSA.Run.heldAtProposal',
    'AvailableChain.FGSA.Run.onParentChain',
    'AvailableChain.FGSA.Run.HeldBefore',
    'AvailableChain.FGSA.Run.ValidForParent',
    'AvailableChain.FGSA.Run.ValidForParent_def',
    'AvailableChain.FGSA.Run.headAtLabel',
    'AvailableChain.FGSA.Run.RXing',
    'AvailableChain.FGSA.Run.RCap',
    'AvailableChain.FGSA.Run.THigh',
    'AvailableChain.FGSA.Run.TCarrier',
    'AvailableChain.FGSA.Run.TRowsSelect',
    'AvailableChain.FGSA.Run.TRowsSync',
    'AvailableChain.FGSA.Run.TRows',
    'AvailableChain.FGSA.Run.SourceBefore',
    'AvailableChain.FGSA.Run.Kept',
    'AvailableChain.FGSA.Run.KeepOrCause',
    'AvailableChain.FGSA.Run.RExcl',
    'AvailableChain.FGSA.Run.RKeep',
    'AvailableChain.FGSA.Run.RFProv',
    'AvailableChain.FGSA.Run.TDel',
    'AvailableChain.FGSA.Run.TDelReset',
    'AvailableChain.FGSA.Run.TGeom',
    'AvailableChain.FGSA.Run.ExactService',
    'AvailableChain.FGSA.Run.PhaseInterval',
    'AvailableChain.FGSA.Run.Transfers',
    'AvailableChain.FGSA.Run.PhaseBody',
    'AvailableChain.FGSA.Run.TPerm',
    'AvailableChain.FGSA.Run.ProposalGap',
    'AvailableChain.FGSA.Run.RepairAfter',
    'AvailableChain.FGSA.Run.TRepair',
    'AvailableChain.FGSA.Run.OpeningEntry',
    'AvailableChain.FGSA.Run.TCommon',
    'AvailableChain.FGSA.Run.TFrontier',
    'AvailableChain.FGSA.Run.oldRowHeights',
    'AvailableChain.FGSA.Run.muOf',
    'AvailableChain.FGSA.Run.high',
    'AvailableChain.FGSA.Run.honestFrontier',
    'AvailableChain.FGSA.Run.HeightRow',
    'AvailableChain.FGSA.Run.H0Reset',
    'AvailableChain.FGSA.Run.H0',
    'AvailableChain.FGSA.Run.tstarOf',
    'AvailableChain.FGSA.Run.PtU',
    'AvailableChain.FGSA.Run.PtW',
    'AvailableChain.FGSA.Run.PtM',
    'AvailableChain.FGSA.Run.PtR',
    'AvailableChain.FGSA.Run.PtK',
    'AvailableChain.FGSA.Run.HealingPrem',
    'AvailableChain.FGSA.Run.HealingWitnessPrem',
    'AvailableChain.FGSA.Run.HealingTimePrem',
    'AvailableChain.FGSA.Run.ResetArrivalPrem',
    'AvailableChain.FGSA.Run.ResetArrivalFullPrem',
    'AvailableChain.FGSA.Run.KernelJoinedPrem',
    'AvailableChain.FGSA.Run.HealingAttemptPrem',
    'AvailableChain.FGSA.Run.muOf_spec',
    'AvailableChain.FGSA.Run.H0.time_unique',
    'AvailableChain.FGSA.Run.H0.tstar_eq',
    'AvailableChain.FGSA.Run.HealingWitness',
    'AvailableChain.FGSA.Run.tstar',
    'AvailableChain.FGSA.Run.healStart',
    'AvailableChain.FGSA.Run.HealSuffix',
    'AvailableChain.FGSA.Run.Healed',
    'AvailableChain.FGSA.Run.healed_same_time',
    'AvailableChain.FGSA.Run.healed_mono_start',

    'AvailableChain.FGSA.Run.CleanState.gateInputs',
    'AvailableChain.FGSA.Run.CleanGateOutputStmt',
    'AvailableChain.FGSA.Run.CleanActionSourcesStmt',
    'AvailableChain.FGSA.Run.CleanFrameStmt',
    'AvailableChain.FGSA.Run.fgsa_storedTargetsBelowOutput',
    'AvailableChain.FGSA.Run.fgsa_rRec',
    'AvailableChain.FGSA.Run.fgsa_reconcileAt',
    'AvailableChain.FGSA.Run.fgsa_reconcileClaim',
    'AvailableChain.FGSA.Run.fgsa_slashable_faulty_count',
    'AvailableChain.FGSA.Run.fgsa_accountable',
    'AvailableChain.FGSA.Run.fgsa_finalLock_ev',
    'AvailableChain.FGSA.Run.fgsa_finalizedSafety',
    'AvailableChain.FGSA.Run.fgsa_finalLock',
    'AvailableChain.FGSA.Run.fgsa_finalLock_erased',
    'AvailableChain.FGSA.Run.fgsa_carrier_geometry',
    'AvailableChain.FGSA.Run.fgsa_carrierAt',
    'AvailableChain.FGSA.Run.fgsa_carrierClaim',
    'AvailableChain.FGSA.Run.held_chain_row_origin',
    'AvailableChain.FGSA.Run.fgsa_clientSafeAll',
    'AvailableChain.FGSA.Run.readAt_chain_row_origin',
    'AvailableChain.FGSA.Run.fgsa_honestNeverSlashed',
    'AvailableChain.FGSA.Run.fgsa_clientSafetyClaim',
    'AvailableChain.FGSA.Run.fgsa_clientSafetyBaseClaim',
    'AvailableChain.FGSA.Run.honest_at_most_one_row_per_action',
    'AvailableChain.FGSA.Run.honest_row_of_attest_some',
    'AvailableChain.FGSA.Run.honest_emit_unique',
    'AvailableChain.FGSA.Run.fgsa_rStore',
    'AvailableChain.FGSA.Run.fgsa_store_cumulative',
    'AvailableChain.FGSA.Run.fgsa_rStoreCumul',
    'AvailableChain.FGSA.Run.fgsa_rMono',
    'AvailableChain.FGSA.Run.fgsa_storeAt',
    'AvailableChain.FGSA.Run.fgsa_storeClaim',
    'AvailableChain.FGSA.Run.fgsa_rFrameExact',
    'AvailableChain.FGSA.Run.fgsa_rActive',
    'AvailableChain.FGSA.Run.fgsa_activeViewAt',
    'AvailableChain.FGSA.Run.fgsa_activeViewClaim',
    'AvailableChain.FGSA.Run.fgsa_rCarrierView',
    'AvailableChain.FGSA.Run.fgsa_rFrame',
    'AvailableChain.FGSA.Run.fgsa_frameAt',
    'AvailableChain.FGSA.Run.fgsa_frameClaim',
    'AvailableChain.FGSA.Run.fgsa_seed_stored',
    'AvailableChain.FGSA.Run.fgsa_seed_bounds',
    'AvailableChain.FGSA.Run.fgsa_rGeo',
    'AvailableChain.FGSA.Run.fgsa_rCert',
    'AvailableChain.FGSA.Run.fgsa_chainCertificatesAt',
    'AvailableChain.FGSA.Run.fgsa_chainCertificatesClaim',
    'AvailableChain.FGSA.Run.sourceDiscipline_qcOrigin',
    'AvailableChain.FGSA.Run.sourceDiscipline_strat',
    'AvailableChain.FGSA.Run.sourceDiscipline_at',
    'AvailableChain.FGSA.Run.sourceDiscipline_srcFrameAbove',

    'AvailableChain.FGSA.Run.sourceDiscipline_tSrc',
    'AvailableChain.FGSA.Run.sourceDiscipline_labelBound',
    'AvailableChain.FGSA.Run.sourceDiscipline_emittedName',
    'AvailableChain.FGSA.Run.sourceDiscipline_base',

    'AvailableChain.FGSA.Run.fgsa_gate_of_coveringBatch',
    'AvailableChain.FGSA.Run.fgsa_S_eq_of_exact',
    'AvailableChain.FGSA.Run.openingSource_extends_served',
    'AvailableChain.FGSA.Run.RCarrierView',
    'AvailableChain.FGSA.Run.RCarrierView_def',
    'AvailableChain.FGSA.Run.RFrame',
    'AvailableChain.FGSA.Run.RFrame_def',
    'AvailableChain.FGSA.Run.RQCOrigin',
    'AvailableChain.FGSA.Run.RQCOrigin_def',
    'AvailableChain.FGSA.Run.FrameAt',
    'AvailableChain.FGSA.Run.RActive',
    'AvailableChain.FGSA.Run.RActive_def',
    'AvailableChain.FGSA.Run.RCert',
    'AvailableChain.FGSA.Run.RCert_def',
    'AvailableChain.FGSA.Run.ChainCertificatesAt',
    'AvailableChain.FGSA.Run.FGSASafetyClaims',
    'AvailableChain.FGSA.Run.FGSASafetyInterfaces',
    'AvailableChain.FGSA.Run.ReconcileAt',
    'AvailableChain.FGSA.Run.OutputNestingAt',
    'AvailableChain.FGSA.Run.OutputNestingClaim',

    'AvailableChain.FGSA.Run.CleanCutPosClaim',
    'AvailableChain.FGSA.Run.FGFoundationClaim',
    'AvailableChain.FGSA.Run.SrcFrameAboveClaim',
    'AvailableChain.FGSA.Run.RunFGBlock',
    'AvailableChain.FGSA.Run.CarrierAt',
    'AvailableChain.FGSA.Run.StoreAt',
    'AvailableChain.FGSA.Run.ActiveViewAt',
    'AvailableChain.FGSA.Run.LeaseOriginsAt',
    'AvailableChain.FGSA.Run.SourceDisciplineBaseAt',
    'AvailableChain.FGSA.Run.SourceDisciplineAt',
    'AvailableChain.FGSA.Run.CarrierClaim',
    'AvailableChain.FGSA.Run.ChainCertificatesClaim',
    'AvailableChain.FGSA.Run.StoreClaim',
    'AvailableChain.FGSA.Run.ActiveViewClaim',
    'AvailableChain.FGSA.Run.LeaseOriginsClaim',
    'AvailableChain.FGSA.Run.ReconcileClaim',
    'AvailableChain.FGSA.Run.FrameClaim',
    'AvailableChain.FGSA.Run.SourceDisciplineBaseClaim',
    'AvailableChain.FGSA.Run.SourceDisciplineClaim',
    'AvailableChain.FGSA.Run.ReleaseStoreAt',
    'AvailableChain.FGSA.Run.ReleaseStoreClaim',
    'AvailableChain.FGSA.Run.ReleaseAt',
    'AvailableChain.FGSA.Run.ReleaseClaim',
    'AvailableChain.FGSA.Run.ReleasePrem',

    'AvailableChain.FGSA.Run.ClientSafeAll',
    'AvailableChain.FGSA.Run.ClientSafetyClaim',
    'AvailableChain.FGSA.Run.ClientSafetyBaseClaim',
    'AvailableChain.FGSA.Run.SameLabelAt',
    'AvailableChain.FGSA.Run.SameLabelClaim',
    'AvailableChain.FGSA.Run.HeadReachesLoAt',
    'AvailableChain.FGSA.Run.HeadReachesLoClaim',
    'AvailableChain.FGSA.Run.CleanHistoryAt',
    'AvailableChain.FGSA.Run.CleanGateAt',
    'AvailableChain.FGSA.Run.CleanTruncAt',
    'AvailableChain.FGSA.Run.CleanSafetyAt',
    'AvailableChain.FGSA.Run.CleanCutClaim',
    'AvailableChain.FGSA.Run.CleanCutZeroClaim',
    'AvailableChain.FGSA.Run.CleanHistoryClaim',
    'AvailableChain.FGSA.Run.CleanPrefixTruncationClaim',
    'AvailableChain.FGSA.Run.CleanSafetyClaim',
    'AvailableChain.FGSA.Run.clientSafety_base',
    'AvailableChain.FGSA.Run.cleanHistory_of_cut',
    'AvailableChain.FGSA.Run.cleanPrefixTruncation_of_cut',
    'AvailableChain.FGSA.Run.cleanSafety_outputs',
    'AvailableChain.FGSA.Run.certified',
    'AvailableChain.FGSA.Run.FrameBelow',
    'AvailableChain.FGSA.Run.RStrat',
    'AvailableChain.FGSA.Run.SrcFrameAbove',
    'AvailableChain.FGSA.Run.SrcFrame',
    'AvailableChain.FGSA.Run.SrcFrameAboveStmt',
    'AvailableChain.FGSA.Run.CPPrefix',
    'AvailableChain.FGSA.Run.CPCompat',
    'AvailableChain.FGSA.Run.TimingContract',
    'AvailableChain.FGSA.Run.FGFoundation',
    'AvailableChain.FGSA.Run.certified_def',
    'AvailableChain.FGSA.Run.HonestRowBefore_def',

    'AvailableChain.FGSA.Run.Outage₂',
    'AvailableChain.FGSA.Run.OutageSet',
    'AvailableChain.FGSA.Run.outWin',
    'AvailableChain.FGSA.Run.OutagePrem',
    'AvailableChain.FGSA.Run.Outage₂.pos',
    'AvailableChain.FGSA.Run.Outage₂.toCleanCut',
    'AvailableChain.FGSA.Run.Outage₂.faultQ',


    'AvailableChain.FGSA.Run.awakeHonestIn',
    'AvailableChain.FGSA.Run.HonestProposal',
    'AvailableChain.FGSA.Run.Base₂',
    'AvailableChain.FGSA.Run.HealthyPrefix₂',
    'AvailableChain.FGSA.Run.CleanPrefix₂',
    'AvailableChain.FGSA.Run.CleanCut₂',
    'AvailableChain.FGSA.Run.Clean₂',
    'AvailableChain.FGSA.Run.Recovery₂',
    'AvailableChain.FGSA.Run.BaseSet',
    'AvailableChain.FGSA.Run.CleanSet',
    'AvailableChain.FGSA.Run.CleanCutSet',
    'AvailableChain.FGSA.Run.CleanPrefixSet',
    'AvailableChain.FGSA.Run.HealingSet',
    'AvailableChain.FGSA.Run.WinSpec',
    'AvailableChain.FGSA.Run.PtB₀',
    'AvailableChain.FGSA.Run.PtT',
    'AvailableChain.FGSA.Run.PtOut',
    'AvailableChain.FGSA.Run.cleanWinAt',
    'AvailableChain.FGSA.Run.cleanWin',
    'AvailableChain.FGSA.Run.cleanPrefixWin',
    'AvailableChain.FGSA.Run.cleanLabelWin',
    'AvailableChain.FGSA.Run.gapWin',
    'AvailableChain.FGSA.Run.formWinAt',
    'AvailableChain.FGSA.Run.kernelWin',
    'AvailableChain.FGSA.Run.trigWin',
    'AvailableChain.FGSA.Run.PtS',
    'AvailableChain.FGSA.Run.PtSP',
    'AvailableChain.FGSA.Run.PtSX',
    'AvailableChain.FGSA.Run.BasePrem',
    'AvailableChain.FGSA.Run.SameLabelPrem',
    'AvailableChain.FGSA.Run.SourceDisciplinePrem',
    'AvailableChain.FGSA.Run.FinalizedSafetyPrem',
    'AvailableChain.FGSA.Run.CleanPrem',
    'AvailableChain.FGSA.Run.CleanPrefixPrem',
    'AvailableChain.FGSA.Run.CleanCutPrem',
    'AvailableChain.FGSA.Run.card_eq_n_of_linked',
    'AvailableChain.FGSA.Run.CleanPrefix₂.toCleanCut',
    'AvailableChain.FGSA.Run.HealthyPrefix₂.faultQ_of_pos',
    'AvailableChain.FGSA.Run.CleanPrefix₂.faultQ',
    'AvailableChain.FGSA.Run.HealthyPrefix₂.batch',
    'AvailableChain.FGSA.Run.CleanPrefix₂.batchAt',
    'AvailableChain.FGSA.Run.Recovery₂.batch',
    'AvailableChain.FGSA.Run.fgsa_clean_delivery_iff',
    'AvailableChain.FGSA.Run.HealthyPrefix₂.of_legacy',
    'AvailableChain.FGSA.Run.HealthyPrefix₂.legacy_delivery',
    'AvailableChain.FGSA.Run.Recovery₂.of_legacy',
    'AvailableChain.FGSA.Run.Recovery₂.gamma_eq',
    'AvailableChain.FGSA.Run.Recovery₂.toRecoveryCore',
    'AvailableChain.FGSA.Run.fgsa_seed_reachable',
    'AvailableChain.FGSA.Run.fgsa_seed_accepted',

    'AvailableChain.FGSA.Run.treeT',
    'AvailableChain.FGSA.Run.treeErased',
    'AvailableChain.FGSA.Run.frameR',
    'AvailableChain.FGSA.Run.domainR',
    'AvailableChain.FGSA.Run.finR',
    'AvailableChain.FGSA.Run.FAdvance',
    'AvailableChain.FGSA.Run.sourceCandidates',
    'AvailableChain.FGSA.Run.jointSource',
    'AvailableChain.FGSA.Run.proposerHead',
    'AvailableChain.FGSA.Run.outputS',
    'AvailableChain.FGSA.Run.frameR_def',
    'AvailableChain.FGSA.Run.jointSource_def',
    'AvailableChain.FGSA.Run.sourceCandidates_def',
    'AvailableChain.FGSA.Run.domainR_def',
    'AvailableChain.FGSA.Run.treeT_def',
    'AvailableChain.FGSA.Run.proposerHead_def',
    'AvailableChain.FGSA.Run.FAdvance_def',
    'AvailableChain.FGSA.Run.R_at',
    'AvailableChain.FGSA.Run.D_at',
    'AvailableChain.FGSA.Run.FAdvanceAt',
    'AvailableChain.FGSA.Run.candidatesAt',
    'AvailableChain.FGSA.Run.proposalHeadAt',
    'AvailableChain.FGSA.Run.actionHead',
    'AvailableChain.FGSA.Run.actionTriple',
    'AvailableChain.FGSA.Run.namedEntry',
    'AvailableChain.FGSA.Run.EntryBelow',
    'AvailableChain.FGSA.Run.RowSigner',
    'AvailableChain.FGSA.Run.HonestRowAt',
    'AvailableChain.FGSA.Run.HonestRowBefore',
    'AvailableChain.FGSA.Run.RowComplete',
    'AvailableChain.FGSA.Run.HonestCarrier',
    'AvailableChain.FGSA.Run.HeldAt',
    'AvailableChain.FGSA.Run.BlockInRunBefore',
    'AvailableChain.FGSA.Run.RowSigner_def',
    'AvailableChain.FGSA.Run.HonestRowAt_def',
    # post-freeze additive _def batch: --expect DATA only.
    'AvailableChain.FGSA.Run.RowComplete_def',
    'AvailableChain.FGSA.Run.HonestCarrier_def',
    'AvailableChain.FGSA.Run.HeldAt_def',
    'AvailableChain.FGSA.Run.namedEntry_def',
    'AvailableChain.FGSA.Run.rowHeight_def',
    'AvailableChain.FGSA.Run.eventTime_def',
    'AvailableChain.FGSA.Run.honestSeats_def',
    'AvailableChain.FGSA.Run.muOf_def',
    'AvailableChain.FGSA.Run.high_def',
    'AvailableChain.FGSA.Run.RStore',
    'AvailableChain.FGSA.Run.RStoreCumul',
    'AvailableChain.FGSA.Run.RMono',
    'AvailableChain.FGSA.Run.RFrameExact',
    'AvailableChain.FGSA.Run.RGeo',
    'AvailableChain.FGSA.Run.RRec',
    'AvailableChain.FGSA.Run.TSrc',
    'AvailableChain.FGSA.Run.LabelBound',
    'AvailableChain.FGSA.Run.TChain',
    'AvailableChain.FGSA.Run.TCompat',
    'AvailableChain.FGSA.Run.AncestorClosed',
    'AvailableChain.FGSA.Run.RStore_def',
    'AvailableChain.FGSA.Run.RStoreCumul_def',
    'AvailableChain.FGSA.Run.RMono_def',
    'AvailableChain.FGSA.Run.RFrameExact_def',
    'AvailableChain.FGSA.Run.RGeo_def',
    'AvailableChain.FGSA.Run.RRec_def',
    'AvailableChain.FGSA.Run.TSrc_def',
    'AvailableChain.FGSA.Run.LabelBound_def',
    'AvailableChain.FGSA.Run.TChain_def',
    'AvailableChain.FGSA.Run.TCompat_def',
    'AvailableChain.FGSA.Run.FrameBelow_def',
    'AvailableChain.FGSA.Run.RStrat_def',
    'AvailableChain.FGSA.Run.SrcFrameAbove_def',
    'AvailableChain.FGSA.Run.SrcFrameAboveStmt_def',
    'AvailableChain.FGSA.Run.CPPrefix_def',
    'AvailableChain.FGSA.Run.CPCompat_def',
    'AvailableChain.FGSA.Run.windowIdx',
    'AvailableChain.FGSA.Run.fgSource_eq_jointSource',
    'AvailableChain.FGSA.Run.ancestorClosed_preceq',
    'AvailableChain.FGSA.Run.ancestorClosed_compatible',
    'AvailableChain.FGSA.Run.srcFrame_genesis_preceq',
    'AvailableChain.FGSA.Run.srcFrame_genesis_compatible',
    'AvailableChain.FGSA.Run.propose_head',
    'AvailableChain.FGSA.Run.frameR_congr_fg',
    'AvailableChain.FGSA.Run.domainR_congr_fg',
    'AvailableChain.FGSA.Run.frame_postClock',
    'AvailableChain.FGSA.Run.eligible_lo_live',
    'AvailableChain.FGSA.Run.jointSelections_record_irrel',
    'AvailableChain.FGSA.Run.rowSigner_iff_holder',
    'AvailableChain.FGSA.Run.emit_lt_handles',
    'AvailableChain.FGSA.Run.preTick_def',
    'AvailableChain.FGSA.Run.postClock_def',
    'AvailableChain.FGSA.Run.gateIn_def',
    'AvailableChain.FGSA.Run.gateResult_def',
    'AvailableChain.FGSA.Run.isGateTime_def',
    'AvailableChain.FGSA.Run.vHead_def',
    'AvailableChain.FGSA.Run.actionSourceFG_def',
    'AvailableChain.FGSA.Run.fgsa_strongW_recF',
    'AvailableChain.FGSA.Run.fgsa_lit_recF',
    'AvailableChain.FGSA.Run.fgsa_recPat_restricted',
    'AvailableChain.FGSA.Run.fgsa_recPatAt_restricted',
    'AvailableChain.FGSA.Run.fgsa_restricted_of_unrestricted',
    'AvailableChain.FGSA.Run.fgsa_horizon_mono',
    'AvailableChain.FGSA.Run.fgsa_B_max',
    'AvailableChain.FGSA.Run.L',
    'AvailableChain.FGSA.Run.P',
    'AvailableChain.FGSA.Run.Γ',
    'AvailableChain.FGSA.Run.ρΓ',
    'AvailableChain.FGSA.Run.ρ₁',
    'AvailableChain.FGSA.Run.ρ',
    'AvailableChain.FGSA.Run.E_g',
    'AvailableChain.FGSA.Run.E_j',
    'AvailableChain.FGSA.Run.B_c',
    'AvailableChain.FGSA.Run.D_c',
    'AvailableChain.FGSA.Run.B_reset',
    'AvailableChain.FGSA.Run.B',
    'AvailableChain.FGSA.Run.B_H2',
    'AvailableChain.FGSA.Run.B_H1',
    'AvailableChain.FGSA.Run.B_H',
    'AvailableChain.FGSA.Run.W_F',
    'AvailableChain.FGSA.Run.B_F',
    'AvailableChain.FGSA.Run.B_heal',
    'AvailableChain.FGSA.Run.B_best',
    'AvailableChain.FGSA.Run.carrierTime2',
    'AvailableChain.FGSA.Run.kernelDeadline',
    'AvailableChain.FGSA.Run.ActionDeliveryBounds',
    'AvailableChain.FGSA.Run.KernelBeforeNextAction',
    'AvailableChain.FGSA.Run.VoteBeforeAction',
    'AvailableChain.FGSA.Run.GateAfterCarrier2',
    'AvailableChain.FGSA.Run.GateActionOrder',
    'AvailableChain.FGSA.Run.FourteenBeforeTwoRounds',
    'AvailableChain.FGSA.Run.cutPred',
    'AvailableChain.FGSA.Run.afterTicksIdx',
    'AvailableChain.FGSA.Run.afterTicks',
    'AvailableChain.FGSA.Run.SuffixIdx',
    'AvailableChain.FGSA.Run.timeIdx',
    'AvailableChain.FGSA.Run.preTick',
    'AvailableChain.FGSA.Run.postClock',
    'AvailableChain.FGSA.Run.postTick',
    'AvailableChain.FGSA.Run.afterTicks_eq_stateBefore',
    'AvailableChain.FGSA.Run.afterTicks_node',
    'AvailableChain.FGSA.Run.afterTicks_eq_tick_preTick',
    'AvailableChain.FGSA.Run.preIdx_le_afterTicksIdx',
    'AvailableChain.FGSA.Run.afterTicksIdx_mono',
    'AvailableChain.FGSA.Run.storeAt',
    'AvailableChain.FGSA.Run.S_at',
    'AvailableChain.FGSA.Run.F_at',
    'AvailableChain.FGSA.Run.J_at',
    'AvailableChain.FGSA.Run.gateIn',
    'AvailableChain.FGSA.Run.gateResult',
    'AvailableChain.FGSA.Run.isGateTime',
    'AvailableChain.FGSA.Run.IsGateTick',
    'AvailableChain.FGSA.Run.gateResultAt',
    'AvailableChain.FGSA.Run.gatePassedAt',
    'AvailableChain.FGSA.Run.fastAt',
    'AvailableChain.FGSA.Run.headAtIdx',
    'AvailableChain.FGSA.Run.vHead',
    'AvailableChain.FGSA.Run.actionSourceFG',
    'AvailableChain.FGSA.Run.actionSource',
    'AvailableChain.FGSA.Run.labelBoundAt',
    'AvailableChain.FGSA.Run.DeliveredAt',
    'AvailableChain.FGSA.Run.HandlesRowAt',
    'AvailableChain.FGSA.Run.AcceptsFinalBefore',
    'AvailableChain.FGSA.Run.cleanResults',
    'AvailableChain.FGSA.Run.BelowLabel',
    'AvailableChain.FGSA.Run.gateResult_eq_saved',
    'AvailableChain.FGSA.Run.isGateTime_iff',
    'AvailableChain.FGSA.Run.gateResultAt_eq_gateResult',
    'AvailableChain.FGSA.Run.vHead_eq_headAtIdx',
    'AvailableChain.FGSA.Run.actionSourceFG_eq_round',
    'AvailableChain.FGSA.Run.acceptsFinalBefore_of_idx',
    'AvailableChain.FGSA.Run.acceptsFinalBefore_mono_deadline',
    'AvailableChain.FGSA.Run.stable_afterTicks',
    # fg-noround/07-H: height coverage, strict row receipt, and source adapters.
    'AvailableChain.FGSA.Run.RowServiceBaseClaim',
    'AvailableChain.FGSA.Run.TRowsReceipt',
    'AvailableChain.FGSA.Run.TRowsReceipt_def',
    'AvailableChain.FGSA.Run.OpeningCovered',
    'AvailableChain.FGSA.Run.FinalityRowCarriage',
    'AvailableChain.FGSA.Run.FinalityRowCarriage_def',
    'AvailableChain.FGSA.Run.HeightMatch',
    'AvailableChain.FGSA.Run.HeightMatch_def',
    'AvailableChain.FGSA.Run.SettledPhaseFrame',
    'AvailableChain.FGSA.Run.SettledPhaseFrame_def',
    'AvailableChain.FGSA.Run.RPhase',
    'AvailableChain.FGSA.Run.RPhase_def',
    'AvailableChain.FGSA.Run.HealRContract',
    'AvailableChain.FGSA.Run.ProgressAttemptStatement',
    'AvailableChain.FGSA.Run.ProgressAttemptStatement_def',
    'AvailableChain.FGSA.Run.HealingInputPrem',
    'AvailableChain.FGSA.Run.RenewedPromotionPrem',
    'AvailableChain.FGSA.Run.fgsa_finalityRowCarriage',
    'AvailableChain.FGSA.Run.sourceDiscipline_emittedNonempty',
    'AvailableChain.FGSA.Run.RowPermissionAt',
    'AvailableChain.FGSA.Run.RowPermissionClaim',
    'AvailableChain.FGSA.Run.RowServiceClaim',
    'AvailableChain.FGSA.Run.HealingInputClaim',
    'AvailableChain.FGSA.Run.HTimeConcl',
    'AvailableChain.FGSA.Run.HTimeClaim',
    'AvailableChain.FGSA.Run.ResetArrivalConcl',
    'AvailableChain.FGSA.Run.ResetArrivalClaim',
    'AvailableChain.FGSA.Run.RenewedPromotionConcl',
    'AvailableChain.FGSA.Run.RenewedPromotionClaim',
    'AvailableChain.FGSA.Run.RowKind',
    'AvailableChain.FGSA.Run.RowNames',
    'AvailableChain.FGSA.Run.SlotChain',
    'AvailableChain.FGSA.Run.EntryAt',
    'AvailableChain.FGSA.Run.JustifiedCross',
    'AvailableChain.FGSA.Run.MixedCross',
    'AvailableChain.FGSA.Run.NoMixedOnPath',
    'AvailableChain.FGSA.Run.SeatCovers',
    'AvailableChain.FGSA.Run.CoveredByChild',
    'AvailableChain.FGSA.Run.foldTrichotomy',
    'AvailableChain.FGSA.Run.StoredProgressConsume',
    'AvailableChain.FGSA.Run.NoMixedMaturity',
    'AvailableChain.FGSA.Run.NamesEntry',
    'AvailableChain.FGSA.Run.rowHeight',
    'AvailableChain.FGSA.Run.eventTime',
    'AvailableChain.FGSA.Run.honestSeats',
    'AvailableChain.FGSA.Run.ChainRowsBefore',
    'AvailableChain.FGSA.Run.PreBatchPrem',
    'AvailableChain.FGSA.Run.NoMixedPreBatchParent',
    'AvailableChain.FGSA.Run.BatchPrem',
    'AvailableChain.FGSA.Run.BatchPrem.batch_of_valid',
    'AvailableChain.FGSA.Run.BatchCoverage',
    'AvailableChain.FGSA.Run.finHeight',
    'AvailableChain.FGSA.Run.FreshPrem',
    'AvailableChain.FGSA.Run.fgsa_rowBitPersist',
    'AvailableChain.FGSA.Run.fgsa_rowService_receipt',
    'AvailableChain.FGSA.Run.validForParent_currentHeightMatch',
    'AvailableChain.FGSA.Run.domainR_eq_storeFrame',
    'AvailableChain.FGSA.Run.fgsa_tRowsSelect',
    'AvailableChain.FGSA.Run.fgsa_rowsReceipt_carriage',
    'AvailableChain.FGSA.Run.fgsa_tRowsReceipt',
    'AvailableChain.FGSA.Run.fgsa_tRowsSync',
    'AvailableChain.FGSA.Run.fgsa_tRows',
    'AvailableChain.FGSA.Run.fgsa_rowServiceBaseClaim',
    'AvailableChain.FGSA.Run.fgsa_rowServiceClaim',
    'AvailableChain.FGSA.Run.fgsa_rowsValidStored_atProposal',
    'AvailableChain.FGSA.Run.fgsa_batchCoverage',
    # S5 H-ATTEMPT-2: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_settle_start',
    'AvailableChain.FGSA.Run.healing_attempt_settle_start',
    'AvailableChain.FGSA.Run.healing_attempt_raise_contest_settle',
    'AvailableChain.FGSA.Run.healing_attempt_raise_other_settle',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_settle',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_other_settle',
    # S5 H-ATTEMPT-3: --expect ADDITIONS only.
    # S5 H-ATTEMPT-4: complete H.10 rows and lane assembly; --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_contest',
    'AvailableChain.FGSA.Run.healing_attempt_firstRow_other',
    'AvailableChain.FGSA.Run.healing_renewedPromotion_terminal',
    'AvailableChain.FGSA.Run.healing_attempt_raise_contest',
    'AvailableChain.FGSA.Run.healing_attempt_raise_other',
    'AvailableChain.FGSA.Run.healing_progressAttempt',

    # POSTRESET-DESIGN: --expect DATA only.
    'AvailableChain.FGSA.Run.PostResetStart',
    'AvailableChain.FGSA.Run.PostResetStart.toH0',
    'AvailableChain.FGSA.Run.ResetTransferCore_def',
    'AvailableChain.FGSA.Run.ProtectedBody_def',
    'AvailableChain.FGSA.Run.PostResetProtectedKept_def',
    'AvailableChain.FGSA.Run.PostResetHighCompatible_def',
    'AvailableChain.FGSA.Run.PostResetResetCompatible_def',
    'AvailableChain.FGSA.Run.PostResetLeaseSafe_def',
    'AvailableChain.FGSA.Run.PostResetFProv_def',
    'AvailableChain.FGSA.Run.PostResetRawTransfer_def',
    'AvailableChain.FGSA.Run.PostResetService_def',
    'AvailableChain.FGSA.Run.ResetTransferCore',
    'AvailableChain.FGSA.Run.ProtectedBody',
    'AvailableChain.FGSA.Run.PostResetProtectedKept',
    'AvailableChain.FGSA.Run.PostResetHighCompatible',
    'AvailableChain.FGSA.Run.PostResetResetCompatible',
    'AvailableChain.FGSA.Run.PostResetLeaseSafe',
    'AvailableChain.FGSA.Run.PostResetFProv',
    'AvailableChain.FGSA.Run.PostResetRawTransfer',
    'AvailableChain.FGSA.Run.PostResetService',
    'AvailableChain.FGSA.Run.PostResetInv',
    # J2-COMPAT: --expect DATA only.
    'AvailableChain.FGSA.Run.postReset_high_compatible_all',
    'AvailableChain.FGSA.Run.postReset_high_compatible_succ',
    'AvailableChain.FGSA.Run.postReset_reset_compatible_all',
    'AvailableChain.FGSA.Run.postReset_reset_compatible_succ',
    'AvailableChain.FGSA.Run.postReset_descent_kept',
    # S5 RS-0: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.reset_period_lower',
    'AvailableChain.FGSA.Run.reset_action_exists',
    'AvailableChain.FGSA.Run.resetFirstRound',
    'AvailableChain.FGSA.Run.resetCutTime',
    'AvailableChain.FGSA.Run.reset_rG_after',
    'AvailableChain.FGSA.Run.reset_rG_first',
    'AvailableChain.FGSA.Run.reset_cut',
    'AvailableChain.FGSA.Run.reset_first_action_upper',
    'AvailableChain.FGSA.Run.reset_cut_lower',
    'AvailableChain.FGSA.Run.reset_cut_upper',
    'AvailableChain.FGSA.Run.resetCutFrontier',
    'AvailableChain.FGSA.Run.reset_frontier',
    'AvailableChain.FGSA.Run.reset_inclusive_frontier',
    'AvailableChain.FGSA.Run.reset_inclusive_start_iff',
    'AvailableChain.FGSA.Run.reset_row_cap',
    'AvailableChain.FGSA.Run.reset_old_row_before_cut',
    'AvailableChain.FGSA.Run.reset_old_height_sup_le',
    'AvailableChain.FGSA.Run.reset_mu_le_iff',
    # H12-RELAY: --expect DATA additions only.
    'AvailableChain.FGSA.Run.healing_source_label_bound',
    'AvailableChain.FGSA.Run.healing_source_relay_deadline',
    'AvailableChain.FGSA.Run.healing_source_row_label',
    'AvailableChain.FGSA.Run.healing_tf_retention',
    'AvailableChain.FGSA.Run.healing_source_path_retained',
    'AvailableChain.FGSA.Run.healing_source_supporter_head',
    'AvailableChain.FGSA.Run.healing_source_body_relay',
    'AvailableChain.FGSA.Run.healing_source_body_stamps',
    'AvailableChain.FGSA.Run.healing_source_old_body',
    'AvailableChain.FGSA.Run.healing_tDel',
    'AvailableChain.FGSA.Run.healing_tDelReset_core',
    'AvailableChain.FGSA.Run.healing_tDelReset',
    # J3-KEEP: --expect DATA only.
    'AvailableChain.FGSA.Run.postReset_general_kept',
    'AvailableChain.FGSA.Run.postReset_keep_height',
    'AvailableChain.FGSA.Run.postReset_keep_contest',
    'AvailableChain.FGSA.Run.postReset_keep_floor',
    'AvailableChain.FGSA.Run.postReset_keep_roots',
    'AvailableChain.FGSA.Run.postReset_keep_witness',
    'AvailableChain.FGSA.Run.postReset_keep_body',
    'AvailableChain.FGSA.Run.postReset_protected_kept_succ',
    'AvailableChain.FGSA.Run.postReset_rKeep_body',
    'AvailableChain.FGSA.Run.postReset_receiver_compatible',
    'AvailableChain.FGSA.Run.postReset_tDel',
    # S5 J6: --expect additions only; gate items are stopped.
    # S5 PA-ASSEMBLY P2: --expect ADDITIONS only.
    'AvailableChain.FGSA.Run.healing_progressAttemptStatement',
    # S5 J6 / J6-2: --expect additions only; the S1 service step is stopped (opening_domain).
    'AvailableChain.FGSA.Run.PostResetRetainedCone',
    'AvailableChain.FGSA.Run.postReset_source_label_le_sub_two',
    'AvailableChain.FGSA.Run.postReset_release_before_proposal',
    'AvailableChain.FGSA.Run.postReset_proposal_horizon',
    'AvailableChain.FGSA.Run.postReset_head_horizon',
    'AvailableChain.FGSA.Run.postReset_synchronous_window',
    'AvailableChain.FGSA.Run.postResetRetainedCone_of_horizon_lt',
    'AvailableChain.FGSA.Run.healing_postReset_retainedReads',
    'AvailableChain.FGSA.Run.healing_postReset_headGeometry',
    'AvailableChain.FGSA.Run.healing_postReset_exactHead',
    'AvailableChain.FGSA.Run.healing_postReset_headCarrier',
    'AvailableChain.FGSA.Run.postResetRetainedCone_iff',
    'AvailableChain.FGSA.Run.healing_postReset_gate_covered_prefix',
    'AvailableChain.FGSA.Run.healing_postReset_exactService_at_cut',
    'AvailableChain.FGSA.Run.healing_postReset_exactService',
    'AvailableChain.FGSA.Run.healing_postReset_gate_guard',
    'AvailableChain.FGSA.Run.healing_postReset_h6GateService',
    # J11 H-TIME: --expect DATA additions only.
    'AvailableChain.FGSA.Run.HealingInputOfH0Statement',
    'AvailableChain.FGSA.Run.HealingInputOfH0Statement_def',
    'AvailableChain.FGSA.Run.healing_resetF_budget_eq',
    'AvailableChain.FGSA.Run.healing_resetFull_horizon',
    'AvailableChain.FGSA.Run.healing_time_strict_of_reset',
    'AvailableChain.FGSA.Run.healing_hTime_of',
    # J3-KEEP: --expect DATA only.
    # J1-RESET: --expect DATA additions only.
    'AvailableChain.FGSA.Run.healing_low_finality_at_reset_reset',
    'AvailableChain.FGSA.Run.healing_resetTransferCore',
    'AvailableChain.FGSA.Run.healing_tDelReset_of_reset',
    'AvailableChain.FGSA.Run.healing_low_finality_after_reset',
    # THigh: --expect DATA additions only.
    'AvailableChain.FGSA.Run.postReset_descent_kept_of_compat',
    'AvailableChain.FGSA.Run.postReset_general_kept_of_compat',
    'AvailableChain.FGSA.Run.postReset_rKeep_body_of_compat',
    'AvailableChain.FGSA.Run.postReset_rKeep_body_reset',
    'AvailableChain.FGSA.Run.postReset_selected_label_above',
    'AvailableChain.FGSA.Run.postReset_selected_label',
    'AvailableChain.FGSA.Run.SelectedBefore',
    'AvailableChain.FGSA.Run.SelectedBefore_def',
    'AvailableChain.FGSA.Run.selectedBefore_of_sourceBefore',
    'AvailableChain.FGSA.Run.postReset_selected_reset_compatible',
    # J5-RAW: --expect DATA additions only.
    'AvailableChain.FGSA.Run.postReset_h5RawTransfer_body',
    # J4-LEASE: --expect DATA only.
    'AvailableChain.FGSA.Run.postReset_fProv_all',
    'AvailableChain.FGSA.Run.postReset_rFProv_reset',
    'AvailableChain.FGSA.Run.postReset_leaseSafe_antecedent_of_lastWrite',
    # J5A-RAW: --expect DATA additions only.
    'AvailableChain.FGSA.Run.PostResetResetLeaseCompatible',
    'AvailableChain.FGSA.Run.PostResetResetLeaseCompatible_def',
    'AvailableChain.FGSA.Run.healing_gate_result_supporter',
    'AvailableChain.FGSA.Run.postReset_delivery_no_obligation',
    'AvailableChain.FGSA.Run.postReset_resetLease_preserve',
    'AvailableChain.FGSA.Run.postReset_resetLease_base',
    'AvailableChain.FGSA.Run.healing_first_transfer_raw_domain',
    'AvailableChain.FGSA.Run.postReset_slow_window_sync',
    'AvailableChain.FGSA.Run.postReset_raw_reset_compatible',
    'AvailableChain.FGSA.Run.postReset_noRewrite',
    'AvailableChain.FGSA.Run.healing_output_moving_suffix',
    'AvailableChain.FGSA.Run.postReset_resetLease_at_reset',
    'AvailableChain.FGSA.Run.postReset_resetLease_succ',
    'AvailableChain.FGSA.Run.postReset_raw_release_compatible',
    'AvailableChain.FGSA.Run.healing_proposal_moving_domain',
    'AvailableChain.FGSA.Run.healing_proposal_moving_parent',
    'AvailableChain.FGSA.Run.postReset_resetLease_zero',
    'AvailableChain.FGSA.Run.postReset_rawTransfer_before_reset',
    'AvailableChain.FGSA.Run.postReset_resetLease_step',
    # J9-POST: --expect DATA additions only.
    'AvailableChain.FGSA.Run.healing_healTContract_reset',
    'AvailableChain.FGSA.Run.healing_rKeep_of_reset',
    'AvailableChain.FGSA.Run.healing_rFProv_of_reset',
    'AvailableChain.FGSA.Run.healing_healRContract_reset',
    'AvailableChain.FGSA.Run.healing_healT_of',
    'AvailableChain.FGSA.Run.healing_healAC_of',
    'AvailableChain.FGSA.Run.healing_healingInput_of',
    # J11 H-TIME: --expect DATA additions only.
    'AvailableChain.FGSA.Run.HealingInputOfH0Statement',
    'AvailableChain.FGSA.Run.HealingInputOfH0Statement_def',
    'AvailableChain.FGSA.Run.healing_resetF_budget_eq',
    'AvailableChain.FGSA.Run.healing_resetFull_horizon',
    'AvailableChain.FGSA.Run.healing_time_strict_of_reset',
    'AvailableChain.FGSA.Run.healing_hTime_of',

    # J7 H.18: --expect DATA additions only.
    'AvailableChain.FGSA.Run.healing_sourcePrefix',
    'AvailableChain.FGSA.Run.healing_proposal_grid_lower',
    'AvailableChain.FGSA.Run.healing_firstProposal_deadline',
    'AvailableChain.FGSA.Run.healing_firstProposal',
    'AvailableChain.FGSA.Run.healing_h0_of',
    'AvailableChain.FGSA.Run.healing_h4_stable',
    'AvailableChain.FGSA.Run.healing_h4_stable_of_service',
    'AvailableChain.FGSA.Run.healing_h4_crossBelow',
    'AvailableChain.FGSA.Run.healing_healed_proposal_lower',
    'AvailableChain.FGSA.Run.healing_healed',
    'AvailableChain.FGSA.Run.healing_reset_rStar_unique',
    'AvailableChain.FGSA.Run.healing_tstar_le_of_h0',
    'AvailableChain.FGSA.Run.healing_timeBound_of_resetArrival',
    'AvailableChain.FGSA.Run.healing_h4_rawCompatible',
    'AvailableChain.FGSA.Run.healing_h4',
    # J10 HealingInput export: --expect DATA additions only.
    'AvailableChain.FGSA.Run.healing_postResetStart_of_h0',
    'AvailableChain.FGSA.Run.healing_healingInputOfH0',
    'AvailableChain.FGSA.Run.healing_hTime_of_inputs',
    # J4-A-LEASE: --expect DATA only.
    'AvailableChain.FGSA.Run.healing_first_transfer_written',
    'AvailableChain.FGSA.Run.postReset_written_sync',
    # J4-A2-LEASE: --expect DATA only.
    'AvailableChain.FGSA.Run.postReset_written_source_compatible',
    'AvailableChain.FGSA.Run.postReset_written_domain',
    'AvailableChain.FGSA.Run.postReset_written_first_head',
    'AvailableChain.FGSA.Run.postReset_written_first_head_label',
    'AvailableChain.FGSA.Run.postReset_written_heads_at_write_cut',
    'AvailableChain.FGSA.Run.postReset_written_later_result',
    'AvailableChain.FGSA.Run.postReset_leaseSafe_results_succ',
    # JOINT-IND: --expect DATA additions only.
    'AvailableChain.FGSA.Run.PostResetResetLeaseCompatibleP',
    'AvailableChain.FGSA.Run.PostResetOpeningDomainP',
    'AvailableChain.FGSA.Run.PostResetResetLeaseStep',
    'AvailableChain.FGSA.Run.PostResetLeaseStep',
    'AvailableChain.FGSA.Run.PostResetRawStep',
    'AvailableChain.FGSA.Run.PostResetOpeningDomainStep',
    'AvailableChain.FGSA.Run.PostResetServiceStep',
    'AvailableChain.FGSA.Run.PostResetResetLeaseCompatibleP_def',
    'AvailableChain.FGSA.Run.PostResetOpeningDomainP_def',
    'AvailableChain.FGSA.Run.PostResetResetLeaseStep_def',
    'AvailableChain.FGSA.Run.PostResetLeaseStep_def',
    'AvailableChain.FGSA.Run.PostResetRawStep_def',
    'AvailableChain.FGSA.Run.PostResetOpeningDomainStep_def',
    'AvailableChain.FGSA.Run.PostResetServiceStep_def',
    'AvailableChain.FGSA.Run.postReset_joint_zero',
    'AvailableChain.FGSA.Run.postReset_joint_all',
    'AvailableChain.FGSA.Run.postReset_inv_all',
    'AvailableChain.FGSA.Run.postReset_reset_lease_compatible_all',
    'AvailableChain.FGSA.Run.postReset_opening_domain_all',

    # J3-REST: --expect DATA additions only.
    'AvailableChain.FGSA.Run.postReset_source_gate_result',
    'AvailableChain.FGSA.Run.postReset_tCarrier_reset',
    'AvailableChain.FGSA.Run.postReset_h2A_reset',
    # J5-A-2: --expect DATA additions only.
    'AvailableChain.FGSA.Run.postReset_raw_first_head_above',
    'AvailableChain.FGSA.Run.postReset_raw_first_head',
    'AvailableChain.FGSA.Run.postReset_raw_first_head_label',
    'AvailableChain.FGSA.Run.postReset_raw_heads_at_gate_cut',
    'AvailableChain.FGSA.Run.postReset_raw_moving_domain',
    'AvailableChain.FGSA.Run.postReset_resetLease_succ_all',
    'AvailableChain.FGSA.Run.postReset_raw_at_gate_cut',
)
ORDER = ('Recurrence', 'Bounds', 'BoundsW', 'Reads', 'Counts', 'Regimes', 'Windows',
         'Packages.Safety', 'OutputReads', 'Packages.Inclusion', 'Packages.Outage', 'Channels', 'Witness',
         'ChannelProps', 'FinalityApi', 'Healed', 'HealedBest', 'WeakContinuation', 'WeakContinuationLive', 'Packages.Finality', 'Packages.FinalityGST',
         'ComposeStmt', 'Fold',
         'Phases', 'PhasesInternal', 'Packages.Healing')
if not SOURCE_ONLY:
    work = Path(tempfile.mkdtemp(prefix='fgsa-claims-check.', dir=ROOT / '.lake'))
    print(f'FGSA claims audit logs: {work}', flush=True)
serial = 0

def audit_workers():
    values = []
    # Two is the measured default: control RSS exceeded 7 GiB on the Mac.
    for key, default in (('AUDIT_WORKERS', '2'), ('LEAN_SLOTS', '3'),
                         ('GATE_SLOTS', os.environ.get('LEAN_SLOTS', '3'))):
        value = os.environ.get(key, default)
        if not re.fullmatch(r'[1-9][0-9]*', value):
            raise SystemExit(f'{key} must be a positive integer')
        values.append(int(value))
    return 1 if os.environ.get('AUDIT_SERIAL', '0') == '1' else min(values)

workers = audit_workers()
# The generated Lean code and the control pool use the same bound.
os.environ['AUDIT_WORKERS'] = str(workers)

def reserve_log(label):
    global serial
    serial += 1
    return work / f'{serial:02d}-{label}.log'

def execute(path, args, *, env=None, cwd=None):
    # Timing is opt-in; it does not enter the check's output.
    if os.environ.get('AUDIT_TIMING', '0') == '1':
        time_args = ['-l'] if sys.platform == 'darwin' else ['-v']
        args = ['/usr/bin/time', *time_args, '-o', str(path.with_suffix('.time')), *args]
    with path.open('w') as out:
        proc = subprocess.run(args, stdout=out, stderr=subprocess.STDOUT,
                              env=env, cwd=cwd)
    path.with_suffix('.rc').write_text(str(proc.returncode) + '\n')
    return proc.returncode

def result(label, path, code, expect):
    output = path.read_text()
    print(f'{label}: rc {code} ({path.name})', flush=True)
    if expect is None:
        if code:
            print(output)
            raise SystemExit(code)
    elif code == 0 or code < 0 or code >= 128 or expect not in output:
        print(output)
        raise SystemExit(f'STOP: negative control {label} did not fail with {expect!r}')
    else:
        print(f'rejected, as expected: {label}', flush=True)
    return output

def run(label, args, *, expect=None, env=None, cwd=None):
    path = reserve_log(label)
    return result(label, path, execute(path, args, env=env, cwd=cwd), expect)

def run_pool(controls):
    # Reserve names before submission. Workers write only their own logs.
    jobs = [(label, reserve_log(label), args, options)
            for label, args, options in sorted(controls, key=lambda c: c[0])]
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(execute, path, args,
                               env=options.get('env'), cwd=options.get('cwd'))
                   for _, path, args, options in jobs]
        outputs = {}
        failure = None
        for (label, path, _, options), future in zip(jobs, futures):
            try:
                outputs[label] = result(label, path, future.result(), options.get('expect'))
            except SystemExit as exc:
                if failure is None:
                    failure = exc
        if failure is not None:
            raise failure
    return outputs

# Exercise the same result path as a compiled control. A missed rejection
# must make the driver fail, even when another concurrent control passes.
if os.environ.get('AUDIT_POOL_SELFTEST', '0') == '1':
    run_pool([
        ('deliberately-failing-control', [sys.executable, '-c', 'print("CONTROL")'],
         {'expect': 'CONTROL'}),
        ('passing-control', [sys.executable, '-c', 'print("PASS")'], {}),
    ])
    raise SystemExit('STOP: pool accepted a deliberately failing control')

# Source policy: use check (e), then the tighter P3/T7 direct-import set.
ctx = L.load_context(ROOT)

def owned(name):
    return any(L.under(name, lib) for lib in LIBS)

def sources():
    files = []
    for lib in LIBS:
        files.append(Path(lib + '.lean'))
        for directory, _, names in os.walk(lib, followlinks=True):
            files.extend(Path(directory) / n for n in sorted(names) if n.lower().endswith('.lean'))
    return sorted(files)

def module(path):
    return str(path.with_suffix('')).replace(os.sep, '.')

def direct_ok(m, dep):
    if dep == 'Init':
        return True
    if m in LIBS:
        return L.under(dep, m) and dep != m and not L.is_test(dep)
    # SYN L58: one exact Assembly root may import the claim facade.
    if (m, dep) == (L.ASSEMBLY_ROOT, CLAIMS + '.FGSAClaims'):
        return True
    if dep in LIBS or dep.endswith('.FGSAClaims'):
        return False
    if dep.startswith(('AvailableChainGridCO.Proofs.', 'AvailableChainKit.',
                       'AvailableChainStatements.')) or dep == 'AvailableChainModel.Generic.Run':
        return False
    if L.under(m, CLAIMS) and L.is_proof(ctx, dep):
        return False
    if L.under(m, INHABIT) and L.under(dep, PROOFS):
        return False
    if owned(dep):
        return True  # check (e) and order below apply to every internal edge
    common = ('AvailableChainEngineV2.', 'AvailableChainFGSA.Model.',
              'AvailableChainFGSA.Statements.', 'AvailableChainFGSARun.Model.',
              'AvailableChainFGSARun.Statements.', 'AvailableChainGeneric.Statements.',
              'AvailableChainSimplexFG.', 'Mathlib.', 'Init.', 'Lean.', 'Std.')
    exact = {'AvailableChainModel.Objects.Identifiers', 'AvailableChainModel.Objects.Time',
             'AvailableChainModel.Objects.Blocks', 'AvailableChainModel.Objects.Codec',
             'AvailableChainModel.Generic.Env', 'AvailableChainGridCO.Model.Protocol',
             'AvailableChainGridCO.Model.Walk', 'AvailableChainSA.Model.Protocol'}
    if dep.startswith(common) or dep in exact or dep in ctx.definitions:
        return True
    return not L.under(m, CLAIMS) and dep.startswith((
        'AvailableChainKitV2.', 'AvailableChainKitFG.', 'AvailableChainFGSA.Proofs.',
        'AvailableChainFGSARun.Proofs.', 'AvailableChainGeneric.Proofs.'))

# O m4: the F2 constants are the declarations of Statements/CleanInvariant.
F2_NAMES = set(re.findall(r"(?m)^(?:def|structure|abbrev|theorem)\s+([A-Za-z_][A-Za-z0-9_']*)",
                          Path(PROOFS + '/Statements/CleanInvariant.lean').read_text()))

def source_findings(m, raw):
    imports, body = L.read_header(raw)
    owner = next(x for x in LIBS if L.under(m, x))
    item = L.Module(m, Path(m.replace('.', '/') + '.lean'), owner, m in LIBS, imports, body)
    findings = []
    for dep in imports:
        for rule, predicate in L.EDGE_RULES.items():
            if predicate(ctx, item, dep):
                findings.append(f'{rule}: {m} imports {dep}')
        if not direct_ok(m, dep):
            findings.append(f'IMPORT NOT ALLOWED: {m} imports {dep}')
        prefix = CLAIMS + '.Statements.'
        if m.startswith(prefix) and dep.startswith(prefix):
            left, right = m[len(prefix):], dep[len(prefix):]
            if left not in ORDER or right not in ORDER or ORDER.index(right) >= ORDER.index(left):
                findings.append(f'MODULE ORDER: {m} imports {dep}')
        if dep in (prefix + 'CleanInvariant', PROOFS + '.Statements.CleanInvariant') or dep.endswith('Internal'):
            lane = 'Clean' if dep.endswith('CleanInvariant') else 'Finality'
            if not m.startswith(PROOFS + '.Proofs.' + lane + '.'):
                findings.append(f'INTERNAL STATEMENT: {m} imports {dep}')
        if L.under(m, CLAIMS) and dep.startswith(PROOFS + '.Proofs.Clean.'):
            findings.append(f'CLEAN PROOF PATH: {m} imports {dep}')
    if L.under(m, CLAIMS):
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", C.strip(raw)):
            last = tok.split('.')[-1]
            if last in F2_NAMES and (tok == last or tok.endswith('Run.' + last)):
                findings.append(f'F2 CONSTANT: {m} names {tok}')
    if m in LIBS and body:
        findings.append(f'B7-BODY: {m}')
    clean = C.strip(raw)
    if re.search(r'\b(native_decide|sorry|admit|axiom)\b|\+native|native\s*:=\s*true|\bofReduce(?:Bool|Nat)\b', clean):
        findings.append(f'FORBIDDEN EVALUATION/AXIOM: {m}')
    if L.under(m, CLAIMS):
        lf = C.LeanFile(owner, str(item.path), m)
        lf._raw = raw
        decls = C.declarations(lf)
        defs = {d.full for d in decls if d.kind == 'def'}
        for d in decls:
            if d.kind in ('theorem', 'lemma') and not (
                m.startswith(CLAIMS + '.Statements.') and
                d.short.endswith('_def') and d.full[:-4] in defs
            ):
                findings.append(f'F-28: {m} {d.full}')
    if L.under(m, PROOFS) and not L.is_test(m) and m != PROOFS:
        if re.search(r'@\[[^]]*\bexpose\b', clean):
            findings.append(f'PROOF EXPOSE: {m}')
        if re.search(r'\b(theorem|lemma|def)\b', clean) and 'public section' not in clean:
            findings.append(f'PROOF PUBLIC SECTION: {m}')
    # Use T7's exact comment-aware V2-open parser, including quoted names,
    # multi-line opens, hiding, selective Auth/Signed, export and namespace.
    t7 = Path('scripts/check-fgsa-run.sh').read_text()
    parser = t7.split("v2_open='", 1)[1].split("'\ncheck_v2_open()", 1)[0]
    parsed = subprocess.run(['perl', '-CSD', '-e', parser], input=clean,
                            text=True, capture_output=True, check=True)
    if parsed.stdout:
        findings.append(f'V2 NAME CLASH: {m}: {parsed.stdout.strip()}')
    return findings

files = sources()
findings = [f for p in files for f in source_findings(module(p), p.read_text())]
if findings:
    print('\n'.join(findings))
    raise SystemExit(1)
if SOURCE_ONLY:
    result = subprocess.run(['python3', 'scripts/check-layers.py'])
    if result.returncode:
        raise SystemExit(result.returncode)
else:
    run('layers', ['python3', 'scripts/check-layers.py'])

def check_source_coverage(imports, roots):
    # Every production module must be in its root facade's transitive closure.
    def closure(starts):
        seen = set()
        pending = list(starts)
        while pending:
            m = pending.pop()
            if m in seen:
                continue
            seen.add(m)
            pending.extend(imports.get(m, ()))
        return seen

    # PhasesInternal is restricted to F4/Finality. The facade cannot import it.
    f4_only = {CLAIMS + '.Statements.PhasesInternal'}
    for lib in LIBS:
        seen = closure([lib])
        missing = [m for m in roots if L.under(m, lib) and not L.is_test(m) and m not in seen
                   and m not in f4_only]
        if missing:
            raise SystemExit('NOT IMPORTED BY ROOT: ' + ', '.join(missing))
    f4_tree = [m for m in roots if L.proof_path(m)[:1] in (('F4',), ('Finality',))]
    if f4_tree:
        seen = closure(f4_tree)
        unreached = sorted(m for m in f4_only if m in roots and m not in seen)
        if unreached:
            raise SystemExit('NOT REACHED FROM F4: ' + ', '.join(unreached))

if SOURCE_ONLY:
    source_edges = {module(p): L.read_header(p.read_text())[0] for p in files}
    check_source_coverage(source_edges, list(source_edges))
    print('FGSA Claims/Proofs/Inhabit source checks: PASS', flush=True)
    raise SystemExit(0)

# Independent source controls use the same policy function as the real scan.
controls = (
    ('statements-non-def-theorem', CLAIMS + '.Statements.Reads',
     'def fgsaControl : Nat := 0\ntheorem fgsaControl_eq : fgsaControl = 0 := rfl\n', 'F-28'),
    ('plain-v2-open', CLAIMS + '.Statements.Reads', 'open AvailableChain.V2\n', 'V2 NAME CLASH'),
    ('grid-proof-import', PROOFS + '.Proofs.Shared.Reads', 'public import AvailableChainGridCO.Proofs.Map\n', 'IMPORT NOT ALLOWED'),
    ('rightward-statement', CLAIMS + '.Statements.Reads', 'public import ' + CLAIMS + '.Statements.Counts\n', 'MODULE ORDER'),
    ('clean-proof-path', CLAIMS + '.Statements.Reads', 'public import ' + PROOFS + '.Proofs.Clean.Step\n', 'CLEAN PROOF PATH'),
    ('f2-constant-in-claim', CLAIMS + '.Claims.Clean',
     'public section\n'
     'def fgsaF2Control : Prop := ∀ (p : AvailableChain.FGSA.Params) '
     '(c : AvailableChain.FGSA.Run.AppCodec Unit) (E : AvailableChain.Generic.Env Unit) '
     '(rho : AvailableChain.V2.Run Unit (AvailableChain.FGSA.Run.fgsa p c)), '
     'AvailableChain.FGSA.Run.CleanHist p c E rho 0\n', 'F2 CONSTANT'),
    ('clean-invariant-import', PROOFS + '.Proofs.Outage.Step',
     'public import ' + PROOFS + '.Statements.CleanInvariant\n', 'INTERNAL STATEMENT'),
    ('claims-proof-import', CLAIMS + '.Claims.Clean', 'public import AvailableChainFGSARun.Proofs.ClientTrace\n', 'IMPORT NOT ALLOWED'),
    ('facade-tests', CLAIMS, 'public import ' + CLAIMS + '.Tests.Axioms\n', 'B7-TESTS'),
    ('cross-lane-proof', PROOFS + '.Proofs.Clean.Step', 'public import ' + PROOFS + '.Proofs.Outage.Step\n', 'LANE'),
    ('cross-lane-export', PROOFS + '.Proofs.Clean.Step', 'public import ' + PROOFS + '.Proofs.Outage.Export\n', 'EXPORT-USE'),
    ('shared-lane-proof', PROOFS + '.Proofs.Shared.Reads', 'public import ' + PROOFS + '.Proofs.Clean.Step\n', 'SHARED'),
    # SYN L58: direct_ok and the layer predicates apply together.
    ('assembly-control-facade', PROOFS + '.Proofs.Assembly.Control',
     'public import ' + CLAIMS + '.FGSAClaims\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-sibling-facade', PROOFS + '.Proofs.Assembly.RootExtra',
     'public import ' + CLAIMS + '.FGSAClaims\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-child-facade', L.ASSEMBLY_ROOT + '.Extra',
     'public import ' + CLAIMS + '.FGSAClaims\n', 'IMPORT NOT ALLOWED'),
    ('assembly-control-root', PROOFS + '.Proofs.Assembly.Control',
     'public import ' + L.ASSEMBLY_ROOT + '\n', 'ASSEMBLY'),
    ('assembly-root-claims-root', L.ASSEMBLY_ROOT,
     'public import ' + CLAIMS + '\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-proofs-root', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '\n', 'IMPORT NOT ALLOWED'),
    ('assembly-root-raw-lane', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Foundations.Store\n', 'ASSEMBLY'),
    ('assembly-root-lane-export', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Foundations.Export\n', 'ASSEMBLY'),
    ('assembly-root-unnamed-lower', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Assembly.Other\n', 'ASSEMBLY'),
    ('assembly-root-lower-child', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Proofs.Assembly.Foundations.Extra\n', 'ASSEMBLY'),
    ('assembly-root-tests', L.ASSEMBLY_ROOT,
     'public import ' + PROOFS + '.Tests.Axioms\n', 'ASSEMBLY'),
    ('assembly-root-inhabit', L.ASSEMBLY_ROOT,
     'public import ' + INHABIT + '.Control\n', 'ASSEMBLY'),
    ('assembly-root-field-claims', L.ASSEMBLY_ROOT,
     'public import ' + CLAIMS + '.Claims.Clean\n', 'CLAIM-USE'),
    ('proofs-root-shared-export', PROOFS,
     'public import ' + PROOFS + '.Proofs.Shared.Export\n', 'EXPORT-USE'),
    ('assembly-root-phases-internal', L.ASSEMBLY_ROOT,
     'public import ' + CLAIMS + '.Statements.PhasesInternal\n', 'INTERNAL STATEMENT'),
)
for label, m, body, expected in controls:
    hits = source_findings(m, 'module\n' + body)
    if not any(expected in f for f in hits):
        raise SystemExit(f'STOP: negative control passed: {label}: {hits}')
    print(f'{label}: rc 1, rejected as expected ({expected})', flush=True)

# SYN L58: each allowed edge must pass both direct_ok and every layer rule.
assembly_positives = (
    ('assembly-root-facade', L.ASSEMBLY_ROOT, CLAIMS + '.FGSAClaims'),
    ('assembly-root-foundations', L.ASSEMBLY_ROOT, PROOFS + '.Proofs.Assembly.Foundations'),
    ('assembly-root-shared', L.ASSEMBLY_ROOT, PROOFS + '.Proofs.Assembly.Shared'),
    ('assembly-root-clean', L.ASSEMBLY_ROOT, PROOFS + '.Proofs.Assembly.Clean'),
    ('assembly-root-foundation-import', L.ASSEMBLY_ROOT, 'Lean.Elab.Command'),
    ('proofs-root-assembly-root', PROOFS, L.ASSEMBLY_ROOT),
)
for label, m, dep in assembly_positives:
    hits = source_findings(m, 'module\npublic import ' + dep + '\n')
    if hits:
        raise SystemExit(f'STOP: positive control failed: {label}: {hits}')
    print(f'{label}: rc 0', flush=True)

# Future F4 coverage stays separate from facade coverage (SYN L58).
phase_internal = CLAIMS + '.Statements.PhasesInternal'
finality_control = PROOFS + '.Proofs.Finality.Control'
coverage_edges = {CLAIMS: (), PROOFS: (finality_control,), INHABIT: (),
                  phase_internal: (), finality_control: ()}
try:
    check_source_coverage(coverage_edges, list(coverage_edges))
except SystemExit as exc:
    if not str(exc).startswith('NOT REACHED FROM F4: '):
        raise
    print('missing-f4-reach: rc 1, rejected as expected (NOT REACHED FROM F4)', flush=True)
else:
    raise SystemExit('STOP: missing F4 reach control passed')
coverage_edges[finality_control] = (phase_internal,)
check_source_coverage(coverage_edges, list(coverage_edges))
print('f4-reach-twin: rc 0', flush=True)

# Positive twin of f2-constant-in-claim: the same Prop over a frozen Claims name passes.
twin_hits = [f for f in source_findings(CLAIMS + '.Claims.Clean', 'module\npublic section\n'
    'def fgsaF2Twin : Prop := ∀ (p : AvailableChain.FGSA.Params) '
    '(c : AvailableChain.FGSA.Run.AppCodec Unit) (E : AvailableChain.Generic.Env Unit) '
    '(rho : AvailableChain.V2.Run Unit (AvailableChain.FGSA.Run.fgsa p c)), '
    'AvailableChain.FGSA.Run.CleanTruncAt p c E rho 0\n') if f.startswith('F2 CONSTANT')]
if twin_hits:
    raise SystemExit(f'STOP: F2 constant positive twin failed: {twin_hits}')
print('f2-constant-twin: rc 0 (a frozen Claims name passes)', flush=True)

# The seven home equation theorems must pass the same source policy.
reads_path = Path(CLAIMS + '/Statements/Reads.lean')
positive_hits = source_findings(module(reads_path), reads_path.read_text())
if positive_hits:
    raise SystemExit(f'STOP: Statements _def positive case failed: {positive_hits}')
print('statements-home-def-theorems: rc 0 (seven matching _def theorems)', flush=True)

for lib in LIBS:
    run('build-' + lib, ['lake', 'build', '--wfail', lib])
    run('build-' + lib + 'Tests', ['lake', 'build', '--wfail', lib + 'Tests'])
run('support', ['lake', 'build', 'AvailableChainCheckSupport'])

# Derive a compiled-edge table only AFTER source policy validation. A built
# module may not contain an edge absent from its checked source. This also
# rejects stale .oleans. Every source module is imported as an audit root;
# root-facade coverage is checked separately below.
edges = [(module(p), L.read_header(p.read_text())[0]) for p in files]
assert CLAIMS + '.FGSAClaims' in dict(edges)[L.ASSEMBLY_ROOT]
print('compiled import table: SYN L58 Assembly.Root -> FGSAClaims included', flush=True)
edge_cases = '\n'.join('  | `' + m + ' => [' + ', '.join('`' + d for d in deps) + '].contains imp' for m, deps in edges)
allowed_import = 'def allowedImport (mod imp : Name) : Bool :=\n  imp == `Init || match mod with\n' + edge_cases + '\n  | _ => false\n\n'
source = Path('scripts/CheckFGSARunAxioms.lean').read_text()
source = source.replace('import AvailableChainFGSARun\n', ''.join('import ' + x + '\n' for x in LIBS), 1)
source = source.replace('def lib : Name := `AvailableChainFGSARun',
    'def libs : List Name := [' + ', '.join('`' + x for x in LIBS) + ']\n' +
    'def inLibraries (m : Name) : Bool := libs.any (·.isPrefixOf m)')
a = source.index('def allowedImport ('); b = source.index('/-- The module names', a)
source = source[:a] + allowed_import + source[b:]
source = source.replace('parts.foldl (fun n s => Name.str n s) lib', 'parts.foldl (fun n s => Name.str n s) dir.fileName.get!.toName')
source = source.replace('lib.isPrefixOf m', 'inLibraries m')
source = source.replace('let mut dir : System.FilePath := "AvailableChainFGSARun"', 'let mut dir : System.FilePath := ""')
source = source.replace('(#[lib] ++ extra)', '(libs.toArray ++ extra)')
source = source.replace('  for m in ← sourceModules dir do',
    '  let dirs := if dir.toString.isEmpty then libs.map (fun n => System.FilePath.mk n.toString) else [dir]\n' +
    '  let mut sourceMods := #[]\n  for d in dirs do sourceMods := sourceMods ++ (← sourceModules d)\n' +
    '  for m in sourceMods do')
source = source.replace('  if cs.isEmpty then\n    IO.eprintln "NO CONSTANTS FOUND"\n    return 2\n',
    '  -- Empty libraries are valid only with successful source/build coverage.\n')
# Change only the generated claims auditor. The T7 template and its users
# keep their existing behavior. Each call has a fresh CoreM state; tasks
# share the imported, read-only Environment and return data without output.
parallel_axioms = '''def auditWorkerCount : IO Nat := do
  let mut count := 2
  for key in ["AUDIT_WORKERS", "LEAN_SLOTS", "GATE_SLOTS"] do
    if let some value ← IO.getEnv key then
      let some n := value.toNat? | throw (IO.userError s!"{key} must be a positive integer")
      if n == 0 then throw (IO.userError s!"{key} must be a positive integer")
      if key == "AUDIT_WORKERS" then count := n else count := min count n
  if (← IO.getEnv "AUDIT_SERIAL") == some "1" then return 1
  return min count ((← IO.getEnv "LEAN_SLOTS").bind String.toNat? |>.getD 3)

def auditAxiomChunk (env : Environment) (chunk : Array (Nat × Name)) :
    IO (Array (Nat × Name × Array Name)) := do
  let mut rows := #[]
  for (i, n) in chunk do
    let bad := (← axiomsOf env n).filter (fun a => !allowed.contains a)
    unless bad.isEmpty do rows := rows.push (i, n, bad)
  return rows

def auditAxioms (env : Environment) (names : Array Name) :
    IO (Array (Nat × Name × Array Name)) := do
  let workers ← auditWorkerCount
  let indexed := names.mapIdx fun i n => (i, n)
  if workers == 1 then return ← auditAxiomChunk env indexed
  let size := (names.size + workers - 1) / workers
  let mut tasks := #[]
  for i in [:workers] do
    let chunk := (indexed.toList.drop (i * size) |>.take size).toArray
    unless chunk.isEmpty do tasks := tasks.push (← IO.asTask (auditAxiomChunk env chunk))
  let mut rows := #[]
  let mut error : Option IO.Error := none
  -- Join every task before propagating a failure.
  for task in tasks do
    match (← IO.wait task) with
    | .ok result => rows := rows ++ result
    | .error e => if error.isNone then error := some e
  if let some e := error then throw e
  -- Original ordinals preserve the serial diagnostic order byte for byte.
  return rows.qsort (fun a b => a.1 < b.1)

'''
source = source.replace('def main (args : List String)', parallel_axioms + 'def main (args : List String)', 1)
serial_loop = '''  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
'''
assert source.count(serial_loop) == 1, 'STOP: claims axiom loop changed'
source = source.replace(serial_loop, '''  let axiomRows ← auditAxioms env (cs.map Prod.fst).toArray
  for (_, n, bad) in axiomRows do
    IO.println s!"BAD AXIOMS {n}: {bad}"
    badAxioms := true
''', 1)
# P10/Q-10: each theorem in a lane Export has a matching Claims/<Lane>
# proposition as its type head (after binders). Helpers belong in lane files.
anchor = '  let mut badAxioms := false\n'
source = source.replace(anchor, anchor + '''  for (n, ci) in cs do
    let some m := moduleOf env n | continue
    let parts := m.components.map (·.toString)
    if parts.length == 4 && parts[0]! == "AvailableChainFGSAProofs" &&
        parts[1]! == "Proofs" && parts[3]! == "Export" then
      if ci matches .thmInfo _ then
        let head := ci.type.getForallBody.getAppFn
        let claimModule := ("AvailableChainFGSAClaims.Claims." ++ parts[2]!).toName
        unless head.constName?.any (fun c => moduleOf env c == some claimModule) do
          IO.println s!"EXPORT CLAIM TYPE: {n} must prove a Prop of {claimModule}"
          badAxioms := true
''')
audit = work / 'CheckClaimsAxioms.lean'
audit.write_text(source)
lease = Path('scripts/CheckFGSARunLease.lean').read_text()
lease = lease.replace('import AvailableChainFGSARun\n', ''.join('import ' + x + '\n' for x in LIBS), 1)
lease = lease.replace('let roots := `AvailableChainFGSARun :: extra',
    'let roots := [' + ', '.join('`' + x for x in LIBS) + '] ++ extra')
lease = lease.replace('  if cs.isEmpty then\n    IO.eprintln "NO CONSTANTS FOUND"\n    return 2\n', '')
lease_file = work / 'CheckClaimsLease.lean'
lease_file.write_text(lease)
roots = [module(p) for p in files]
args = ['lake', 'env', 'lean', '--run', str(audit)]
for m in roots:
    args += ['--root', m]
if EXPECTED:
    args += ['--expect', *EXPECTED]
run('axioms-coverage-used-constants', args)
run('lease', ['lake', 'env', 'lean', '--run', str(lease_file), *roots])

# Every production module must be in its root facade's transitive closure.
# Importing all modules for the audit above cannot mask a missing facade edge.
# J3 STOP A (lead ruling 2026-09-30): PhasesInternal may be imported only by the
# F4 tree (the INTERNAL STATEMENT edge rule above), so the Claims facade cannot
# reach it. It stays in the source and compiled audit roots. Once an F4-tree
# module exists, it must reach PhasesInternal instead.
check_source_coverage(dict(edges), roots)
run('proof-eqns', ['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
                   '--baseline', 'scripts/baselines/check-proof-eqns.txt'])
run('unused-imports', ['bash', 'scripts/shake-report.sh', '--fail-on-new', *roots])

# The gate's merge tier sets NEG=0: it skips the compiled negative controls
# below (about 135 s on the NUC), as the other check scripts do.
if os.environ.get('NEG', '1') == '0':
    print('compiled negative controls: SKIPPED (NEG=0)', flush=True)
    print('all FGSA claims checks pass (NEG=0: no compiled negative controls)', flush=True)
    raise SystemExit(0)

# Compiled negative controls. They are never added to the real library.
# Use the real auditor and require its diagnostic, not merely a Lean error.
control_path = run('control-lean-path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
controls = []

def control_dir(label, *, shadow=False):
    neg = work / 'controls' / label
    neg.mkdir(parents=True)
    # A tiny offline Lake package: no dependencies or fetch step.
    (neg / 'lean-toolchain').write_text(Path('lean-toolchain').read_text())
    (neg / 'lakefile.toml').write_text('name = "fgsa-controls"\n[[lean_lib]]\nname = "FGSAControl"\nglobs = ["FGSAControl.+"]\n')
    if shadow:
        # Lean resolves an entire prefix at its first path entry. Each
        # auditor gets private built roots and only its own shadow module.
        built = ROOT / '.lake/build/lib/lean'
        for lib in LIBS:
            shutil.copytree(built / lib, neg / lib)
            for p in built.glob(lib + '.*'):
                if p.is_file():
                    shutil.copy2(p, neg / p.name)
    return neg

def shadow_env(neg):
    return dict(os.environ, LEAN_PATH=str(neg) + os.pathsep + control_path)

def run_shadow(label, args, *, expect=None):
    return run(label, ['lake', 'env', 'lean', *args], expect=expect,
               env=shadow_env(neg), cwd=neg)

def queue_shadow(label, args, *, expect):
    controls.append((label, ['lake', 'env', 'lean', *args],
                     dict(expect=expect, env=shadow_env(neg), cwd=neg)))

def write_module(name, text):
    p = neg / (name.replace('.', '/') + '.lean')
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    return p

def compile_module(name, text):
    p = write_module(name, text)
    run_shadow('compile-' + name.split('.')[-1],
               ['-o', str(p.with_suffix('.olean')), str(p)])
    return p

bad = PROOFS + '.Proofs.Shared.NegUse'
neg = control_dir('grid-constant-in-statement', shadow=True)
compile_module(bad, '''module
public import AvailableChainGridCO.Proofs.Map
public import AvailableChainKit.Engine.EngineClock
public section
namespace AvailableChain.FGSA.Run
def negKitClock {n : Nat} (P : AvailableChain.Generic.ProtocolSpec n) : Type :=
  AvailableChain.Engine.ClockLaws P
def negStatements : Type := AvailableChain.Statements.Generic.Constants
theorem negGridStatement {n : Nat} (st : AvailableChain.GridCO.State n)
    (h : AvailableChain.GridCO.ComparableTargets st) :
    AvailableChain.GridCO.ComparableTargets st := h
end AvailableChain.FGSA.Run
end
''')
queue_shadow('grid-constant-in-statement', ['--run', str(audit), '--root', bad],
    expect='FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negGridStatement uses AvailableChain.GridCO.ComparableTargets')
# The controls have the same FG-SA namespace and upstream reachability as T7.
lease_bad = PROOFS + '.Proofs.Shared.NegLease'
neg = control_dir('default-lease', shadow=True)
compile_module(lease_bad, '''module
public import AvailableChainFGSA.Model.Clock
public section
namespace AvailableChain.FGSA.Run
def negLease (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) :
    AvailableChain.GridCO.State 1 := AvailableChain.GridCO.gate p st 0
end AvailableChain.FGSA.Run
end
''')
queue_shadow('default-lease', ['--run', str(lease_file), lease_bad], expect='BAD LEASE INSTANCE')

# SYN L58: replace one ordinary Assembly .olean in the scratch copy only.
# The generated table still contains its validated, unchanged source edges.
assembly_bad = PROOFS + '.Proofs.Assembly.Foundations'
neg = control_dir('assembly-facade-compiled-import', shadow=True)
assembly_text = Path(assembly_bad.replace('.', '/') + '.lean').read_text()
compile_module(assembly_bad, assembly_text.replace(
    'module\n', 'module\npublic import ' + CLAIMS + '.FGSAClaims\n', 1))
queue_shadow('assembly-facade-compiled-import', ['--run', str(audit), '--root', assembly_bad],
    expect='COMPILED IMPORT NOT ALLOWED: ' + assembly_bad +
    ' imports ' + CLAIMS + '.FGSAClaims')

neg = control_dir('control-build')
write_module('FGSAControl.Statements.Fn', '''module
@[expose] public section
def fgsaControlFn : Bool → Nat
  | true => 1
  | false => 0
end
''')
write_module('FGSAControl.Proofs.NegEq', '''module
public import FGSAControl.Statements.Fn
public section
theorem fgsaControlEq : fgsaControlFn true = 1 := by simp [fgsaControlFn]
end
''')
write_module('FGSAControl.NegUnused', '''module
public import Init.Data.List.Sort
public section
def fgsaControlUnused : Nat := 0
end
''')
run('control-build', ['lake', 'build', 'FGSAControl'], cwd=neg)
# CheckProofEqns reads repository-relative inputs as well as its baseline.
# This extra module has a unique prefix, so Lake's path order needs no shadow.
simp_dir = work / 'controls' / 'simp-without-f-def'
unused_dir = work / 'controls' / 'unused-import-control'
shutil.copytree(neg, simp_dir)
shutil.copytree(neg, unused_dir)
control_env = dict(os.environ, LEAN_PATH=str(simp_dir / '.lake/build/lib/lean'))
controls.append(('simp-without-f-def', ['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
    '--baseline', 'scripts/baselines/check-proof-eqns.txt', 'FGSAControl.Proofs.NegEq'],
    dict(env=control_env, expect='EQ EXPORT FGSAControl.Proofs.NegEq')))
# Use the same --fail-on-new baseline comparison as the real D47 scan.
# shake-report reads its package from cwd only via its cd, so obtain Lake's
# raw report here, then apply the same removal key and frozen baseline.
controls.append(('unused-import-control', ['lake', 'shake', 'FGSAControl.NegUnused'],
                 dict(cwd=unused_dir, expect='remove #[public import Init.Data.List.Sort]')))
run_pool(controls)
key = 'remove FGSAControl/NegUnused.lean public import Init.Data.List.Sort'
if C.read_baseline('shake-report')[key]:
    raise SystemExit('STOP: unused-import control is in the baseline')
print('unused-import baseline comparison: rc 1 (NEW removal), rejected as expected', flush=True)
print('all FGSA claims checks pass', flush=True)
PY
