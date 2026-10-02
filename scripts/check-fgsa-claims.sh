#!/usr/bin/env bash
# P3 F0.0b: Claims, Proofs and Inhabit guard. The compiled auditors below
# adapt the CURRENT T7.1 auditors, including their generated-owner rules.
# No baseline is written. Fixtures and audit logs stay under .lake.
# SOURCE_ONLY=1 runs source findings and facade/F4 coverage, without controls or Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PY'
from pathlib import Path
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
    'AvailableChain.FGSA.Run.fgsa_eligible_eq_of_same_floor',
    'AvailableChain.FGSA.Run.fgsa_eligible_eq_of_parent_height',
    'AvailableChain.FGSA.Run.fgsa_score_geometry_of_domains',
    'AvailableChain.FGSA.Run.fgsa_score_eq_on_candidates_on_run',
    'AvailableChain.FGSA.Run.fgsa_retained_scores_of_candidates',
    'AvailableChain.FGSA.Run.RetainedWalkRunGeometry',
    'AvailableChain.FGSA.Run.RetainedEndpointGeometry',
    'AvailableChain.FGSA.Run.fgsa_Z_preceq_liveRoot',
    'AvailableChain.FGSA.Run.fgsa_retained_prefix_of_trunk_or_support',
    'AvailableChain.FGSA.Run.fgsa_walk_domain_of_witness',
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
    'AvailableChain.FGSA.Run.HTimeBestStatement',
    'AvailableChain.FGSA.Run.HTimeBestStatement_def',
    'AvailableChain.FGSA.Run.HTimeSearchStatement',
    'AvailableChain.FGSA.Run.HTimeSearchStatement_def',
    'AvailableChain.FGSA.Run.TStart',
    'AvailableChain.FGSA.Run.FullVoteService',
    'AvailableChain.FGSA.Run.TVote',
    'AvailableChain.FGSA.Run.WalkBatch',
    'AvailableChain.FGSA.Run.TWalk',
    'AvailableChain.FGSA.Run.CoreServices',
    'AvailableChain.FGSA.Run.PhaseKind',
    'AvailableChain.FGSA.Run.AttemptTask',
    'AvailableChain.FGSA.Run.AttemptKey',
    "AvailableChain.FGSA.Run.B'_reset",
    'AvailableChain.FGSA.Run.ResetArrivalStatement',
    'AvailableChain.FGSA.Run.ResetArrivalStatement_def',
    'AvailableChain.FGSA.Run.ResetArrivalFullStatement',
    'AvailableChain.FGSA.Run.ResetArrivalFullStatement_def',
    'AvailableChain.FGSA.Run.KernelConclusion',
    'AvailableChain.FGSA.Run.KernelPt',
    'AvailableChain.FGSA.Run.KernelPrem',
    'AvailableChain.FGSA.Run.KernelFromContract',
    'AvailableChain.FGSA.Run.KernelACSide',
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
    'AvailableChain.FGSA.Run.finalityWindow',
    'AvailableChain.FGSA.Run.FirstFinalityPrem',
    'AvailableChain.FGSA.Run.FinalityLivenessPrem',
    'AvailableChain.FGSA.Run.ProposalFinalPrem',
    'AvailableChain.FGSA.Run.AboveFrontierPrem',
    'AvailableChain.FGSA.Run.QualifiedFinalityPrem',
    'AvailableChain.FGSA.Run.SkipFinalityPrem',
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
    'AvailableChain.FGSA.Run.FinalitySet',
    'AvailableChain.FGSA.Run.WinSpec',
    'AvailableChain.FGSA.Run.PtB₀',
    'AvailableChain.FGSA.Run.PtT',
    'AvailableChain.FGSA.Run.PtOut',
    'AvailableChain.FGSA.Run.cleanWinAt',
    'AvailableChain.FGSA.Run.cleanWin',
    'AvailableChain.FGSA.Run.cleanPrefixWin',
    'AvailableChain.FGSA.Run.cleanLabelWin',
    'AvailableChain.FGSA.Run.gapWin',
    'AvailableChain.FGSA.Run.formWin',
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
    'AvailableChain.FGSA.Run.B_Q',
    'AvailableChain.FGSA.Run.B_skip',
    'AvailableChain.FGSA.Run.γ',
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
    'AvailableChain.FGSA.Run.FirstCross',
    'AvailableChain.FGSA.Run.ProposalWalk',
    'AvailableChain.FGSA.Run.finHeight',
    'AvailableChain.FGSA.Run.FreshPrem',
    'AvailableChain.FGSA.Run.fgsa_rowBitPersist',
    'AvailableChain.FGSA.Run.fgsa_rowService_receipt',
    'AvailableChain.FGSA.Run.validForParent_heightMatch',
    'AvailableChain.FGSA.Run.fgsa_tRowsSelect',
    'AvailableChain.FGSA.Run.fgsa_rowsReceipt_carriage',
    'AvailableChain.FGSA.Run.fgsa_tRowsReceipt',
    'AvailableChain.FGSA.Run.fgsa_tRowsSync',
    'AvailableChain.FGSA.Run.fgsa_tRows',
    'AvailableChain.FGSA.Run.fgsa_rowServiceBaseClaim',
    'AvailableChain.FGSA.Run.fgsa_rowServiceClaim',
    'AvailableChain.FGSA.Run.fgsa_rowsValidStored_atProposal',
    'AvailableChain.FGSA.Run.fgsa_batchCoverage',
)
ORDER = ('Recurrence', 'Bounds', 'Reads', 'Counts', 'Regimes', 'Windows',
         'Packages.Safety', 'Packages.Outage', 'Channels', 'Witness',
         'ChannelProps', 'Healed', 'Packages.Finality', 'ComposeStmt', 'Fold',
         'Phases', 'PhasesInternal', 'Packages.Healing')
if not SOURCE_ONLY:
    work = Path(tempfile.mkdtemp(prefix='fgsa-claims-check.', dir=ROOT / '.lake'))
    print(f'FGSA claims audit logs: {work}', flush=True)
serial = 0

def run(label, args, *, expect=None, env=None, cwd=None):
    global serial
    serial += 1
    path = work / f'{serial:02d}-{label}.log'
    with path.open('w') as out:
        proc = subprocess.run(args, stdout=out, stderr=subprocess.STDOUT,
                              env=env, cwd=cwd)
    output = path.read_text()
    print(f'{label}: rc {proc.returncode} ({path.name})', flush=True)
    if expect is None:
        if proc.returncode:
            print(output)
            raise SystemExit(proc.returncode)
    elif proc.returncode == 0 or expect not in output:
        print(output)
        raise SystemExit(f'STOP: negative control {label} did not fail with {expect!r}')
    else:
        print(f'rejected, as expected: {label}', flush=True)
    return output

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
neg = work / 'controls'
neg.mkdir()
# Lean resolves an entire module prefix at the first search-path entry.
# Copy the built roots too, as the current T7 negative controls do.
for lib in LIBS:
    built = ROOT / '.lake/build/lib/lean'
    shutil.copytree(built / lib, neg / lib)
    for p in built.glob(lib + '.*'):
        if p.is_file():
            shutil.copy2(p, neg / p.name)

# A tiny offline Lake package lets the controls use lake env lean and lets
# shake read their build traces. It has no dependencies or fetch step.
(neg / 'lean-toolchain').write_text(Path('lean-toolchain').read_text())
(neg / 'lakefile.toml').write_text('name = "fgsa-controls"\n[[lean_lib]]\nname = "FGSAControl"\nglobs = ["FGSAControl.+"]\n')
negative_env = dict(os.environ, LEAN_PATH=str(neg) + os.pathsep +
    run('control-lean-path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip())

def run_shadow(label, args, *, expect=None):
    return run(label, ['lake', 'env', 'lean', *args], expect=expect,
               env=negative_env, cwd=neg)

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
run_shadow('grid-constant-in-statement', ['--run', str(audit), '--root', bad],
    expect='FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negGridStatement uses AvailableChain.GridCO.ComparableTargets')
# The controls have the same FG-SA namespace and upstream reachability as T7.
lease_bad = PROOFS + '.Proofs.Shared.NegLease'
compile_module(lease_bad, '''module
public import AvailableChainFGSA.Model.Clock
public section
namespace AvailableChain.FGSA.Run
def negLease (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) :
    AvailableChain.GridCO.State 1 := AvailableChain.GridCO.gate p st 0
end AvailableChain.FGSA.Run
end
''')
run_shadow('default-lease', ['--run', str(lease_file), lease_bad], expect='BAD LEASE INSTANCE')

# SYN L58: replace one ordinary Assembly .olean in the scratch copy only.
# The generated table still contains its validated, unchanged source edges.
assembly_bad = PROOFS + '.Proofs.Assembly.Foundations'
assembly_text = Path(assembly_bad.replace('.', '/') + '.lean').read_text()
compile_module(assembly_bad, assembly_text.replace(
    'module\n', 'module\npublic import ' + CLAIMS + '.FGSAClaims\n', 1))
run_shadow('assembly-facade-compiled-import', ['--run', str(audit), '--root', assembly_bad],
    expect='COMPILED IMPORT NOT ALLOWED: ' + assembly_bad +
    ' imports ' + CLAIMS + '.FGSAClaims')

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
control_env = dict(os.environ, LEAN_PATH=str(neg / '.lake/build/lib/lean'))
run('simp-without-f-def', ['lake', 'env', 'lean', '--run', 'scripts/CheckProofEqns.lean',
    '--baseline', 'scripts/baselines/check-proof-eqns.txt', 'FGSAControl.Proofs.NegEq'],
    env=control_env, expect='EQ EXPORT FGSAControl.Proofs.NegEq')
# Use the same --fail-on-new baseline comparison as the real D47 scan.
# shake-report reads its package from cwd only via its cd, so obtain Lake's
# raw report here, then apply the same removal key and frozen baseline.
out = run('unused-import-control', ['lake', 'shake', 'FGSAControl.NegUnused'],
          cwd=neg, expect='remove #[public import Init.Data.List.Sort]')
key = 'remove FGSAControl/NegUnused.lean public import Init.Data.List.Sort'
if C.read_baseline('shake-report')[key]:
    raise SystemExit('STOP: unused-import control is in the baseline')
print('unused-import baseline comparison: rc 1 (NEW removal), rejected as expected', flush=True)
print('all FGSA claims checks pass', flush=True)
PY
