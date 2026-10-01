module
public import AvailableChainFGSAProofs.Proofs.Shared.HeadCover -- shake: keep (F1b.4a axiom audit)
public import AvailableChainFGSAProofs.Proofs.Clean.GateOutput -- shake: keep (gate output axiom audit)
public import AvailableChainFGSAProofs.Proofs.Clean.Transfer -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Clean.TransferFrame -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Clean.StepGate -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Clean.Action -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Clean.Frame -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Relay -- shake: keep (relay axiom audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Count -- shake: keep (F1b.1 axiom audit)
public import AvailableChainFGSAProofs.Proofs.Assembly.Shared -- shake: keep (F1b.3 export axiom audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Release -- shake: keep (F1b.3 axiom audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.Counts -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.Cap -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalizedSafety -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Assembly.Foundations -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.Certificates -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.Client -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Gate -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Compose -- shake: keep (public aliases or axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Healed -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Channels -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Recurrence -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (axiom audit commands)

public import AvailableChainFGSAProofs.Proofs.Clean.Chain -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Clean.State -- shake: keep (axiom audit commands)
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate -- shake: keep (axiom audit commands)

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

#print axioms AvailableChain.FGSA.Run.Outage₂.pos
#print axioms AvailableChain.FGSA.Run.Outage₂.toCleanCut
#print axioms AvailableChain.FGSA.Run.Outage₂.faultQ
#print axioms AvailableChain.FGSA.Run.fgSource_eq_jointSource
#print axioms AvailableChain.FGSA.Run.ancestorClosed_preceq
#print axioms AvailableChain.FGSA.Run.ancestorClosed_compatible
#print axioms AvailableChain.FGSA.Run.srcFrame_genesis_preceq
#print axioms AvailableChain.FGSA.Run.srcFrame_genesis_compatible
#print axioms AvailableChain.FGSA.Run.propose_head
#print axioms AvailableChain.FGSA.Run.frameR_congr_fg
#print axioms AvailableChain.FGSA.Run.domainR_congr_fg
#print axioms AvailableChain.FGSA.Run.frame_postClock
#print axioms AvailableChain.FGSA.Run.eligible_lo_live
#print axioms AvailableChain.FGSA.Run.jointSelections_record_irrel
#print axioms AvailableChain.FGSA.Run.rowSigner_iff_holder
#print axioms AvailableChain.FGSA.Run.emit_lt_handles

#print axioms AvailableChain.FGSA.Run.clientSafety_base
#print axioms AvailableChain.FGSA.Run.cleanHistory_of_cut
#print axioms AvailableChain.FGSA.Run.cleanPrefixTruncation_of_cut
#print axioms AvailableChain.FGSA.Run.cleanSafety_outputs

#print axioms AvailableChain.FGSA.Run.fgsa_rStore
#print axioms AvailableChain.FGSA.Run.fgsa_store_cumulative
#print axioms AvailableChain.FGSA.Run.fgsa_rStoreCumul
#print axioms AvailableChain.FGSA.Run.fgsa_rMono
#print axioms AvailableChain.FGSA.Run.fgsa_storeAt
#print axioms AvailableChain.FGSA.Run.fgsa_storeClaim
#print axioms AvailableChain.FGSA.Run.fgsa_rFrameExact
#print axioms AvailableChain.FGSA.Run.fgsa_rActive
#print axioms AvailableChain.FGSA.Run.fgsa_activeViewAt
#print axioms AvailableChain.FGSA.Run.fgsa_activeViewClaim
#print axioms AvailableChain.FGSA.Run.fgsa_rCarrierView
#print axioms AvailableChain.FGSA.Run.fgsa_rFrame
#print axioms AvailableChain.FGSA.Run.fgsa_frameAt
#print axioms AvailableChain.FGSA.Run.fgsa_frameClaim
#print axioms AvailableChain.FGSA.Run.fgsa_seed_stored
#print axioms AvailableChain.FGSA.Run.fgsa_seed_bounds
#print axioms AvailableChain.FGSA.Run.fgsa_rGeo
#print axioms AvailableChain.FGSA.Run.fgsa_rCert
#print axioms AvailableChain.FGSA.Run.fgsa_chainCertificatesAt
#print axioms AvailableChain.FGSA.Run.fgsa_chainCertificatesClaim

#print axioms AvailableChain.FGSA.Run.fgsa_storedTargetsBelowOutput
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOrigins_chain
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOrigins_ancestorDeadlines
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOrigins_fastWrites
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_tSrc
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_labelBound
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_emittedName
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_base
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_qcOrigin
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_strat
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_at
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_srcFrameAbove
#print axioms AvailableChain.FGSA.Run.fgsa_rRec
#print axioms AvailableChain.FGSA.Run.fgsa_reconcileAt
#print axioms AvailableChain.FGSA.Run.fgsa_reconcileClaim
#print axioms AvailableChain.FGSA.Run.fgsa_carrierAt
#print axioms AvailableChain.FGSA.Run.fgsa_carrierClaim
#print axioms AvailableChain.FGSA.Run.held_chain_row_origin
#print axioms AvailableChain.FGSA.Run.fgsa_carrier_geometry
#print axioms AvailableChain.FGSA.Run.fgsa_finalLock
#print axioms AvailableChain.FGSA.Run.fgsa_finalLock_erased
#print axioms AvailableChain.FGSA.Run.fgsa_clientSafeAll
#print axioms AvailableChain.FGSA.Run.fgsa_clientSafetyClaim
#print axioms AvailableChain.FGSA.Run.fgsa_clientSafetyBaseClaim
#print axioms AvailableChain.FGSA.Run.honest_one_row_per_round

#print axioms AvailableChain.FGSA.Run.fgsa_slashable_faulty_count
#print axioms AvailableChain.FGSA.Run.fgsa_accountable
#print axioms AvailableChain.FGSA.Run.fgsa_finalLock_ev
#print axioms AvailableChain.FGSA.Run.fgsa_finalizedSafety
#print axioms AvailableChain.FGSA.Run.fgsa_gate_of_coveringBatch
#print axioms AvailableChain.FGSA.Run.fgsa_S_eq_of_exact
#print axioms AvailableChain.FGSA.Run.openingSource_extends_served
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

#print axioms AvailableChain.FGSA.Run.fgsa_leaseOrigins_writeLabel
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOrigins_lastWrite
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOrigins_origins
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOriginsAt
#print axioms AvailableChain.FGSA.Run.fgsa_leaseOriginsClaim
#print axioms AvailableChain.FGSA.Run.fgsa_sourceDisciplineBaseClaim
#print axioms AvailableChain.FGSA.Run.fgsa_sourceDisciplineClaim
#print axioms AvailableChain.FGSA.Run.fgsa_srcFrameAboveClaim

#print axioms AvailableChain.FGSA.Run.fgsa_fgFoundationClaim
#print axioms AvailableChain.FGSA.Run.fgsa_faultX_of_count
#print axioms AvailableChain.FGSA.Run.fgsa_faultQ_of_count
#print axioms AvailableChain.FGSA.Run.fgsa_target_exact_quorum
#print axioms AvailableChain.FGSA.Run.Recovery₂.faultX
#print axioms AvailableChain.FGSA.Run.Recovery₂.faultQ
#print axioms AvailableChain.FGSA.Run.fgsa_rCap
#print axioms AvailableChain.FGSA.Run.fgsa_finalityCap
#print axioms AvailableChain.FGSA.Run.fgsa_rCap_time
#print axioms AvailableChain.FGSA.Run.fgsa_rCap_before
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLag

#print axioms AvailableChain.FGSA.Run.openingSource_eq_of_no_strict_extension

#print axioms AvailableChain.FGSA.Run.FGFinalizedAt

#print axioms AvailableChain.FGSA.Run.FinalityRunBlock

#print axioms AvailableChain.FGSA.Run.finalityStoreRows

#print axioms AvailableChain.FGSA.Run.FinalityCarriage

#print axioms AvailableChain.FGSA.Run.fgsa_pureAccountable

#print axioms AvailableChain.FGSA.Run.fgsa_pureAgreement

#print axioms AvailableChain.FGSA.Run.FGWholeRunAccountable

#print axioms AvailableChain.FGSA.Run.fgsa_wholeRunAccountable

#print axioms AvailableChain.FGSA.Run.FGSASlashableBound

#print axioms AvailableChain.FGSA.Run.fgsa_wholeRunAgreement

#print axioms AvailableChain.FGSA.Run.fgsa_eventPrefixAgreement

#print axioms AvailableChain.FGSA.Run.fgsa_storeSlashableBound_of_faults

#print axioms AvailableChain.FGSA.Run.fgsa_slashableBound_of_faults

#print axioms AvailableChain.FGSA.Run.fgsa_finalLock_faulty_count

#print axioms AvailableChain.FGSA.Run.fgsa_accountable_base

#print axioms AvailableChain.FGSA.Run.fgsa_unforgeable_of_base

#print axioms AvailableChain.FGSA.Run.held_chain_row_origin_delivery

#print axioms AvailableChain.FGSA.Run.held_chain_row_origin_before

#print axioms AvailableChain.FGSA.Run.fgsa_outputNestingAt

#print axioms AvailableChain.FGSA.Run.fgsa_outputNestingClaim

#print axioms AvailableChain.FGSA.Run.fgsa_tSrc

#print axioms AvailableChain.FGSA.Run.fgsa_labelBound

#print axioms AvailableChain.FGSA.Run.fgsa_timingContract

#print axioms AvailableChain.FGSA.Run.fgsa_finalityStoreRows_contains
#print axioms AvailableChain.FGSA.Run.fgsa_finalizedMonotone

#print axioms AvailableChain.FGSA.Run.stored_block_wire_delivery
#print axioms AvailableChain.FGSA.Run.stored_chain_row_origin_delivery
#print axioms AvailableChain.FGSA.Run.carried_rows_carriage
#print axioms AvailableChain.FGSA.Run.delivered_runBlock_carriage
#print axioms AvailableChain.FGSA.Run.proposalRows_source
#print axioms AvailableChain.FGSA.Run.store_wire_origin
#print axioms AvailableChain.FGSA.Run.emitted_runBlock_carriage
#print axioms AvailableChain.FGSA.Run.fgsa_runBlock_carriage
#print axioms AvailableChain.FGSA.Run.fgsa_slashableBound_of_base
#print axioms AvailableChain.FGSA.Run.fgsa_storeSlashableBound_of_base
#print axioms AvailableChain.FGSA.Run.fgsa_eventPrefixAgreement_of_bound
#print axioms AvailableChain.FGSA.Run.fgsa_finalLock_of_bound

#print axioms AvailableChain.FGSA.Run.FGSASlashableBound_def
#print axioms AvailableChain.FGSA.Run.cleanResults_eq_of_noGate
#print axioms AvailableChain.FGSA.Run.cleanHist_step_of_noGate
#print axioms AvailableChain.FGSA.Run.cleanHist_step_delivery
#print axioms AvailableChain.FGSA.Run.cleanHist_step_noGateTick
#print axioms AvailableChain.FGSA.Run.clean_delivery_fields
#print axioms AvailableChain.FGSA.Run.clean_block_reconcile
#print axioms AvailableChain.FGSA.Run.clean_noGate_fields
#print axioms AvailableChain.FGSA.Run.cleanState_index_facts
#print axioms AvailableChain.FGSA.Run.clean_gate_raw
#print axioms AvailableChain.FGSA.Run.clean_gate_store
#print axioms AvailableChain.FGSA.Run.clean_state_gate_guard
#print axioms AvailableChain.FGSA.Run.clean_gate_passed
#print axioms AvailableChain.FGSA.Run.clean_gate_writes
#print axioms AvailableChain.FGSA.Run.clean_gate_lease_targets
#print axioms AvailableChain.FGSA.Run.clean_gate_fast_prefix
#print axioms AvailableChain.FGSA.Run.clean_gate_output_compatible
#print axioms AvailableChain.FGSA.Run.clean_gate_sExtends
#print axioms AvailableChain.FGSA.Run.clean_gate_leases
#print axioms AvailableChain.FGSA.Run.clean_gate_saved
#print axioms AvailableChain.FGSA.Run.clean_gate_savedOnly
#print axioms AvailableChain.FGSA.Run.clean_gate_fastAt
#print axioms AvailableChain.FGSA.Run.clean_gate_sOrigin
#print axioms AvailableChain.FGSA.Run.clean_gate_fastWrite

#print axioms AvailableChain.FGSA.Run.CleanRowSources_def
#print axioms AvailableChain.FGSA.Run.CleanCertSources_def
#print axioms AvailableChain.FGSA.Run.CleanStateStep_def
#print axioms AvailableChain.FGSA.Run.CleanHistStep_def
#print axioms AvailableChain.FGSA.Run.CleanOrdinaryDelivery_def
#print axioms AvailableChain.FGSA.Run.CleanBlockDelivery_def
#print axioms AvailableChain.FGSA.Run.CleanNoGateTick_def
#print axioms AvailableChain.FGSA.Run.CleanGateTick_def
#print axioms AvailableChain.FGSA.Run.CleanDeliveryStateStep_def
#print axioms AvailableChain.FGSA.Run.CleanDeliveryHistStep_def
#print axioms AvailableChain.FGSA.Run.CleanBlockStateStep_def
#print axioms AvailableChain.FGSA.Run.CleanBlockHistStep_def
#print axioms AvailableChain.FGSA.Run.CleanNoGateStateStep_def
#print axioms AvailableChain.FGSA.Run.CleanNoGateHistStep_def
#print axioms AvailableChain.FGSA.Run.CleanGateStateStep_def
#print axioms AvailableChain.FGSA.Run.CleanGateHistStep_def

#print axioms AvailableChain.FGSA.Run.clean_certSources_of_rows
#print axioms AvailableChain.FGSA.Run.clean_gateInputs_from_rows
#print axioms AvailableChain.FGSA.Run.clean_delivery_rowSources
#print axioms AvailableChain.FGSA.Run.clean_noGate_rowSources
#print axioms AvailableChain.FGSA.Run.clean_block_reconcile_state
#print axioms AvailableChain.FGSA.Run.clean_deliveryHistStep
#print axioms AvailableChain.FGSA.Run.clean_blockHistStep
#print axioms AvailableChain.FGSA.Run.clean_noGateHistStep
#print axioms AvailableChain.FGSA.Run.cleanState_zero
#print axioms AvailableChain.FGSA.Run.clean_gate_fields_all

#print axioms AvailableChain.FGSA.Run.clean_deliveryStateStep
#print axioms AvailableChain.FGSA.Run.clean_blockStateStep
#print axioms AvailableChain.FGSA.Run.clean_noGateStateStep
#print axioms AvailableChain.FGSA.Run.clean_gate_state_of_rows

#print axioms AvailableChain.FGSA.Run.CleanActionStep_def
#print axioms AvailableChain.FGSA.Run.clean_gateStateStep_of_action
#print axioms AvailableChain.FGSA.Run.cleanState_of_hist
#print axioms AvailableChain.FGSA.Run.sExtends_upTo_of_action

#print axioms AvailableChain.FGSA.Run.cpPrefix_of_srcFrame
#print axioms AvailableChain.FGSA.Run.cpCompat_of_srcFrame
#print axioms AvailableChain.FGSA.Run.cleanFrame_of_state

#print axioms AvailableChain.FGSA.Run.CleanFrameStmt_def
#print axioms AvailableChain.FGSA.Run.clean_actionStep
#print axioms AvailableChain.FGSA.Run.clean_gateStateStep
#print axioms AvailableChain.FGSA.Run.sExtends_upTo
#print axioms AvailableChain.FGSA.Run.cleanFrame

#print axioms AvailableChain.FGSA.Run.clean_gate_passed_of_ordered
#print axioms AvailableChain.FGSA.Run.clean_gate_batch
#print axioms AvailableChain.FGSA.Run.clean_gate_stamps
#print axioms AvailableChain.FGSA.Run.clean_gate_zero
#print axioms AvailableChain.FGSA.Run.clean_gate_head_prefixes
#print axioms AvailableChain.FGSA.Run.clean_gate_same
#print axioms AvailableChain.FGSA.Run.clean_gate_nonempty
#print axioms AvailableChain.FGSA.Run.clean_gate_history_osn
#print axioms AvailableChain.FGSA.Run.clean_gateHistStep
#print axioms AvailableChain.FGSA.Run.fgsa_releaseCount_antitone
#print axioms AvailableChain.FGSA.Run.fgsa_release_store
#print axioms AvailableChain.FGSA.Run.fgsa_release_bound

#print axioms AvailableChain.FGSA.Run.fgsa_releaseStoreClaim
#print axioms AvailableChain.FGSA.Run.fgsa_releaseClaim

#print axioms AvailableChain.FGSA.Run.fgsa_sameLabel
#print axioms AvailableChain.FGSA.Run.fgsa_sameLabelClaim
#print axioms AvailableChain.FGSA.Run.fgsa_honest_head_eq_of_stored
#print axioms AvailableChain.FGSA.Run.fgsa_active_support_of_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_covered_honest_head_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_stored_honest_head_awake
#print axioms AvailableChain.FGSA.Run.fgsa_late_rest_bound
#print axioms AvailableChain.FGSA.Run.fgsa_gate_batch_premises
#print axioms AvailableChain.FGSA.Run.fgsa_active_path_of_coverage
#print axioms AvailableChain.FGSA.Run.fgsa_gate_zero_of_receipts

#print axioms AvailableChain.FGSA.Run.clean_transfer_source_acceptances
#print axioms AvailableChain.FGSA.Run.clean_transfer_gate_acceptances
#print axioms AvailableChain.FGSA.Run.clean_transfer_receipt_path
#print axioms AvailableChain.FGSA.Run.clean_transfer_prefreeze_path
#print axioms AvailableChain.FGSA.Run.clean_transfer_frame
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_backward_relay

#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_seat_clean_late
#print axioms AvailableChain.FGSA.Run.fgsa_headSupport_subset_headVotes
#print axioms AvailableChain.FGSA.Run.fgsa_headVotes_provenance
#print axioms AvailableChain.FGSA.Run.fgsa_vote_accepted_before_head_read
#print axioms AvailableChain.FGSA.Run.fgsa_headVotes_backward_relay

#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_vote_forward
#print axioms AvailableChain.FGSA.Run.fgsa_voteSupports_of_path

#print axioms AvailableChain.FGSA.Run.clean_transfer_receipt_path_of_head
#print axioms AvailableChain.FGSA.Run.clean_transfer_prefreeze_path_of_head
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_forward_relay

#print axioms AvailableChain.FGSA.Run.cleanTransfer

#print axioms AvailableChain.FGSA.Run.cleanCut_zero_body
#print axioms AvailableChain.FGSA.Run.cleanSafety_of_trunc_body
#print axioms AvailableChain.FGSA.Run.cleanHistoryAt_zero
#print axioms AvailableChain.FGSA.Run.cleanTruncAt_zero
#print axioms AvailableChain.FGSA.Run.cleanSafetyAt_of_trunc
#print axioms AvailableChain.FGSA.Run.cleanCutZero_export

-- F2.6: bounded closure, all source reads, and the public history wrapper.
#print axioms AvailableChain.FGSA.Run.clean_actionSources_body
#print axioms AvailableChain.FGSA.Run.clean_actionSources
#print axioms AvailableChain.FGSA.Run.clean_invariant
#print axioms AvailableChain.FGSA.Run.cleanHistoryAt_body
#print axioms AvailableChain.FGSA.Run.cleanHistoryAt
#print axioms AvailableChain.FGSA.Run.sExtends
#print axioms AvailableChain.FGSA.Run.clean_gateOutput_body
#print axioms AvailableChain.FGSA.Run.clean_gateOutput

-- F2.7: bounded Clean results and lane exports.
#print axioms AvailableChain.FGSA.Run.clean_sCompatible
#print axioms AvailableChain.FGSA.Run.clean_outputsAt
#print axioms AvailableChain.FGSA.Run.cleanGateAt_body
#print axioms AvailableChain.FGSA.Run.cleanTruncAt_body
#print axioms AvailableChain.FGSA.Run.cleanSafety_body
#print axioms AvailableChain.FGSA.Run.cleanGateAt
#print axioms AvailableChain.FGSA.Run.cleanTruncAt
#print axioms AvailableChain.FGSA.Run.cleanSafety
#print axioms AvailableChain.FGSA.Run.cleanCutPos_export
#print axioms AvailableChain.FGSA.Run.cleanSafety_of_cut

-- F2.8: channel-free Clean claim assembly.
#print axioms AvailableChain.FGSA.Run.fgsa_cleanCutClaim
#print axioms AvailableChain.FGSA.Run.fgsa_cleanHistoryClaim
#print axioms AvailableChain.FGSA.Run.fgsa_cleanPrefixTruncationClaim
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSafetyClaim
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSafety_outputs

#print axioms AvailableChain.FGSA.Run.batch_head_covers
#print axioms AvailableChain.FGSA.Run.healed_same_time
#print axioms AvailableChain.FGSA.Run.healed_mono_start

-- F0.8b: new public declarations.
#print axioms AvailableChain.FGSA.Run.muOf_spec
#print axioms AvailableChain.FGSA.Run.H0.time_unique
#print axioms AvailableChain.FGSA.Run.H0.tstar_eq
#print axioms AvailableChain.Gen.Pure.QualSearch.of_recS
#print axioms AvailableChain.Gen.Pure.QualSearch.of_recC
#print axioms AvailableChain.Gen.Pure.QualSearch.of_lit

#print axioms AvailableChain.FGSA.Run.HealAC.tsMono
#print axioms AvailableChain.FGSA.Run.HealAC.tExact

#check AvailableChain.FGSA.Run.QualSearch.of_recS
#check AvailableChain.FGSA.Run.QualSearch.of_recC
#check AvailableChain.FGSA.Run.QualSearch.of_lit
