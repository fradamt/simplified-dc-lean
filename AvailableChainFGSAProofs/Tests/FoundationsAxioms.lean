module
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalizedSafety -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.OpeningCovered -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Foundations.OpeningCoveredLower -- shake: keep (audit)

public section

namespace AvailableChain.FGSA.Run

#print axioms fgsa_rStore
#print axioms fgsa_rStoreCumul
#print axioms fgsa_rStoreDurable
#print axioms fgsa_rStoreEpoch
#print axioms fgsa_rMonoAll
#print axioms fgsa_rMono
#print axioms fgsa_rFrameExactNext
#print axioms fgsa_rActive
#print axioms fgsa_rCarrierView
#print axioms fgsa_rFrameNext
#print axioms fgsa_rFrameNextEpoch
#print axioms fgsa_seed_stored
#print axioms fgsa_seed_bounds
#print axioms FGFinalizedAt_def
#print axioms FinalityRunBlock_def
#print axioms finalityStoreRows_def
#print axioms fgsa_finalityStoreRows_contains
#print axioms FinalityCarriage_def
#print axioms fgsa_pureAccountable
#print axioms fgsa_pureAgreement
#print axioms finalityRun_parent_scope
#print axioms fgsa_runAccountable
#print axioms FGSASlashableBound_def
#print axioms rootScope_finality_read
#print axioms fgsa_wholeRunAccountable
#print axioms fgsa_eventPrefixAgreement_of_bound
#print axioms fgsa_wholeRunAgreement
#print axioms fgsa_slashable_faulty_count
#print axioms fgsa_eventPrefixAgreement
#print axioms fgsa_storeSlashableBound_of_faults
#print axioms fgsa_slashableBound_of_faults
#print axioms fgsa_storeSlashableBound_of_unforgeable
#print axioms fgsa_storeSlashableBound_of_base
#print axioms fgsa_accountable
#print axioms fgsa_finalLock_ev
#print axioms fgsa_finalLock_faulty_count
#print axioms fgsa_accountable_base
#print axioms carried_rows_carriage
#print axioms delivered_runBlock_carriage
#print axioms proposalRows_source
#print axioms store_wire_origin
#print axioms emitted_runBlock_carriage
#print axioms fgsa_runBlock_carriage
#print axioms fgsa_slashableBound_of_valid
#print axioms fgsa_slashableBound_of_base
#print axioms fgsa_finalityRowCarriage
#print axioms fgsa_bridge_runAccountable
#print axioms fgsa_bridge_parent_scope
#print axioms fgsa_bridge_read_scope
#print axioms fgsa_bridge_stores_accountable
#print axioms fgsa_bridge_reads_accountable
#print axioms fgsa_bridge_event_agreement
#print axioms fgsa_bridge_read_agreement
#print axioms fgsa_bridge_pool_count
#print axioms fgsa_bridge_slashableBound_of_faults
#print axioms fgsa_bridge_finalizedMonotone
#print axioms fgsa_bridge_finalizedMonotone_restart
#print axioms fgsa_bridge_clientSafeAll
#print axioms fgsa_bridge_read_row_origin
#print axioms fgsa_safetySlashesRead
#print axioms fgsa_bridge_honestNeverSlashed
#print axioms fgsa_apiPureAccountableClaim_body
#print axioms fgsa_apiPureAgreementClaim_body
#print axioms fgsa_apiWholeRunAccountableClaim_body
#print axioms fgsa_apiWholeRunAgreementClaim_body
#print axioms fgsa_apiEventPrefixAgreementClaim_body
#print axioms fgsa_apiFaultCountSlashableBoundClaim_body
#print axioms fgsa_apiFinalizedMonotonicityClaim_body
#print axioms fgsa_apiFinalizedMonotonicityRestartClaim_body
#print axioms fgsa_apiFinalizedSafetyClaim_body
#print axioms fgsa_apiFinalLockClaim_body
#print axioms fgsa_apiHonestNeverSlashedClaim_body
#print axioms fgsa_finalizedSafety
#print axioms fgsa_finalizedMonotone
#print axioms fgsa_finalizedMonotone_restart
#print axioms fgsa_storedTargetsBelowOutput
#print axioms fgsa_leaseOrigins_writeLabel
#print axioms fgsa_leaseOrigins_lastWrite
#print axioms fgsa_leaseOrigins_origins
#print axioms fgsa_leaseOrigins_fastWrites
#print axioms fgsa_leaseOrigins_chain
#print axioms fgsa_leaseOrigins_ancestorDeadlines
#print axioms rowPermission_confirmedReader_gate
#print axioms rowPermission_own_lock
#print axioms rowPermission_pair
#print axioms rowPermission_covered
#print axioms rowPermission_at
#print axioms fgsa_rowBitPersist
#print axioms fgsa_rowService_receipt
#print axioms validForParent_currentHeightMatch
#print axioms fgsa_tRowsSelect
#print axioms fgsa_rowsReceipt_carriage
#print axioms fgsa_tRowsReceipt
#print axioms fgsa_tRowsSync
#print axioms fgsa_tRows
#print axioms fgsa_rowsValidStored_atProposal
#print axioms BatchPrem.batch_of_valid
#print axioms fgsa_batchCoverage
#print axioms sourceDiscipline_tSrc
#print axioms sourceDiscipline_labelBound
#print axioms sourceDiscipline_emittedNonempty
#print axioms sourceDiscipline_emittedName
#print axioms emittedName_window
#print axioms sourceDiscipline_qcOrigin
#print axioms sourceDiscipline_strat
#print axioms sourceDiscipline_srcFrameAbove
#print axioms openingCovered_frontier_gate
#print axioms openingCovered_lower_gate

end AvailableChain.FGSA.Run
end
