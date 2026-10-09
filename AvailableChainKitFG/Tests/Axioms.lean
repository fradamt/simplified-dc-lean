module
public import AvailableChainKitFG.TreeCorrespondence
public import AvailableChainKitFG.TreeFrameGeometry
public import AvailableChainKitFG.TreeTwoChanges
public import AvailableChainKitFG.TreeFrameBridge
public import AvailableChainKitFG.FrameChannels
public import AvailableChainKitFG.Accountable
public import AvailableChainKitFG.CrossingNoFinal
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.CausalCap
public import AvailableChainKitFG.ViewLockChains
public import AvailableChainKitFG.TwoChanges
public import AvailableChainKitFG.RowBits
public import AvailableChainKitFG.RecordHigh
public import AvailableChainKitFG.ClientOnceSafety
public import AvailableChainKitFG.RecordHighOnce
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainKitFG.AccountableCore

/-! Kernel dependency audit for the FG chain lemmas without root premises. -/

#print axioms AvailableChain.KitFG.slashableWeight_or_justified_eq
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_preceq
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_preceq
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_compatible_of_le
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_compatible
#print axioms AvailableChain.KitFG.exists_crossing_quorum_ne_justified
#print axioms AvailableChain.KitFG.e1Weight_of_finalityQC_not_preceq
#print axioms AvailableChain.KitFG.slashableWeight_of_finalized_crossing
#print axioms AvailableChain.KitFG.exists_honest_timeout_of_crossing
#print axioms AvailableChain.KitFG.frame_facts
#print axioms AvailableChain.KitFG.causalCap_row
#print axioms AvailableChain.KitFG.causalCap_justified_row
#print axioms AvailableChain.KitFG.finalityCap_row
#print axioms AvailableChain.KitFG.finalityCap_height_row
#print axioms AvailableChain.KitFG.causalCap

#print axioms AvailableChain.KitFG.storeFrame_noContest_of_crossed
#print axioms AvailableChain.KitFG.storeFrame_contest_of_compatible
#print axioms AvailableChain.KitFG.storeFrame_height_of_crossed_prefix
#print axioms AvailableChain.KitFG.storeFrame_retention_of_compatible
#print axioms AvailableChain.KitFG.ViewLockOfChainsStatement_def
#print axioms AvailableChain.KitFG.ViewLockOfHonestChainsStatement_def
#print axioms AvailableChain.KitFG.viewLock_of_chains
#print axioms AvailableChain.KitFG.viewLock_of_honest_chains
#print axioms AvailableChain.KitFG.LowerFDomainIdentityStatement_def
#print axioms AvailableChain.KitFG.lowerF_domain_identity
#print axioms AvailableChain.KitFG.chainBits_def
#print axioms AvailableChain.KitFG.sameBitState_def
#print axioms AvailableChain.KitFG.rowMatchesBit_def
#print axioms AvailableChain.KitFG.BitPersistStatement_def
#print axioms AvailableChain.KitFG.BitFromRowStatement_def
#print axioms AvailableChain.KitFG.bit_fold_covered
#print axioms AvailableChain.KitFG.bit_persist
#print axioms AvailableChain.KitFG.bit_from_row
#print axioms AvailableChain.KitFG.HighRecord_def
#print axioms AvailableChain.KitFG.RecordHighStatement_def
#print axioms AvailableChain.KitFG.NoHighContestStatement_def
#print axioms AvailableChain.KitFG.recordHigh
#print axioms AvailableChain.KitFG.noHighContest

-- Send-once client: pure content, record safety, and restart laws.
#print axioms AvailableChain.KitFG.onceSignedContent_eq_iff
#print axioms AvailableChain.KitFG.onceKey_eq_iff_signedContent_eq
#print axioms AvailableChain.KitFG.record_row_without_finality
#print axioms AvailableChain.KitFG.record_row_optional_finality
#print axioms AvailableChain.KitFG.createRowOnce_released
#print axioms AvailableChain.KitFG.createRowOnce_none
#print axioms AvailableChain.KitFG.createRowOnce_safe
#print axioms AvailableChain.KitFG.createRowOnce_valid
#print axioms AvailableChain.KitFG.createRowOnce_sent
#print axioms AvailableChain.KitFG.createRowOnce_sameHeight
#print axioms AvailableChain.KitFG.clientRunOnce_covers
#print axioms AvailableChain.KitFG.clientRunOnce_noSlash
#print axioms AvailableChain.KitFG.clientRunOnce_fresh
#print axioms AvailableChain.KitFG.clientRunOnce_keys_nodup
#print axioms AvailableChain.KitFG.clientRecordOnce_sent
#print axioms AvailableChain.KitFG.clientRecordOnce_append
#print axioms AvailableChain.KitFG.clientRunOnce_append
#print axioms AvailableChain.KitFG.record_row_once_signer_irrel
#print axioms AvailableChain.KitFG.createRowOnce_signer_irrel
#print axioms AvailableChain.KitFG.clientRunOnce_signedContent_nodup
#print axioms AvailableChain.KitFG.recordInv_createRowOnce
#print axioms AvailableChain.KitFG.recordExtends_createRowOnce
#print axioms AvailableChain.KitFG.covers_createRowOnce
#print axioms AvailableChain.KitFG.createRowOnce_noSelfSlash
#print axioms AvailableChain.SimplexFG.createRowOnce_def

-- The send-once high guard reuses the old row-count argument.
#print axioms AvailableChain.KitFG.RecordHighOnceStatement_def
#print axioms AvailableChain.KitFG.recordHigh_optional_finality
#print axioms AvailableChain.KitFG.recordHighOnce

-- ROOT-DIGEST: public root and content declarations.
#print axioms AvailableChain.KitFG.RootInjectiveOn_def
#print axioms AvailableChain.KitFG.StoreStepRoots
#print axioms AvailableChain.KitFG.StoreStepRoots_def
#print axioms AvailableChain.KitFG.candidateJ_rootInj_of_viewRootInj
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_preceq_of_parent_roots
#print axioms AvailableChain.KitFG.finalized_preceq_parent_of_certificate
#print axioms AvailableChain.KitFG.parent_preceq_parent
#print axioms AvailableChain.KitFG.preceq_parent_of_ne
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_compatible_of_parent_roots

-- AvailableChainKitFG/TreeFrameDef.lean
#print axioms AvailableChain.KitFG.treeStoreControlsView
#print axioms AvailableChain.KitFG.treeStoreControlsView_def
#print axioms AvailableChain.KitFG.treeStoreFrameView
#print axioms AvailableChain.KitFG.treeStoreFrameView_def
#print axioms AvailableChain.KitFG.treeFjControlsView
#print axioms AvailableChain.KitFG.treeFjControlsView_def
#print axioms AvailableChain.KitFG.treeFjFrameView
#print axioms AvailableChain.KitFG.treeFjFrameView_def

-- AvailableChainKitFG/TreeFrameBridge.lean
#print axioms AvailableChain.KitFG.treeECView
#print axioms AvailableChain.KitFG.treeECView_def
#print axioms AvailableChain.KitFG.treeStoreControlsView_contest_iff
#print axioms AvailableChain.KitFG.treeFjControlsView_contest_iff
#print axioms AvailableChain.KitFG.treeStoreControlsView_contest_witness
#print axioms AvailableChain.KitFG.treeFjControlsView_contest_witness
#print axioms AvailableChain.KitFG.treeStoreControlsView_contest_imp
#print axioms AvailableChain.KitFG.treeFjControlsView_contest_imp
#print axioms AvailableChain.KitFG.treeStoreControlsView_eq
#print axioms AvailableChain.KitFG.treeStoreFrameView_eq
#print axioms AvailableChain.KitFG.treeFjControlsView_eq
#print axioms AvailableChain.KitFG.treeFjFrameView_eq
#print axioms AvailableChain.KitFG.treeStoreControlsView_eq_of_no_offF_top
#print axioms AvailableChain.KitFG.treeFjControlsView_eq_of_no_offF_top
#print axioms AvailableChain.KitFG.treeStoreControlsView_J_preceq_of_rootIsJ
#print axioms AvailableChain.KitFG.treeFjControlsView_J_preceq_of_rootIsJ

-- AvailableChainKitFG/TreeCorrespondence.lean
#print axioms AvailableChain.KitFG.treePair_eq_of_lexKey_eq
#print axioms AvailableChain.KitFG.treeLexMax_eq_of_greatest
#print axioms AvailableChain.KitFG.treeLexMax_spec
#print axioms AvailableChain.KitFG.treeLexMax_of_none
#print axioms AvailableChain.KitFG.treeTop_extends_J

-- AvailableChainKitFG/TreeFrameGeometry.lean
#print axioms AvailableChain.KitFG.treeStore_contest_persist
#print axioms AvailableChain.KitFG.treeStore_contest_persist_of_inv

-- AvailableChainKitFG/TreeTwoChanges.lean
#print axioms AvailableChain.KitFG.treeLe_frontier
#print axioms AvailableChain.KitFG.treePhaseOf
#print axioms AvailableChain.KitFG.treeEJ
#print axioms AvailableChain.KitFG.treeEJ_def
#print axioms AvailableChain.KitFG.treeNFrame
#print axioms AvailableChain.KitFG.treePhaseOf_eq
#print axioms AvailableChain.KitFG.treeNFrame_eq
#print axioms AvailableChain.KitFG.treeFjControls_contest
#print axioms AvailableChain.KitFG.treeGap_of_ne
#print axioms AvailableChain.KitFG.treeTop_contest
#print axioms AvailableChain.KitFG.treeTop_uncontested
#print axioms AvailableChain.KitFG.treeTop_contested
#print axioms AvailableChain.KitFG.treeRootIsJ_iff
#print axioms AvailableChain.KitFG.treeOne_le_frontier
#print axioms AvailableChain.KitFG.treeLexMax_fst_lt
#print axioms AvailableChain.KitFG.treeLexMax_top_of_carrier
#print axioms AvailableChain.KitFG.treeLexMax_carrier_of_top
#print axioms AvailableChain.KitFG.treeECView_of_contest
#print axioms AvailableChain.KitFG.treeECView_mono_of_retained
#print axioms AvailableChain.KitFG.treeEvidence_mono
#print axioms AvailableChain.KitFG.treeEffFrame_of_bits
#print axioms AvailableChain.KitFG.treeNFrame_eq_phaseFrame
#print axioms AvailableChain.KitFG.treeTwoChanges
#print axioms AvailableChain.KitFG.treeTwoChanges_count
#print axioms AvailableChain.KitFG.treeTwoChanges_nested
