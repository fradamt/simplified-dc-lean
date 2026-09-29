module
public import AvailableChainFGSA.Proofs.BlockAncestry
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.Fields
public import AvailableChainFGSA.Proofs.ActView
public import AvailableChainFGSA.Proofs.Nesting
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.Admission
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainFGSA.Proofs.CrossNode

/-! Kernel dependency audit (Task 13 Step 1): one line for each public theorem of
Tasks 2 and 7–12. Each prints only `propext`, `Classical.choice`, `Quot.sound`, or
no axiom. `scripts/CheckFGSAAxioms.lean` checks every FGSA constant mechanically. -/

-- Proofs/BlockAncestry.lean
#print axioms AvailableChain.FGSA.block_preceq_refl
#print axioms AvailableChain.FGSA.block_preceq_trans
#print axioms AvailableChain.FGSA.block_preceq_antisymm
#print axioms AvailableChain.FGSA.block_genesis_preceq
#print axioms AvailableChain.FGSA.block_preceq_total_of_common
#print axioms AvailableChain.FGSA.block_compatible_comm
#print axioms AvailableChain.FGSA.block_compatible_of_common
#print axioms AvailableChain.FGSA.block_incompatible_of_preceq
#print axioms AvailableChain.FGSA.block_compatible_of_preceq_compatible

-- Proofs/Carrier.lean
#print axioms AvailableChain.FGSA.eraseFG_slot
#print axioms AvailableChain.FGSA.eraseFG_root
#print axioms AvailableChain.FGSA.eraseFG_parent
#print axioms AvailableChain.FGSA.eraseFG_eq_genesis
#print axioms AvailableChain.FGSA.eraseFG_preceq
#print axioms AvailableChain.FGSA.eraseFG_compatible
#print axioms AvailableChain.FGSA.eraseFG_injOn
#print axioms AvailableChain.FGSA.preceq_of_eraseFG_preceq
#print axioms AvailableChain.FGSA.compatible_iff_eraseFG
#print axioms AvailableChain.FGSA.viewRootInj_of_rootInj
#print axioms AvailableChain.FGSA.rootInjectiveOn_of_viewRootInj
#print axioms AvailableChain.FGSA.erase_rootInjective
#print axioms AvailableChain.FGSA.eraseFG_injective
#print axioms AvailableChain.FGSA.encLabel_inj
#print axioms AvailableChain.FGSA.encAuth_inj
#print axioms AvailableChain.FGSA.encRowBody_inj
#print axioms AvailableChain.FGSA.encRowWire_inj
#print axioms AvailableChain.FGSA.appOf_packBody
#print axioms AvailableChain.FGSA.packInner_inj
#print axioms AvailableChain.FGSA.packBody_inj
#print axioms AvailableChain.FGSA.rowsOk_iff
#print axioms AvailableChain.FGSA.rowsOk_node_packBody
#print axioms AvailableChain.FGSA.rows_eq_of_rowsOk

-- Proofs/Fields.lean
#print axioms AvailableChain.FGSA.admitHead_fg
#print axioms AvailableChain.FGSA.admitHead_base_blocks
#print axioms AvailableChain.FGSA.admitHead_base_stable
#print axioms AvailableChain.FGSA.admitHead_obligations
#print axioms AvailableChain.FGSA.admitHead_fastWrite
#print axioms AvailableChain.FGSA.admitHead_genuine
#print axioms AvailableChain.FGSA.admitRow_eq
#print axioms AvailableChain.FGSA.admitBlock_refused
#print axioms AvailableChain.FGSA.onView_fg
#print axioms AvailableChain.FGSA.onView_base_blocks
#print axioms AvailableChain.FGSA.onView_proposals
#print axioms AvailableChain.FGSA.onView_rowPool
#print axioms AvailableChain.FGSA.onView_fastWrite
#print axioms AvailableChain.FGSA.normalizeS_fg
#print axioms AvailableChain.FGSA.normalizeS_fields
#print axioms AvailableChain.FGSA.reconcile_fg
#print axioms AvailableChain.FGSA.freeze_blocks
#print axioms AvailableChain.FGSA.release_blocks
#print axioms AvailableChain.FGSA.saGate_blocks
#print axioms AvailableChain.FGSA.gateStep_fg
#print axioms AvailableChain.FGSA.gateStep_base_blocks
#print axioms AvailableChain.FGSA.gateStep_proposals
#print axioms AvailableChain.FGSA.gateStep_rowPool
#print axioms AvailableChain.FGSA.savedGenuine_append
#print axioms AvailableChain.FGSA.saGate_genuine
#print axioms AvailableChain.FGSA.gateStep_fresh
#print axioms AvailableChain.FGSA.gateStep_saved
#print axioms AvailableChain.FGSA.fastSet_prefix
#print axioms AvailableChain.FGSA.clockPre_fields
#print axioms AvailableChain.FGSA.clockPre_fg
#print axioms AvailableChain.FGSA.clockPre_genuine
#print axioms AvailableChain.FGSA.clockPre_fastWrite
#print axioms AvailableChain.FGSA.clock_fg
#print axioms AvailableChain.FGSA.clock_base_blocks
#print axioms AvailableChain.FGSA.clock_proposals
#print axioms AvailableChain.FGSA.clock_rowPool

-- Proofs/ActView.lean
#print axioms AvailableChain.FGSA.block_compatible_of_preceq
#print axioms AvailableChain.FGSA.block_compatible_of_below
#print axioms AvailableChain.FGSA.eraseFG_ancestor_mem
#print axioms AvailableChain.FGSA.actView_blocks
#print axioms AvailableChain.FGSA.actView_genesis_F
#print axioms AvailableChain.FGSA.actView_ancestor_closed
#print axioms AvailableChain.FGSA.actView_antitone
#print axioms AvailableChain.FGSA.actView_path
#print axioms AvailableChain.FGSA.blockExcluded_stable
#print axioms AvailableChain.FGSA.actView_eq
#print axioms AvailableChain.FGSA.actView_fields
#print axioms AvailableChain.FGSA.actView_noVeto
#print axioms AvailableChain.FGSA.actView_releaseCount_zero
#print axioms AvailableChain.FGSA.actView_onView
#print axioms AvailableChain.FGSA.actView_admitHead
#print axioms AvailableChain.FGSA.clockPre_eq
#print axioms AvailableChain.FGSA.onView_onView
#print axioms AvailableChain.FGSA.clock_eq_saClock_offGate
#print axioms AvailableChain.FGSA.clock_eq_saClockFrom_gate
#print axioms AvailableChain.FGSA.clock_eq_saClockFrom_gate'

-- Proofs/Nesting.lean
#print axioms AvailableChain.FGSA.outputNesting_v1
#print axioms AvailableChain.FGSA.normalizeS_nest
#print axioms AvailableChain.FGSA.reconcile_nest
#print axioms AvailableChain.FGSA.gateStep_nest
#print axioms AvailableChain.FGSA.admitRow_nest
#print axioms AvailableChain.FGSA.foldl_admitRow_nest
#print axioms AvailableChain.FGSA.admitProposal_stable
#print axioms AvailableChain.FGSA.process_nest
#print axioms AvailableChain.FGSA.clockPre_stable
#print axioms AvailableChain.FGSA.clock_nest
#print axioms AvailableChain.FGSA.outputNesting_stored
#print axioms AvailableChain.FGSA.finalized_preceq_stable

-- Proofs/Reconcile.lean
#print axioms AvailableChain.FGSA.reconcile_eq
#print axioms AvailableChain.FGSA.reconcile_obligations
#print axioms AvailableChain.FGSA.reconcile_genuine
#print axioms AvailableChain.FGSA.reconcile_savedGenuine
#print axioms AvailableChain.FGSA.reconcile_fastWrite
#print axioms AvailableChain.FGSA.reconcile_stable
#print axioms AvailableChain.FGSA.reconcile_frame
#print axioms AvailableChain.FGSA.storeControls_reconcile
#print axioms AvailableChain.FGSA.preceq_normal
#print axioms AvailableChain.FGSA.reconcile_idem
#print axioms AvailableChain.FGSA.reconcile_saCompat
#print axioms AvailableChain.FGSA.stable_preceq_normal
#print axioms AvailableChain.FGSA.reconcile_harmless
#print axioms AvailableChain.FGSA.reconcile_fastOrigin
#print axioms AvailableChain.FGSA.mem_genuine_of_saved
#print axioms AvailableChain.FGSA.reconcile_harmless_origin

-- Proofs/Admission.lean
#print axioms AvailableChain.FGSA.CStoreInv.toInv0
#print axioms AvailableChain.FGSA.pickPair_some_spec
#print axioms AvailableChain.FGSA.parentFG_spec
#print axioms AvailableChain.FGSA.parentFG_isSome_iff_root
#print axioms AvailableChain.FGSA.admitBlock_missingParent
#print axioms AvailableChain.FGSA.eraseFG_fgBlock
#print axioms AvailableChain.FGSA.fgBlock_parent
#print axioms AvailableChain.FGSA.fgBlock_slot
#print axioms AvailableChain.FGSA.fgBlock_root
#print axioms AvailableChain.FGSA.fgBlock_rows
#print axioms AvailableChain.FGSA.fgBlock_notMem
#print axioms AvailableChain.FGSA.toRow_forall₂
#print axioms AvailableChain.FGSA.blockAccepted_of_wellFormed
#print axioms AvailableChain.FGSA.rootTest_iff_blockTest
#print axioms AvailableChain.FGSA.blockAccepted_facts
#print axioms AvailableChain.FGSA.blockAccepted_rowsOk
#print axioms AvailableChain.FGSA.accepted_base_facts
#print axioms AvailableChain.FGSA.fg_on_block_accepts
#print axioms AvailableChain.FGSA.admitVote_withBlocks
#print axioms AvailableChain.FGSA.foldVotes_withBlocks
#print axioms AvailableChain.FGSA.foldVotes_fields
#print axioms AvailableChain.FGSA.admitProposal_of_accept
#print axioms AvailableChain.FGSA.base_admitProposal_accepts
#print axioms AvailableChain.FGSA.activeCompatible_eq
#print axioms AvailableChain.FGSA.foldl_admitRow_eq
#print axioms AvailableChain.FGSA.admitBlock_accepted_eq
#print axioms AvailableChain.FGSA.accepted_F_facts
#print axioms AvailableChain.FGSA.foldl_admitRow_view
#print axioms AvailableChain.FGSA.admitProposal_base_view
#print axioms AvailableChain.FGSA.actView_admitBlock_sameF
#print axioms AvailableChain.FGSA.actView_admitBlock_movedF
#print axioms AvailableChain.FGSA.admitBlock_sufficient
#print axioms AvailableChain.FGSA.admitBlock_sufficient_absent

-- Proofs/StoreInv.lean
#print axioms AvailableChain.FGSA.viewRootInj_TF
#print axioms AvailableChain.FGSA.storeControls_eq
#print axioms AvailableChain.FGSA.J_mem
#print axioms AvailableChain.FGSA.Z_mem
#print axioms AvailableChain.FGSA.savedGenuine_congr
#print axioms AvailableChain.FGSA.fastOrigin_congr
#print axioms AvailableChain.FGSA.cstoreInv_of_sublist
#print axioms AvailableChain.FGSA.cstoreInv_normalizeS
#print axioms AvailableChain.FGSA.rootInj_all
#print axioms AvailableChain.FGSA.cstoreInv_init
#print axioms AvailableChain.FGSA.cstoreInv_accepted_pre
#print axioms AvailableChain.FGSA.cstoreInv_admitBlock
#print axioms AvailableChain.FGSA.cstoreInv_process
#print axioms AvailableChain.FGSA.clockPre_obligations_sublist
#print axioms AvailableChain.FGSA.cstoreInv_clockPre
#print axioms AvailableChain.FGSA.writeObligation_keys
#print axioms AvailableChain.FGSA.writeKeys_keys
#print axioms AvailableChain.FGSA.saGateWriteKeys_level
#print axioms AvailableChain.FGSA.saGate_cases
#print axioms AvailableChain.FGSA.ne_of_saved
#print axioms AvailableChain.FGSA.notMem_keys_of_unsaved
#print axioms AvailableChain.FGSA.compat_of_confirmation
#print axioms AvailableChain.FGSA.cstoreInv_gateFresh
#print axioms AvailableChain.FGSA.cstoreInv_gateStep
#print axioms AvailableChain.FGSA.saCompat_gateStep
#print axioms AvailableChain.FGSA.fastOrigin_gateStep
#print axioms AvailableChain.FGSA.cstoreInv_clock
#print axioms AvailableChain.FGSA.storeInvariant
#print axioms AvailableChain.FGSA.fg_step_cases
#print axioms AvailableChain.FGSA.fMonotone
#print axioms AvailableChain.FGSA.process_F_mono
#print axioms AvailableChain.FGSA.clock_F_eq
#print axioms AvailableChain.FGSA.process_hmax_mono
#print axioms AvailableChain.FGSA.process_pair_mono
#print axioms AvailableChain.FGSA.actView_eq_image
#print axioms AvailableChain.FGSA.admitBlock_reconcile_harmless
#print axioms AvailableChain.FGSA.fgBlockOf_spec
#print axioms AvailableChain.FGSA.deepest_spec
#print axioms AvailableChain.FGSA.foldl_select_mem
#print axioms AvailableChain.FGSA.fgHead_stored
#print axioms AvailableChain.FGSA.rootInjectiveBelow_base
#print axioms AvailableChain.FGSA.find?_congr_mem
#print axioms AvailableChain.FGSA.leaseOf_eq_deadlineOf

-- Proofs/Metadata.lean
#print axioms AvailableChain.FGSA.admitVote_stamps
#print axioms AvailableChain.FGSA.foldVotes_stamps
#print axioms AvailableChain.FGSA.writeKeys_stamps
#print axioms AvailableChain.FGSA.saGate_stamps
#print axioms AvailableChain.FGSA.gateStep_stamps
#print axioms AvailableChain.FGSA.clockPre_stamps
#print axioms AvailableChain.FGSA.clock_cumulative
#print axioms AvailableChain.FGSA.accepted_st2
#print axioms AvailableChain.FGSA.admitProposal_prefix
#print axioms AvailableChain.FGSA.process_cumulative
#print axioms AvailableChain.FGSA.metaInv_init
#print axioms AvailableChain.FGSA.block?_proposal
#print axioms AvailableChain.FGSA.metaInv_admitRow
#print axioms AvailableChain.FGSA.metaInv_foldl_admitRow
#print axioms AvailableChain.FGSA.wire_block_mem
#print axioms AvailableChain.FGSA.accepted_rows_decode
#print axioms AvailableChain.FGSA.metaInv_accepted
#print axioms AvailableChain.FGSA.metaInv_process
#print axioms AvailableChain.FGSA.metaInv_clock
#print axioms AvailableChain.FGSA.metadataInvariant
#print axioms AvailableChain.FGSA.stored_wire_of_block

-- Proofs/CrossNode.lean
#print axioms AvailableChain.FGSA.contentAgree_symm
#print axioms AvailableChain.FGSA.contentAgree_self
#print axioms AvailableChain.FGSA.contentAgree
#print axioms AvailableChain.FGSA.contentAgree_reachable
#print axioms AvailableChain.FGSA.eraseFG_ancestor_preceq
#print axioms AvailableChain.FGSA.fg_eq_of_eraseFG_eq_across
#print axioms AvailableChain.FGSA.fg_eq_of_root_eq_across
#print axioms AvailableChain.FGSA.preceq_iff_across
#print axioms AvailableChain.FGSA.compatible_iff_across
#print axioms AvailableChain.FGSA.rootInjectiveOn_across
