import AvailableChainFGSAProofs.Proofs.Assembly.Root
import AvailableChainKitFG
import AvailableChainFGSAProofs.Tests.NonVacuity.HealingRun
import AvailableChainFGSAProofs.Tests.NonVacuity.HealingPackages
import AvailableChainFGSAProofs.Tests.NonVacuity.HealingClaims
import AvailableChainFGSAProofs.Tests.NonVacuity.FinalityClaims
#check AvailableChain.FGSA.Run.proposal_handlesS_direct
#print axioms AvailableChain.FGSA.Run.proposal_handlesS_direct
#check AvailableChain.FGSA.Run.proposal_handle_in_scope
#print axioms AvailableChain.FGSA.Run.proposal_handle_in_scope
#check AvailableChain.FGSA.Run.proposal_trigger_in_scope
#print axioms AvailableChain.FGSA.Run.proposal_trigger_in_scope
#check AvailableChain.FGSA.Run.stored_content_eq
#print axioms AvailableChain.FGSA.Run.stored_content_eq
#check AvailableChain.FGSA.Run.contentOk_withApp
#print axioms AvailableChain.FGSA.Run.contentOk_withApp
#check AvailableChain.FGSA.Run.withApp_zero_proposalBlock
#print axioms AvailableChain.FGSA.Run.withApp_zero_proposalBlock
#check AvailableChain.FGSA.Run.rowsOk_withApp_proposalBlock
#print axioms AvailableChain.FGSA.Run.rowsOk_withApp_proposalBlock
#check AvailableChain.FGSA.Run.rootBlockInRun_delivered
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_delivered
#check AvailableChain.FGSA.Run.rootBlockInRun_held
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_held
#check AvailableChain.FGSA.Run.rootBlockInRun_ancestor
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_ancestor
#check AvailableChain.FGSA.Run.rootBlockInRun_eq
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_eq
#check AvailableChain.FGSA.Run.rootInjectiveOn_run
#print axioms AvailableChain.FGSA.Run.rootInjectiveOn_run
#check AvailableChain.FGSA.Run.storeStepRoots_run
#print axioms AvailableChain.FGSA.Run.storeStepRoots_run
#check AvailableChain.FGSA.Run.stored_fg_body_delivery
#print axioms AvailableChain.FGSA.Run.stored_fg_body_delivery
#check AvailableChain.FGSA.Run.stored_body_delivery
#print axioms AvailableChain.FGSA.Run.stored_body_delivery
#check AvailableChain.FGSA.Run.rootBlockInRun_stored
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_stored
#check AvailableChain.FGSA.Run.rootBlockInRun_stored_proposal
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_stored_proposal
#check AvailableChain.FGSA.Run.stored_body_ancestor
#print axioms AvailableChain.FGSA.Run.stored_body_ancestor
#check AvailableChain.FGSA.Run.emitted_proposal_parent_stored
#print axioms AvailableChain.FGSA.Run.emitted_proposal_parent_stored
#check AvailableChain.FGSA.Run.emitted_payload_parent_stored
#print axioms AvailableChain.FGSA.Run.emitted_payload_parent_stored
#check AvailableChain.FGSA.Run.emitted_proposal_slot_root
#print axioms AvailableChain.FGSA.Run.emitted_proposal_slot_root
#check AvailableChain.FGSA.Run.rootBlockInRun_genesis_or_delivered
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_genesis_or_delivered
#check AvailableChain.FGSA.Run.rootBlockInRun_origin
#print axioms AvailableChain.FGSA.Run.rootBlockInRun_origin
#check AvailableChain.FGSA.Run.rootScope_store
#print axioms AvailableChain.FGSA.Run.rootScope_store
#check AvailableChain.FGSA.Run.rootScope_ancestor
#print axioms AvailableChain.FGSA.Run.rootScope_ancestor
#check AvailableChain.FGSA.Run.rootScope_eq
#print axioms AvailableChain.FGSA.Run.rootScope_eq
#check AvailableChain.FGSA.Run.rootScope_source
#print axioms AvailableChain.FGSA.Run.rootScope_source
#check AvailableChain.FGSA.Run.certified_preceq
#print axioms AvailableChain.FGSA.Run.certified_preceq
#check AvailableChain.FGSA.Run.rootScope_entry
#print axioms AvailableChain.FGSA.Run.rootScope_entry
#check AvailableChain.FGSA.Run.rootScope_justified
#print axioms AvailableChain.FGSA.Run.rootScope_justified
#check AvailableChain.FGSA.Run.rootScope_finalized
#print axioms AvailableChain.FGSA.Run.rootScope_finalized
#check AvailableChain.FGSA.Run.srcFrameAbove_scoped
#print axioms AvailableChain.FGSA.Run.srcFrameAbove_scoped
#check AvailableChain.FGSA.Run.rootScope_result
#print axioms AvailableChain.FGSA.Run.rootScope_result
#check AvailableChain.FGSA.Run.rootScope_belowLabel
#print axioms AvailableChain.FGSA.Run.rootScope_belowLabel
#check AvailableChain.FGSA.Run.contentAgree_run
#print axioms AvailableChain.FGSA.Run.contentAgree_run
#check AvailableChain.FGSA.Run.fgsa_proposal_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_proposal_receipt
#check AvailableChain.FGSA.Run.fgsa_receiptCoverage
#print axioms AvailableChain.FGSA.Run.fgsa_receiptCoverage
#check AvailableChain.FGSA.fgsa_ordinary_parent_of_live_prefix
#print axioms AvailableChain.FGSA.fgsa_ordinary_parent_of_live_prefix
#check AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry
#print axioms AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry
#check AvailableChain.FGSA.fgsa_ordinary_parent_of_live_cover
#print axioms AvailableChain.FGSA.fgsa_ordinary_parent_of_live_cover
#check AvailableChain.FGSA.Run.exactHead_of_pivot
#print axioms AvailableChain.FGSA.Run.exactHead_of_pivot
#check AvailableChain.FGSA.Run.finalityRun_parent_scope
#print axioms AvailableChain.FGSA.Run.finalityRun_parent_scope
#check AvailableChain.FGSA.Run.fgsa_runAccountable
#print axioms AvailableChain.FGSA.Run.fgsa_runAccountable
#check AvailableChain.FGSA.Run.rootScope_finality_read
#print axioms AvailableChain.FGSA.Run.rootScope_finality_read
#check AvailableChain.FGSA.Run.cpPrefix_of_srcFrame
#print axioms AvailableChain.FGSA.Run.cpPrefix_of_srcFrame
#check AvailableChain.FGSA.Run.cpCompat_of_scopedFrame
#print axioms AvailableChain.FGSA.Run.cpCompat_of_scopedFrame
#check AvailableChain.FGSA.Run.sourceDiscipline_strat
#print axioms AvailableChain.FGSA.Run.sourceDiscipline_strat
#check AvailableChain.FGSA.Run.arming_frame_below
#print axioms AvailableChain.FGSA.Run.arming_frame_below
#check AvailableChain.FGSA.Run.inclusion_frame_below
#print axioms AvailableChain.FGSA.Run.inclusion_frame_below
#check AvailableChain.FGSA.Run.fgsa_pureAccountable
#print axioms AvailableChain.FGSA.Run.fgsa_pureAccountable
#check AvailableChain.FGSA.Run.fgsa_pureAgreement
#print axioms AvailableChain.FGSA.Run.fgsa_pureAgreement
#check AvailableChain.FGSA.Run.fgsa_wholeRunAccountable
#print axioms AvailableChain.FGSA.Run.fgsa_wholeRunAccountable
#check AvailableChain.FGSA.Run.fgsa_wholeRunAgreement
#print axioms AvailableChain.FGSA.Run.fgsa_wholeRunAgreement
#check AvailableChain.FGSA.Run.fgsa_finalLock_of_bound
#print axioms AvailableChain.FGSA.Run.fgsa_finalLock_of_bound
#check AvailableChain.FGSA.Run.fgsa_rXing
#print axioms AvailableChain.FGSA.Run.fgsa_rXing
#check AvailableChain.FGSA.Run.healing_rows_above_entry_at_height
#print axioms AvailableChain.FGSA.Run.healing_rows_above_entry_at_height
#check AvailableChain.FGSA.Run.kmid_rows_above_entry
#print axioms AvailableChain.FGSA.Run.kmid_rows_above_entry
#check AvailableChain.FGSA.Run.fgsaClaims
#print axioms AvailableChain.FGSA.Run.fgsaClaims
#check AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective
#print axioms AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective
#check AvailableChain.FGSA.Run.Base₂.idealization
#print axioms AvailableChain.FGSA.Run.Base₂.idealization
#check AvailableChain.KitFG.FGStoreSafety.of_certificate
#print axioms AvailableChain.KitFG.FGStoreSafety.of_certificate
#check AvailableChain.KitFG.simplexStoreInvariant
#print axioms AvailableChain.KitFG.simplexStoreInvariant
#check AvailableChain.FGSA.Run.Tests.NonVacuity.HealingRun.nvRoots
#print axioms AvailableChain.FGSA.Run.Tests.NonVacuity.HealingRun.nvRoots
#check AvailableChain.FGSA.Run.Tests.NonVacuity.HealingPackages.nvRoots
#print axioms AvailableChain.FGSA.Run.Tests.NonVacuity.HealingPackages.nvRoots
#check AvailableChain.FGSA.Run.Tests.NonVacuity.HealingClaims.nvRoots
#print axioms AvailableChain.FGSA.Run.Tests.NonVacuity.HealingClaims.nvRoots
#check AvailableChain.FGSA.Run.Tests.NonVacuity.FinalityClaims.nvRoots
#print axioms AvailableChain.FGSA.Run.Tests.NonVacuity.FinalityClaims.nvRoots
#check AvailableChain.FGSA.Run.Tests.NonVacuity.FinalityClaims.nvLiveDC
#print axioms AvailableChain.FGSA.Run.Tests.NonVacuity.FinalityClaims.nvLiveDC
#check AvailableChain.FGSA.fgStoreSafety
#print axioms AvailableChain.FGSA.fgStoreSafety
#check AvailableChain.FGSA.Window.windowStoreSafety
#print axioms AvailableChain.FGSA.Window.windowStoreSafety
#check AvailableChain.KitFG.simplexStoreSafety
#print axioms AvailableChain.KitFG.simplexStoreSafety
