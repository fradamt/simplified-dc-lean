module
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainFGSARun.Model.Families
public import AvailableChainFGSARun.Proofs.Protocol
public import AvailableChainFGSARun.Proofs.Excludes
public import AvailableChainFGSARun.Proofs.Interface
public import AvailableChainFGSARun.Proofs.ClockLaws
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainFGSARun.Proofs.Acceptance
public import AvailableChainFGSARun.Tests.Acceptance

/-! Kernel dependency audit of the FG-SA run library (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md`, T7.1): one `#print axioms`
line for each public theorem and each E5 value of the library. Each line
prints only `propext`, `Classical.choice`, `Quot.sound`, or no axiom.
`scripts/CheckFGSARunAxioms.lean` checks every constant of the library
mechanically. -/

-- Interface and clock laws (T7.3, T7.4)
#print axioms AvailableChain.FGSA.Run.fgsaInterface
#print axioms AvailableChain.FGSA.Run.fgsaOutputs
#print axioms AvailableChain.FGSA.Run.finalizedOut
#print axioms AvailableChain.FGSA.Run.proposalTime_fgsa
#print axioms AvailableChain.FGSA.Run.propLabel_injective
#print axioms AvailableChain.FGSA.Run.fgsaClock
#print axioms AvailableChain.FGSA.Run.fgsa_restore_now_eq
#print axioms AvailableChain.FGSA.Run.fgsa_hrestore_now
#print axioms AvailableChain.FGSA.Run.fgsa_hrestore
#print axioms AvailableChain.FGSA.Run.fgsa_hrestore_field

-- Model/Protocol.lean (T7.2)
#print axioms AvailableChain.FGSA.Run.toWireEquiv
#print axioms AvailableChain.FGSA.Run.slotOf_offset
#print axioms AvailableChain.FGSA.Run.duties_spec
#print axioms AvailableChain.FGSA.Run.duties_nodup
#print axioms AvailableChain.FGSA.Run.fgsa

-- Model/Families.lean (T7.2)
#print axioms AvailableChain.FGSA.Run.fgsaFamilies
#print axioms AvailableChain.FGSA.Run.fgsaIso

-- Proofs/Protocol.lean (T7.2)
#print axioms AvailableChain.FGSA.Run.restore_st
#print axioms AvailableChain.FGSA.Run.restore_rec
#print axioms AvailableChain.FGSA.Run.clock_rec
#print axioms AvailableChain.FGSA.Run.process_rec
#print axioms AvailableChain.FGSA.Run.recordOwn_st
#print axioms AvailableChain.FGSA.Run.recordOwn_rec
#print axioms AvailableChain.FGSA.Run.attest_signer_irrel
#print axioms AvailableChain.FGSA.Run.act_fg
#print axioms AvailableChain.FGSA.Run.recordOwn_attest
#print axioms AvailableChain.FGSA.Run.act_prop
#print axioms AvailableChain.FGSA.Run.act_prop_zero
#print axioms AvailableChain.FGSA.Run.withApp_zero
#print axioms AvailableChain.FGSA.Run.rowsOk_withApp
#print axioms AvailableChain.FGSA.Run.singleSeat_prop
#print axioms AvailableChain.FGSA.Run.linked_selfVisible
#print axioms AvailableChain.FGSA.Run.tick_st
#print axioms AvailableChain.FGSA.Run.ofWire_toWire
#print axioms AvailableChain.FGSA.Run.toWire_ofWire
#print axioms AvailableChain.FGSA.Run.toWire_injective
#print axioms AvailableChain.FGSA.Run.toWire_ofHead
#print axioms AvailableChain.FGSA.Run.toWire_ofRow
#print axioms AvailableChain.FGSA.Run.ofRow_injective
#print axioms AvailableChain.FGSA.Run.ofHead_injective
#print axioms AvailableChain.FGSA.Run.ofRow_auth
#print axioms AvailableChain.FGSA.Run.decode_eq_vote
#print axioms AvailableChain.FGSA.Run.decode_eq_row
#print axioms AvailableChain.FGSA.Run.decode_eq_block
#print axioms AvailableChain.FGSA.Run.rowWire_decode
#print axioms AvailableChain.FGSA.Run.processedS_ofRow
#print axioms AvailableChain.FGSA.Run.excludesS_ofRow
#print axioms AvailableChain.FGSA.Run.rowExcl_iff
#print axioms AvailableChain.FGSA.Run.handlesS_ofRow_iff

-- Proofs/Excludes.lean (T7.2, `excludes_inert`)
#print axioms AvailableChain.FGSA.Run.Internal.eraseDups_nodup'
#print axioms AvailableChain.FGSA.Run.Internal.grid_equivocates_mono
#print axioms AvailableChain.FGSA.Run.Internal.grid_votesAt_subset
#print axioms AvailableChain.FGSA.Run.Internal.lt_sub_one_iff_add_one_lt
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_head_iff
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_head
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_congr
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_now
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_of_excludes
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_of_votes
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_keeps
#print axioms AvailableChain.FGSA.Run.Internal.grid_fold_keeps
#print axioms AvailableChain.FGSA.Run.Internal.grid_fold_now
#print axioms AvailableChain.FGSA.Run.Internal.grid_fold_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitProposal_now
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitProposal_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitProposal_keeps
#print axioms AvailableChain.FGSA.Run.excludesS_of_vote
#print axioms AvailableChain.FGSA.Run.excludesS_of_row
#print axioms AvailableChain.FGSA.Run.excludesS_of_block
#print axioms AvailableChain.FGSA.Run.excludesS_of_none
#print axioms AvailableChain.FGSA.Run.row_wire_roundtrip
#print axioms AvailableChain.FGSA.Run.admitRow_of_rowExcl
#print axioms AvailableChain.FGSA.Run.admitBlock_of_blockExcluded
#print axioms AvailableChain.FGSA.Run.excludesS_inert
#print axioms AvailableChain.FGSA.Run.excludes_inert
#print axioms AvailableChain.FGSA.Run.Internal.admitRow_base
#print axioms AvailableChain.FGSA.Run.Internal.foldl_admitRow_base
#print axioms AvailableChain.FGSA.Run.Internal.ite_reconcile
#print axioms AvailableChain.FGSA.Run.process_base_now
#print axioms AvailableChain.FGSA.Run.process_keeps_grid
#print axioms AvailableChain.FGSA.Run.rowExcl_congr
#print axioms AvailableChain.FGSA.Run.rowExcl_of_congr
#print axioms AvailableChain.FGSA.Run.admitRow_keeps
#print axioms AvailableChain.FGSA.Run.foldl_admitRow_keeps
#print axioms AvailableChain.FGSA.Run.process_keeps_row
#print axioms AvailableChain.FGSA.Run.process_keeps_block
#print axioms AvailableChain.FGSA.Run.excludesS_process
#print axioms AvailableChain.FGSA.Run.Internal.foldl_vn
#print axioms AvailableChain.FGSA.Run.Internal.saGateFrom_vn
#print axioms AvailableChain.FGSA.Run.Internal.clockPre_vn
#print axioms AvailableChain.FGSA.Run.Internal.gateStep_vn
#print axioms AvailableChain.FGSA.Run.clock_vn
#print axioms AvailableChain.FGSA.Run.process_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.slotOf_mono
#print axioms AvailableChain.FGSA.Run.excludesS_clock
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_vote
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_row
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_block
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_none
#print axioms AvailableChain.FGSA.Run.excludesFixed_excludesS
#print axioms AvailableChain.FGSA.Run.excludesFixed_process
#print axioms AvailableChain.FGSA.Run.excludesFixed_clock
#print axioms AvailableChain.FGSA.Run.excludes_inert_epoch
#print axioms AvailableChain.FGSA.Run.excludesFixed_inert_epoch
#print axioms AvailableChain.FGSA.Run.Epoch.weaken
#print axioms AvailableChain.FGSA.Run.epoch_of_restartFree
#print axioms AvailableChain.FGSA.Run.excludes_stable_epoch
#print axioms AvailableChain.FGSA.Run.excludesFixed_stable_epoch

-- Run-to-store bridge (T7.5)
#print axioms AvailableChain.FGSA.Run.reachable_stateBefore
#print axioms AvailableChain.FGSA.Run.reachable_stateBeforeTime
#print axioms AvailableChain.FGSA.Run.reachable_readAt
#print axioms AvailableChain.FGSA.Run.reachable_final
#print axioms AvailableChain.FGSA.Run.reachable_postClock
#print axioms AvailableChain.FGSA.Run.reachable_postTick
#print axioms AvailableChain.FGSA.Run.storeBundle_stateBefore
#print axioms AvailableChain.FGSA.Run.storeBundle_stateBeforeTime
#print axioms AvailableChain.FGSA.Run.storeBundle_readAt
#print axioms AvailableChain.FGSA.Run.storeBundle_final
#print axioms AvailableChain.FGSA.Run.storeBundle_postClock
#print axioms AvailableChain.FGSA.Run.storeBundle_postTick
#print axioms AvailableChain.FGSA.Run.inv0_stateBefore
#print axioms AvailableChain.FGSA.Run.cstoreInv_stateBefore
#print axioms AvailableChain.FGSA.Run.metaInv_stateBefore
#print axioms AvailableChain.FGSA.Run.nestOK_stateBefore
#print axioms AvailableChain.FGSA.Run.outputNesting_run
#print axioms AvailableChain.FGSA.Run.leaseBelowOutput_stateBefore
#print axioms AvailableChain.FGSA.Run.leaseBelowOutput_honest
#print axioms AvailableChain.FGSA.Run.stored_proposal_delivered
-- Hook and receipt laws (T7.7)
#print axioms AvailableChain.FGSA.Run.fgsa_clock_now
#print axioms AvailableChain.FGSA.Run.fgsaHooks
#print axioms AvailableChain.FGSA.Run.handles_wellFormed
#print axioms AvailableChain.FGSA.Run.fgsaAdmissionTime
#print axioms AvailableChain.FGSA.Run.fgsaTimely
#print axioms AvailableChain.FGSA.Run.fgsaAcceptanceInv
#print axioms AvailableChain.FGSA.Run.fgsaTrigger
#print axioms AvailableChain.FGSA.Run.fgsa_slot_threshold_iff
#print axioms AvailableChain.FGSA.Run.fgsa_round_threshold_iff
#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock
#print axioms AvailableChain.FGSA.Run.fgsaAcceptance
#print axioms AvailableChain.FGSA.Run.fgsaAdmitSound
#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock_clockOf
#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock_actTime
#print axioms AvailableChain.FGSA.Run.fgsaTrigger_def
#print axioms AvailableChain.FGSA.Run.fgsa_trigger_of_emit
#print axioms AvailableChain.FGSA.Run.fgsa_trigger_of_accept
#print axioms AvailableChain.FGSA.Run.Tests.fgsa_carried_row_cap_control
