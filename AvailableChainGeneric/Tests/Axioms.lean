module
public import AvailableChainGeneric.Statements.V2.Slashing
public import AvailableChainGeneric.Statements.Pure.Quorum
public import AvailableChainGeneric.Statements.Pure.QuorumInter
public import AvailableChainGeneric.Statements.Pure.SupportCounts
public import AvailableChainGeneric.Statements.Pure.FirstBad
public import AvailableChainGeneric.Statements.Pure.Schedule
public import AvailableChainGeneric.Statements.Pure.Walk
public import AvailableChainGeneric.Statements.Pure.Props
public import AvailableChainGeneric.Statements.V2.Reads
public import AvailableChainGeneric.Statements.V2.Counts
public import AvailableChainGeneric.Statements.V2.Obs
public import AvailableChainGeneric.Statements.V2.Interface
public import AvailableChainGeneric.Statements.V2.Receipt
public import AvailableChainGeneric.Statements.V2.Regimes
public import AvailableChainGeneric.Statements.V2.Linked
public import AvailableChainGeneric.Statements.V2.Signatures
public import AvailableChainGeneric.Statements.AC.Reads
public import AvailableChainGeneric.Statements.AC.Lease
public import AvailableChainGeneric.Statements.AC.History
public import AvailableChainGeneric.Statements.AC.Transfer
public import AvailableChainGeneric.Statements.AC.Votes
public import AvailableChainGeneric.Proofs.Pure.FirstBad
public import AvailableChainGeneric.Proofs.Pure.Schedule
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainGeneric.Proofs.Pure.Walk
public import AvailableChainGeneric.Proofs.Pure.Quorum
public import AvailableChainGeneric.Proofs.Pure.SupportCounts
public import AvailableChainGeneric.Proofs.Pure.Fold
public import AvailableChainGeneric.Proofs.Pure.Props
public import AvailableChainGeneric.Proofs.V2.Fields
public import AvailableChainGeneric.Proofs.V2.Reads
public import AvailableChainGeneric.Proofs.V2.Induction
public import AvailableChainGeneric.Proofs.V2.BaseTransport
public import AvailableChainGeneric.Proofs.V2.Receipt
public import AvailableChainGeneric.Proofs.V2.Regimes
public import AvailableChainGeneric.Proofs.V2.Linked
public import AvailableChainGeneric.Proofs.V2.Signatures
public import AvailableChainGeneric.Proofs.AC.Output
public import AvailableChainGeneric.Proofs.AC.Lease
public import AvailableChainGeneric.Proofs.AC.History
public import AvailableChainGeneric.Proofs.AC.Transfer
public import AvailableChainGeneric.Proofs.AC.Votes
public import AvailableChainGeneric.Statements.AC.Support
public import AvailableChainGeneric.Statements.Pure.HonestCount
public import AvailableChainGeneric.Proofs.AC.Support
public import AvailableChainGeneric.Proofs.Pure.HonestCount

-- A4 support and honest-origin count contracts and proofs.
#print axioms AvailableChain.Gen.AC.GoldfishScoreAntitoneStatement_def
#print axioms AvailableChain.Gen.AC.ConflictingScoreSumLeStatement_def
#print axioms AvailableChain.Gen.AC.VoterCountLeOfSeatsSubsetStatement_def
#print axioms AvailableChain.Gen.Pure.HonestOriginOfCountStatement_def
#print axioms AvailableChain.Gen.AC.goldfishScore_antitone_statement
#print axioms AvailableChain.Gen.AC.goldfishScore_antitone
#print axioms AvailableChain.Gen.AC.goldfishScore_antitone_of_preceq
#print axioms AvailableChain.Gen.AC.conflicting_score_sum_le_statement
#print axioms AvailableChain.Gen.AC.conflicting_score_sum_le
#print axioms AvailableChain.Gen.AC.voterCount_le_of_seats_subset_statement
#print axioms AvailableChain.Gen.AC.voterCount_le_of_seats_subset
#print axioms AvailableChain.Gen.Pure.honest_origin_of_count_statement
#print axioms AvailableChain.Gen.Pure.honest_origin_of_count

/-! Kernel dependency audit of the Generic library: one line for each public
theorem, in facade order. The library globs build this test module. -/

-- Statements/Pure/Quorum.lean
#print axioms AvailableChain.Gen.Pure.qF_def
#print axioms AvailableChain.Gen.Pure.Weights.weight_pos
#print axioms AvailableChain.Gen.Pure.Weights.totalWeight_def
#print axioms AvailableChain.Gen.Pure.Weights.weightOf_def
#print axioms AvailableChain.Gen.Pure.Weights.q_def
#print axioms AvailableChain.Gen.Pure.Weights.IsQuorum_def

-- Statements/Pure/FirstBad.lean
#print axioms AvailableChain.Gen.Pure.FirstFailure_def
#print axioms AvailableChain.Gen.Pure.RetroAt_def

-- Statements/Pure/Schedule.lean
#print axioms AvailableChain.Gen.Pure.PatAt_def
#print axioms AvailableChain.Gen.Pure.InWindow_def
#print axioms AvailableChain.Gen.Pure.slotLen_def
#print axioms AvailableChain.Gen.Pure.Pattern.lastRound_def
#print axioms AvailableChain.Gen.Pure.Pattern.lastSlot_def
#print axioms AvailableChain.Gen.Pure.Pattern.tailEnd_def
#print axioms AvailableChain.Gen.Pure.windowEnd_def
#print axioms AvailableChain.Gen.Pure.windowEndAt_def
#print axioms AvailableChain.Gen.Pure.RecPat_def
#print axioms AvailableChain.Gen.Pure.RecPatAt_def
#print axioms AvailableChain.Gen.Pure.Qualified_def
#print axioms AvailableChain.Gen.Pure.Strong_def
#print axioms AvailableChain.Gen.Pure.FGood_def
#print axioms AvailableChain.Gen.Pure.FGood4_def
#print axioms AvailableChain.Gen.Pure.Skip_def
#print axioms AvailableChain.Gen.Pure.FinForm.pat_def
#print axioms AvailableChain.Gen.Pure.FinForm.lo_def
#print axioms AvailableChain.Gen.Pure.FinForm.len_def
#print axioms AvailableChain.Gen.Pure.FinForm.holds_def
#print axioms AvailableChain.Gen.Pure.RecS_def
#print axioms AvailableChain.Gen.Pure.RecF_def
#print axioms AvailableChain.Gen.Pure.RecF4_def
#print axioms AvailableChain.Gen.Pure.RecSkip_def
#print axioms AvailableChain.Gen.Pure.StrongRecW_def
#print axioms AvailableChain.Gen.Pure.Lit_def
#print axioms AvailableChain.Gen.Pure.RecC_def
#print axioms AvailableChain.Gen.Pure.windowEndA_def
#print axioms AvailableChain.Gen.Pure.windowEndAtA_def
#print axioms AvailableChain.Gen.Pure.QualSearch_def
#print axioms AvailableChain.Gen.Pure.lastSlotIdx_def
#print axioms AvailableChain.Gen.Pure.Pattern.Compat_def

-- Statements/Pure/Walk.lean
#print axioms AvailableChain.Gen.Pure.DominatedSuffix_def
#print axioms AvailableChain.Gen.Pure.NoEligibleChild_def
#print axioms AvailableChain.Gen.Pure.AnchorClosed_def
#print axioms AvailableChain.Gen.Pure.DescendantDepthBound_def
#print axioms AvailableChain.Gen.Pure.SuffixPersists_def
#print axioms AvailableChain.Gen.Pure.SuffixReflects_def
#print axioms AvailableChain.Gen.Pure.SuffixScoresAgree_def

-- Statements/Pure/Props.lean
#print axioms AvailableChain.Gen.Pure.CompatOn_def
#print axioms AvailableChain.Gen.Pure.CompatAt_def
#print axioms AvailableChain.Gen.Pure.MonoOn_def
#print axioms AvailableChain.Gen.Pure.BelowOn_def
#print axioms AvailableChain.Gen.Pure.ServedOn_def
#print axioms AvailableChain.Gen.Pure.CompatOnOfCompatAtMonoStatement_def
#print axioms AvailableChain.Gen.Pure.ServedOnMonoStatement_def

-- Statements/V2/Reads.lean
#print axioms AvailableChain.V2.Run.idxBefore_def
#print axioms AvailableChain.V2.Run.nthIdx?_def
#print axioms AvailableChain.Gen.V2.pubFloor_def
#print axioms AvailableChain.Gen.V2.HonestSlot_def
#print axioms AvailableChain.Gen.V2.HoldsBefore_def
#print axioms AvailableChain.Gen.V2.MonoAlong_def
#print axioms AvailableChain.Gen.V2.HoldsBeforeIffExistsIdxStatement_def
#print axioms AvailableChain.Gen.V2.Pending_def

-- Statements/V2/Counts.lean
#print axioms AvailableChain.Gen.V2.faulty_def
#print axioms AvailableChain.Gen.V2.awakeHonest_def

-- Statements/V2/Obs.lean

-- Statements/V2/Interface.lean

-- Statements/V2/Receipt.lean
#print axioms AvailableChain.Gen.V2.Trigger_def

-- Statements/V2/Regimes.lean
#print axioms AvailableChain.Gen.V2.LabelSync_def
#print axioms AvailableChain.Gen.V2.SeedAt_def

-- Statements/AC/Reads.lean
#print axioms AvailableChain.Gen.AC.Lease.target_def
#print axioms AvailableChain.Gen.AC.Lease.level_def
#print axioms AvailableChain.Gen.AC.Lease.deadline_def
#print axioms AvailableChain.Gen.AC.LeaseBelowOutput_def
#print axioms AvailableChain.Gen.AC.normalizeOutput_def
#print axioms AvailableChain.Gen.AC.ACReads.saved_def
#print axioms AvailableChain.Gen.AC.ACReads.gateView_def
#print axioms AvailableChain.Gen.AC.ACReads.gateLevels_def
#print axioms AvailableChain.Gen.AC.ACReads.gatePrefixes_def
#print axioms AvailableChain.Gen.AC.ACReads.gateLeases_def
#print axioms AvailableChain.Gen.AC.ACReads.gateFast_def
#print axioms AvailableChain.Gen.AC.GateWrite_def
#print axioms AvailableChain.Gen.AC.Reconcile_def
#print axioms AvailableChain.Gen.AC.GateWriteSpec_def

-- Proofs/Pure/FirstBad.lean
#print axioms AvailableChain.Gen.Pure.AGRule.holds
#print axioms AvailableChain.Gen.Pure.firstFailure_holds
#print axioms AvailableChain.Gen.Pure.WindowRule.holds

-- Proofs/Pure/Schedule.lean
#print axioms AvailableChain.Gen.Pure.RecPat.recPat_mono
#print axioms AvailableChain.Gen.Pure.lr_recS
#print axioms AvailableChain.Gen.Pure.ls_recS
#print axioms AvailableChain.Gen.Pure.lr_recF
#print axioms AvailableChain.Gen.Pure.ls_recF
#print axioms AvailableChain.Gen.Pure.lr_recF4
#print axioms AvailableChain.Gen.Pure.ls_recF4
#print axioms AvailableChain.Gen.Pure.lr_recSkip
#print axioms AvailableChain.Gen.Pure.ls_recSkip
#print axioms AvailableChain.Gen.Pure.lr_strong
#print axioms AvailableChain.Gen.Pure.ls_strong
#print axioms AvailableChain.Gen.Pure.wE_recS
#print axioms AvailableChain.Gen.Pure.wE_recF
#print axioms AvailableChain.Gen.Pure.wE_recF4
#print axioms AvailableChain.Gen.Pure.wE_recSkip
#print axioms AvailableChain.Gen.Pure.wE_strongW
#print axioms AvailableChain.Gen.Pure.wE_lit
#print axioms AvailableChain.Gen.Pure.wEAt_recC
#print axioms AvailableChain.Gen.Pure.wEAtA_value
#print axioms AvailableChain.Gen.Pure.sanity_recSkip
#print axioms AvailableChain.Gen.Pure.patAt_recS
#print axioms AvailableChain.Gen.Pure.patAt_recF
#print axioms AvailableChain.Gen.Pure.patAt_recF4
#print axioms AvailableChain.Gen.Pure.patAt_recSkip
#print axioms AvailableChain.Gen.Pure.patAt_strong
#print axioms AvailableChain.Gen.Pure.strong_two
#print axioms AvailableChain.Gen.Pure.holds_iff_recS
#print axioms AvailableChain.Gen.Pure.holds_iff_recF
#print axioms AvailableChain.Gen.Pure.holds_iff_recF4
#print axioms AvailableChain.Gen.Pure.holds_iff_recSkip
#print axioms AvailableChain.Gen.Pure.holds_iff_strongW
#print axioms AvailableChain.Gen.Pure.holds_iff_lit
#print axioms AvailableChain.Gen.Pure.holds_iff_recC
#print axioms AvailableChain.Gen.Pure.holds_iff_fgood
#print axioms AvailableChain.Gen.Pure.holds_iff_fgood4
#print axioms AvailableChain.Gen.Pure.inWindow_one
#print axioms AvailableChain.Gen.Pure.recS_min
#print axioms AvailableChain.Gen.Pure.recF_min
#print axioms AvailableChain.Gen.Pure.recF4_min
#print axioms AvailableChain.Gen.Pure.recSkip_min
#print axioms AvailableChain.Gen.Pure.strongPair_iff
#print axioms AvailableChain.Gen.Pure.lit_min
#print axioms AvailableChain.Gen.Pure.recC_min
#print axioms AvailableChain.Gen.Pure.QualSearch_iff_recPat
#print axioms AvailableChain.Gen.Pure.QualSearch.of_recS
#print axioms AvailableChain.Gen.Pure.QualSearch.of_lit
#print axioms AvailableChain.Gen.Pure.QualSearch.of_recC
#print axioms AvailableChain.Gen.Pure.idx_lex
#print axioms AvailableChain.Gen.Pure.slotReading
#print axioms AvailableChain.Gen.Pure.compat_finForm
#print axioms AvailableChain.Gen.Pure.slot_le_last
#print axioms AvailableChain.Gen.Pure.event_le_windowEnd
#print axioms AvailableChain.Gen.Pure.event_le_windowEndAt
#print axioms AvailableChain.Gen.Pure.FinForm.len_pos
#print axioms AvailableChain.Gen.Pure.strong_all

-- Proofs/Pure/Props.lean
#print axioms AvailableChain.Gen.Pure.compatOn_of_compatAt_mono_statement
#print axioms AvailableChain.Gen.Pure.compatOn_of_compatAt_mono
#print axioms AvailableChain.Gen.Pure.servedOn_mono_statement
#print axioms AvailableChain.Gen.Pure.servedOn_mono

-- Proofs/Pure/BlockOrder.lean
#print axioms AvailableChain.Gen.Pure.block_preceq_refl
#print axioms AvailableChain.Gen.Pure.block_preceq_trans
#print axioms AvailableChain.Gen.Pure.block_preceq_antisymm
#print axioms AvailableChain.Gen.Pure.block_genesis_preceq
#print axioms AvailableChain.Gen.Pure.block_preceq_total_of_common
#print axioms AvailableChain.Gen.Pure.block_compatible_comm
#print axioms AvailableChain.Gen.Pure.block_compatible_of_common
#print axioms AvailableChain.Gen.Pure.block_incompatible_of_preceq
#print axioms AvailableChain.Gen.Pure.block_compatible_of_preceq_compatible
#print axioms AvailableChain.Gen.Pure.prefix_depth
#print axioms AvailableChain.Gen.Pure.prefix_eq_of_depth
#print axioms AvailableChain.Gen.Pure.path_child
#print axioms AvailableChain.Gen.Pure.pathNodes_spec
#print axioms AvailableChain.Gen.Pure.two_conflicts
#print axioms AvailableChain.Gen.Pure.deepest_of_compatible

-- Proofs/V2/Fields.lean
#print axioms AvailableChain.Gen.V2.ownRecord_fold_restart

-- Proofs/V2/Reads.lean
#print axioms AvailableChain.Gen.V2.stateBefore_idxBefore_statement
#print axioms AvailableChain.Gen.V2.stateBefore_idxBefore
#print axioms AvailableChain.Gen.V2.pubFloor_le
#print axioms AvailableChain.Gen.V2.publicTime_le_pubFloor
#print axioms AvailableChain.Gen.V2.index_lt_idxBefore_iff
#print axioms AvailableChain.Gen.V2.holdsBefore_iff_exists_idx_statement
#print axioms AvailableChain.Gen.V2.holdsBefore_iff_exists_idx

-- Proofs/V2/Induction.lean
#print axioms AvailableChain.Gen.V2.invariant_triple
#print axioms AvailableChain.Gen.V2.invariant_clock_free
#print axioms AvailableChain.Gen.V2.interval_induction_all
#print axioms AvailableChain.Gen.V2.write_once_along_run
#print axioms AvailableChain.Gen.V2.kept_from_seed

-- Proofs/V2/BaseTransport.lean
#print axioms AvailableChain.Gen.V2.base_invariant
#print axioms AvailableChain.Gen.V2.base_invariant_holdsBefore

-- Proofs/V2/Receipt.lean
#print axioms AvailableChain.Gen.V2.deliveryWithin_of_partialSynchrony
#print axioms AvailableChain.Gen.V2.deliveryWithin_of_healthyPrefix
#print axioms AvailableChain.Gen.V2.timely_of_clock_statement
#print axioms AvailableChain.Gen.V2.timely_of_emit_statement
#print axioms AvailableChain.Gen.V2.timely_of_relay_statement
#print axioms AvailableChain.Gen.V2.firstAccept_of_processed_statement
#print axioms AvailableChain.Gen.V2.timely_of_clock
#print axioms AvailableChain.Gen.V2.timely_of_emit
#print axioms AvailableChain.Gen.V2.timely_of_relay
#print axioms AvailableChain.Gen.V2.firstAccept_of_processed
#print axioms AvailableChain.Gen.V2.accepted_by_deadline_statement
#print axioms AvailableChain.Gen.V2.accepted_by_deadline

-- Proofs/V2/Regimes.lean
#print axioms AvailableChain.Gen.V2.LabelSync.dl_vt_le
#print axioms AvailableChain.Gen.V2.LabelSync.relayBy
#print axioms AvailableChain.Gen.V2.LabelSync.of_cleanCut
#print axioms AvailableChain.Gen.V2.LabelSync.of_recovery
#print axioms AvailableChain.Gen.V2.LabelFacts.of_cleanCut
#print axioms AvailableChain.Gen.V2.LabelFacts.of_recovery

-- Proofs/AC/Output.lean
#print axioms AvailableChain.Gen.AC.output_step_of_restartFree
#print axioms AvailableChain.Gen.AC.gateWrite_of_scheduleWellFormed_statement
#print axioms AvailableChain.Gen.AC.gateWrite_of_scheduleWellFormed

-- Statements/AC/Lease.lean
#print axioms AvailableChain.Gen.AC.LeaseChainStatement_def
#print axioms AvailableChain.Gen.AC.PendingGateHarmlessStatement_def
#print axioms AvailableChain.Gen.AC.UniqueLeaseKeys_def
#print axioms AvailableChain.Gen.AC.LeaseMapChain_def
#print axioms AvailableChain.Gen.AC.ProtectsUntil_def

-- Proofs/AC/Lease.lean
#print axioms AvailableChain.Gen.AC.lease_chain_statement
#print axioms AvailableChain.Gen.AC.pendingGate_harmless_statement
#print axioms AvailableChain.Gen.AC.lease_chain
#print axioms AvailableChain.Gen.AC.pendingGate_harmless
#print axioms AvailableChain.Gen.AC.write_unique_keys
#print axioms AvailableChain.Gen.AC.deadlineOf_eq_of_lease_row
#print axioms AvailableChain.Gen.AC.write_protectsUntil
#print axioms AvailableChain.Gen.AC.expire_protectsUntil
#print axioms AvailableChain.Gen.AC.release_protectsUntil
#print axioms AvailableChain.Gen.AC.release_of_supporters

-- Proofs/Pure/Quorum.lean
#print axioms AvailableChain.Gen.Pure.count_rec
#print axioms AvailableChain.Gen.Pure.count_clean
#print axioms AvailableChain.Gen.Pure.quorum_honest
#print axioms AvailableChain.Gen.Pure.quorum_intersection
#print axioms AvailableChain.Gen.Pure.quorum_inter_honest

-- Statements/Pure/QuorumInter.lean and the unit-seat proofs.
#print axioms AvailableChain.Gen.Pure.FaultXInterHonestStatement_def
#print axioms AvailableChain.Gen.Pure.faultX_inter_honest_statement
#print axioms AvailableChain.Gen.Pure.FaultX.inter_honest

-- Statements/Pure/SupportCounts.lean and Proofs/Pure/SupportCounts.lean
#print axioms AvailableChain.Gen.Pure.TwoMajoritiesIntersectStatement_def
#print axioms AvailableChain.Gen.Pure.two_majorities_intersect_statement
#print axioms AvailableChain.Gen.Pure.two_majorities_intersect

-- Proofs/Pure/Fold.lean
#print axioms AvailableChain.Gen.Pure.fold_field
#print axioms AvailableChain.Gen.Pure.foldl_select_mem
#print axioms AvailableChain.Gen.Pure.find?_congr_mem

-- Statements/AC/History.lean and Proofs/AC/History.lean
#print axioms AvailableChain.Gen.AC.GenuineExtends_def
#print axioms AvailableChain.Gen.AC.GenuineContinues_def
#print axioms AvailableChain.Gen.AC.GenuineHistory_def
#print axioms AvailableChain.Gen.AC.genuine_history_induction

-- Statements/AC/Transfer.lean
#print axioms AvailableChain.Gen.AC.GateService_def
#print axioms AvailableChain.Gen.AC.GateOfCoveringBatchStatement_def
#print axioms AvailableChain.Gen.AC.SEqOfExactStatement_def

-- Proofs/AC/Transfer.lean
#print axioms AvailableChain.Gen.AC.gate_of_coveringBatch_statement
#print axioms AvailableChain.Gen.AC.S_eq_of_exact_statement
#print axioms AvailableChain.Gen.AC.gate_of_coveringBatch
#print axioms AvailableChain.Gen.AC.S_eq_of_exact

-- Statements/V2/Linked.lean and Proofs/V2/Linked.lean
#print axioms AvailableChain.Gen.V2.LinkedHolderEqStatement_def
#print axioms AvailableChain.Gen.V2.LinkedCardLeOfHoldersStatement_def
#print axioms AvailableChain.Gen.V2.linked_holder_eq_statement
#print axioms AvailableChain.Gen.V2.linked_holder_eq
#print axioms AvailableChain.Gen.V2.linked_card_le_of_holders_statement
#print axioms AvailableChain.Gen.V2.linked_card_le_of_holders

-- Statements/V2/Signatures.lean and Proofs/V2/Signatures.lean
#print axioms AvailableChain.Gen.V2.EmittedUniquePerLabelStatement_def
#print axioms AvailableChain.Gen.V2.HonestUniquePerLabelStatement_def
#print axioms AvailableChain.Gen.V2.emitted_unique_per_label_statement
#print axioms AvailableChain.Gen.V2.emitted_unique_per_label
#print axioms AvailableChain.Gen.V2.honest_unique_per_label_statement
#print axioms AvailableChain.Gen.V2.honest_unique_per_label

-- Statements/V2/Slashing.lean
#print axioms AvailableChain.Gen.V2.HonestNeverSlashed_def

-- Proofs/Pure/Walk.lean
#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_statement
#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix
#print axioms AvailableChain.Gen.Pure.walk_exact_of_dominated_suffix_statement
#print axioms AvailableChain.Gen.Pure.walk_exact_of_dominated_suffix
#print axioms AvailableChain.Gen.Pure.walk_reanchor_of_dominated_suffix_statement
#print axioms AvailableChain.Gen.Pure.walk_reanchor_of_dominated_suffix
#print axioms AvailableChain.Gen.Pure.walk_avoids_unsupported_child_statement
#print axioms AvailableChain.Gen.Pure.walk_avoids_unsupported_child
#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_of_anchor_eligible_statement
#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_of_anchor_eligible
#print axioms AvailableChain.Gen.Pure.walk_terminal_of_descendant_depth_bound_statement
#print axioms AvailableChain.Gen.Pure.walk_terminal_of_descendant_depth_bound
#print axioms AvailableChain.Gen.Pure.walk_noEligibleChild_of_anchorClosed_statement
#print axioms AvailableChain.Gen.Pure.walk_noEligibleChild_of_anchorClosed
#print axioms AvailableChain.Gen.Pure.ghost_transfer_sfx_statement
#print axioms AvailableChain.Gen.Pure.ghost_transfer_sfx

-- Statements/AC/Votes.lean
#print axioms AvailableChain.Gen.AC.voteSupports_def
#print axioms AvailableChain.Gen.AC.poolSupports_def
#print axioms AvailableChain.Gen.AC.plainSupporters_def
#print axioms AvailableChain.Gen.AC.TransferBounds_def
#print axioms AvailableChain.Gen.AC.TransferStatement_def
#print axioms AvailableChain.Gen.AC.BatchBounds_def
#print axioms AvailableChain.Gen.AC.BatchCountsStatement_def
#print axioms AvailableChain.Gen.AC.TransferN2Statement_def
#print axioms AvailableChain.Gen.AC.ScoreEqOnStatement_def
#print axioms AvailableChain.Gen.AC.CapVoteStatement_def
#print axioms AvailableChain.Gen.AC.CapPairStatement_def
#print axioms AvailableChain.Gen.AC.BatchStatement_def

-- Proofs/AC/Votes.lean
#print axioms AvailableChain.Gen.AC.vote_pool_eraseDups_nodup
#print axioms AvailableChain.Gen.AC.cap_pair_statement
#print axioms AvailableChain.Gen.AC.cap_pair
#print axioms AvailableChain.Gen.AC.cap_vote_statement
#print axioms AvailableChain.Gen.AC.cap_vote
#print axioms AvailableChain.Gen.AC.vote_pool_mem_seats
#print axioms AvailableChain.Gen.AC.vote_pool_voterCount_card
#print axioms AvailableChain.Gen.AC.vote_pool_support_witness
#print axioms AvailableChain.Gen.AC.vote_pool_support_ancestor
#print axioms AvailableChain.Gen.AC.vote_pool_support_compatible
#print axioms AvailableChain.Gen.AC.vote_pool_clean_unique
#print axioms AvailableChain.Gen.AC.vote_pool_equivocates_mono
#print axioms AvailableChain.Gen.AC.vote_pool_clean_subset
#print axioms AvailableChain.Gen.AC.vote_pool_equivocates_participant
#print axioms AvailableChain.Gen.AC.vote_pool_seats_subset
#print axioms AvailableChain.Gen.AC.vote_pool_seats_backward
#print axioms AvailableChain.Gen.AC.vote_pool_score_card
#print axioms AvailableChain.Gen.AC.vote_pool_plain_subset_score
#print axioms AvailableChain.Gen.AC.vote_pool_support_conflict
#print axioms AvailableChain.Gen.AC.batch_counts_statement
#print axioms AvailableChain.Gen.AC.batch_counts
#print axioms AvailableChain.Gen.AC.transfer_n2_statement
#print axioms AvailableChain.Gen.AC.transfer_n2
#print axioms AvailableChain.Gen.AC.score_eq_on_statement
#print axioms AvailableChain.Gen.AC.score_eq_on
#print axioms AvailableChain.Gen.AC.transfer_statement
#print axioms AvailableChain.Gen.AC.transfer

-- Statements/AC/LeaseWindow.lean
#print axioms AvailableChain.Gen.AC.SlowWindowConflictAbsurdStatement_def
#print axioms AvailableChain.Gen.AC.ExpireByThresholdStatement_def

-- Proofs/AC/Lease.lean (G26)
#print axioms AvailableChain.Gen.AC.slow_window_conflict_absurd_statement
#print axioms AvailableChain.Gen.AC.slow_window_conflict_absurd
#print axioms AvailableChain.Gen.AC.expire_by_threshold_statement
#print axioms AvailableChain.Gen.AC.expire_by_threshold
