# P-Ou round 2 — closure handoff

Base: babc0460 (sleep-int 03aecc74 plus S-Ap P15-CUT ddfe84be).
P-Ou is PREPARED, not CLOSED. This file records required inputs and ports.

P-Cl2's exact growth suppliers are installed at Outage/Export:166, after
`end CleanClaims`. The old section includes do not bind this theorem.
The public claim has no new premise. Claims/Outage already had the approved
independent trigger/deadline reader scopes; only its comment changed.
GrowthConsumer contains the actual unfolded production body, not a private
copy. Its build passes. The mixed Export build fails in its other imports.
Do not count that lower build as closure of the mixed Export.

Growth inputs:
- P-Cl1/P-Cl2: produce CleanTruncAt at the horizon from the sleep cut and
  compile production Clean/Export. Its public-output compatibility projection
  is the hOutputs argument of clean_growth_compatible_of_outputs.
- P-Ou: produce one confirmed inclusion witness at g(s) for each supplied
  honest proposal B. The witness is exactly
  `exists y, confirmedReader y g(s) and B <= S_at(timeIdx g(s),y)`.
  Together with hOutputs, the compiled compatibility proof covers every
  earlier confirmed trigger reader, even if that reader sleeps later.
- P-Ou: port inclusion_retained_reads/exact HEAD and InclusionGate* to
  confirmed readers, enabled gates, joined transfer and local epochs. Then
  prove scoped clean_inclusion_body for all later confirmed reads. Neither
  growth supplier is yet derived completely from CleanSet.
- P-ShA interfaces exist: use RegimesService *_on and exact retained
  geometry/ScoreServiceScope. P-Ou must derive those local inputs; past
  processing does not imply retained HistorySafeAt after restart.

P-Ar inputs:
- clean_epoch_saved_row from the running P-Cl1 round 2 is still absent here.
- Close corrected arming_prefix_batch_receipt, protected-receiver origins
  and arming seeds. The required prefix service includes earlyTime q <= b0.
- The origin supplies a gate at/before b0. outage_prefix_cut_of_origin then
  gives 6*delta <= b0; outage_prefix_label_cut gives the per-label bound.
  Genesis uses block_genesis_preceq and needs no pending prefix receipt.
- The round-1 unrestricted transfer defect is repaired in landed
  arming_head_ge_on and arming_healthy_batch: both use the joined guard.
- ArmingDuty:122/130 still fails at the joined act branches; :181 still
  supplies the old root idealization to a receipt theorem.
- ArmingGate:156/221 still uses old gate equations; :268 lacks the enabled
  marker; :316 lacks the exact receiver awake fact.
- Supply lower GREEN arming_write_row, arming_writeKeys_stable and
  arming_gateResult_tick (with its enabled guard) for PersistenceStep.
  P-Ou does not edit or duplicate P-Ar producers.

P-Ou receipt callers:
- ContinuationPaths:17/44 uses ReceiptCoverageAnchorPremises and
  fgsa_active_path_of_coverage_anchor. Both production consumers build.
- Remaining ContinuationReceipt calls need exact local coverage. The
  regression/early-gate calls anchor at v(s), deadline e(s); the frozen
  transfer call anchors at e(s), deadline f(s). ReadyTrigger, HistorySafeAt,
  handlers and restartFree must refer to that same anchor. Bind pathCoverage
  to dl(anchor o t). Do not supply dl(anchor)=dl(send) or global NoRestart.
- The public restored service still needs fresh HEAD/target dependencies,
  retained-history safety, compatible finality and survival at each of the
  early, freeze and proposal cuts. No public receipt premise was added.

Good votes and writes:
- outage_good_batch_of_e derives the exact good-seat majority and the late
  complement bound by A union W from Base2 and E, at every receiver store.
- outageV_gate_of_receipts uses that opponent cardinality as its internal
  count parameter. Membership, strict stamps and compatible targets are
  still service/joint-invariant inputs.
- outage_gate_writeKeys_compatible proves compatibility of newly written
  gate rows when the passed result is compatible. It allows old conflicting
  rows. The all-honest late-write invariant is still open.
- Full good-vote compatibility, late-write exclusion, both joint inductions
  and the handover at v(r+k+1) remain P-Ou work after arming/service inputs.
- T31/T35/T37 still need actual earlier witnesses or proofs that avoid the
  ticks. T61 now requests confirmedReaderAtIdx at the post-gate cut and gets
  awake only for that reader; its full test module waits on InclusionGate*.

Other owners:
- P-As: port Shared/Claims and Assembly/Outage to the two growth suppliers
  and the approved scoped conclusions. Shared/Claims fails on this base.
- S-Ap: D013 and P15-CUT are installed; no new defect was found in the
  corrected prefix predicate. The Run facade and Run.Tests.Axioms stay
  EXPECTED-FAIL in this map. Claims/Statements was not edited.
- P-Da: register GrowthConsumer, ContinuationPaths and GoodVotes in the
  architecture map and canonical audit inventory. No shared exception,
  baseline, checker or scope row was changed.
- Canonical audit moves: the two receipt names move from ContinuationReceipt
  to ContinuationPaths; outageV_gate_of_receipts moves from ContinuationGate
  to GoodVotes. SleepAxioms and P-Ou.coverage-fragment.txt audit all 59 names.
