# Sleep premise ledger

Before G-S0, each package records one row per internal theorem that uses a proposed
premise. Use packet row IDs from plan §5.1. At G-S0, change each status to approved
or rework. P-Da keeps this file as a record.

```text
┌──────────────┬──────────────┬─────────────┬────────────────────┐
│ Theorem name │ File         │ Packet rows │ Status             │
├──────────────┼──────────────┼─────────────┼────────────────────┤
└──────────────┴──────────────┴─────────────┴────────────────────┘
```

## W2a — approved packet, 2026-10-10

Approval: `sleep-packet-approved.md`, P1–P24, G-S0 passed.
Each row below is approved. No additional premise or public claim text is proposed.

- `Reachable.restart` — `P24`, approved.
  `AvailableChainFGSA/Statements/Invariants.lean`.
  Repair: old reset → prior reachable wipe.

- `joinedNow; joinedAtTime` — `P24`, approved.
  `AvailableChainFGSA/Model/Store.lean`.
  Repair: inclusive previous slot, integer subtraction.

- `wipe; acRestart; reachable_acRestart` — `P24`, approved.
  `AvailableChainFGSA/Model/Restart.lean`.
  `AvailableChainFGSA/Proofs/Restart.lean`.
  Repair: durable fields kept, HEAD-only replay.

- `gateStep_fresh` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Fields.lean`.
  Repair: add joinedNow at the gate input.

- `clockPre_eq` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: release gains the tick-time join guard.

- `clock_eq_saClock_offGate` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: add joinedAtTime at t.

- `clock_eq_saClockFrom_gate; gate'` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: add joinedAtTime at t.

- `storeInvariant; metadataInvariant` — `P24`, approved.
  `AvailableChainFGSA/Proofs/StoreInv.lean`.
  `AvailableChainFGSA/Proofs/Metadata.lean`.
  Repair: prior invariant supplies retained content.

- `rowsValidStored_reachable; stored_r6wW` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Metadata.lean`.
  `AvailableChainFGSA/WindowAdmissionInvariant.lean`.
  Repair: retained rows keep their validity.

- `outputNesting_stored; base_headDomain_none` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Nesting.lean`.
  `AvailableChainFGSA/Proofs/HeadDomain.lean`.
  Repair: F/S kept; headDomain cleared.

- `storeBundleInvariant` — `P24`, approved.
  `AvailableChainFGSA/Proofs/StoreBundle.lean`.
  Repair: all stored target bounds survive any w.

Constructor record: remove `AvailableChain.FGSA.Reachable.reset`;
add `AvailableChain.FGSA.Reachable.restart`. D0e-a must use the new spelling.
Run callers remain with W2b/W3; other owners are in `scripts/dev-pkg/W2a.txt`.

## W1a — 2026-10-10

Approved source: `sleep-packet-approved.md`, G-S0 approval of P1–P24 on 2026-10-09.
P1 option (a) adds the sleep parent in both engines. No weaker theorem conclusion
or extra theorem premise is proposed. The proof and fixture edits compile with `--wfail`.

P3: packet typo, r9 form `.restart v t`. The lead approved this correction on
2026-10-10. Both World.step branches now bind and pass the restart time.
This fixes an unbound name; it changes no approved meaning.

File keys (all relative to the repository):
- EngineLift: `AvailableChainEngineV2/Engine/Duty/Lift.lean`.
- Lift: `AvailableChainEngineV2/Conditions/Duty/Lift.lean`.
- Self: `AvailableChainEngineV2/Laws/SelfDelivery.lean`.
- DSelf: `AvailableChainEngineV2/Laws/Duty/SelfDelivery.lean`.
- Run/DRun: `AvailableChainEngineV2/Engine/{Run,Duty/Run}.lean`.
- Schedule/DSchedule: `AvailableChainEngineV2/Conditions/{Schedule,Duty/Schedule}.lean`.
- Delivery/DDelivery: `AvailableChainEngineV2/Conditions/{Delivery,Duty/Delivery}.lean`.
- Clock/DClock: `AvailableChainKitV2/{ClockLaws,DutyClockLaws}.lean`.

`approved; built` records text approval and successful compilation.
The writer does not claim that the required external reviews are complete.
The Lift theorem names below have the prefix `AvailableChain.V2.D.`.

```text
┌─────────────────────────────────────────────┬──────────────┬───────────┬─────────────────────┐
│ Declaration                                 │ File         │ Packet    │ Status              │
├─────────────────────────────────────────────┼──────────────┼───────────┼─────────────────────┤
│ sleepWellFormed_toD_iff                     │ Lift         │ P1(a)     │ approved; built     │
│ restartsAtWakes_toD_iff                     │ Lift         │ P1        │ approved; built     │
│ noRestartOn_toD_iff                         │ Lift         │ P1        │ approved; built     │
│ noRestartAfter_toD_iff                      │ Lift         │ P1        │ approved; built     │
│ linkReadyOn_toD_iff                         │ Lift         │ P1, P2    │ approved; built     │
│ processedByActionCut_toD_iff                │ Lift         │ P1, P2    │ approved; built     │
│ handledBetween_toD_iff                      │ Lift         │ P2        │ approved; built     │
│ deliveryService_toD_iff                     │ Lift         │ P2        │ approved; built     │
│ deliveryDemand_toD_iff                      │ Lift         │ P2        │ approved; built     │
│ scheduleWellFormed_toD_iff                  │ Lift         │ P1(a)     │ approved; built     │
│ partialSynchrony_toD_iff                    │ Lift         │ P2        │ approved; built     │
│ healthyPrefixDelivery_toD_iff               │ Lift         │ P2        │ approved; built     │
│ executionValid_toD_iff                      │ Lift         │ P1(a)     │ approved; built     │
│ ExecutionValid.snoc_selfDelivery            │ Self         │ P1(a)     │ approved; built     │
│ ExecutionValid.snoc_selfDelivery            │ DSelf        │ P1(a)     │ approved; built     │
│ ExecutionValid (sleep parent)               │ Schedule     │ P1(a)     │ approved; built     │
│ ExecutionValid (sleep parent)               │ DSchedule    │ P1(a)     │ approved; built     │
│ PartialSynchrony / HealthyPrefixDelivery    │ Delivery     │ P2        │ approved; built     │
│ PartialSynchrony / HealthyPrefixDelivery    │ DDelivery    │ P2        │ approved; built     │
│ World.step restart                          │ Run          │ P3        │ approved; built     │
│ World.step restart                          │ DRun         │ P3        │ approved; built     │
│ RestoreTimeLaw                              │ Clock        │ P3        │ approved; built     │
│ RestoreTimeLaw                              │ DClock       │ P3        │ approved; built     │
│ world_step_toD                              │ EngineLift   │ P3        │ approved; built     │
└─────────────────────────────────────────────┴──────────────┴───────────┴─────────────────────┘
```

Continuation corrections:

```text
┌───────────────────────────────────────────────────────────┬──────────────────────┐
│ Ledger row                                                │ Status               │
├───────────────────────────────────────────────────────────┼──────────────────────┤
│ P3: packet typo, r9 form `.restart v t`                   │ approved; built      │
│ P1: NoRestartOn/After event index annotated `(i : Nat)`   │ same predicate       │
│ P2: negative delivery test horizon set to its deadline, 2 │ fixture only; built  │
└───────────────────────────────────────────────────────────┴──────────────────────┘
```

The P1 annotation resolves an ambiguous List index instance in both twins.
It changes no quantifier domain from the intended event index in r9 and D0a.
The P2 fixture formerly ended at 1. Its deadline 2 is outside that horizon,
so the approved demand has no obligation. The local test now ends at 2.
No approved statement has a weaker conclusion, new premise, or changed quantifier.

Writer validation: DCK PASS (package W1a), with the brief's controls exception.
The normal run passed builds and strict audits, then the old P-PC control map
rejected the five new W1a modules. The NEG=0 run passed in 88.14 s.
Checker scripts are unchanged; the sleep-int controls fix was not merged.
The required Sol and Opus reviews remain with the lead.

## W2a continuation — lead rulings, 2026-10-10

The lead approved the two corrections after merge `02531030`.
`clock_namedBodies` in `AvailableChainFGSA/Proofs/NamedStore.lean`
keeps its type and uses `clock_proposals` from `Proofs/Fields.lean`.
This proof-only edit is approved outside plan §14.2.
Validation uses the default repository heartbeat config.
No source heartbeat limit is increased.

Two modules omitted from plan §14.6 are EXPECTED-FAIL, owner W3:
- `AvailableChainFGSARun.Proofs.AncestorDeadlinesStore`: gate unfolds
  at lines 455, 465 and 485 do not handle the unjoined branch.
- `AvailableChainFGSARun.Proofs.AncestorDeadlines`: imports that failed module.

Both modules stay REQUIRED at S1. The W2a package map now includes
the five new W1a modules from the merged S1 list as GREEN.
`NamedStore` is a W2a TARGET for the approved proof repair.

W1a merge failures are assigned by plan §14.6/§8.1 and the merged W1a map.
The failed modules are:
- `AvailableChainFGCompose.Statements.SafetyClient` — W3.
- `AvailableChainFGCompose.Statements.SafetyStore` — W3.
- `AvailableChainFGCompose.Tests.Restart` — W3.
- `AvailableChainFGSARun.Model.Protocol` — W2b.
- `AvailableChainGeneric.Proofs.V2.Fields` — W1b.
- `AvailableChainGeneric.Statements.V2.Duty.Receipt` — W1b.
- `AvailableChainGeneric.Statements.V2.Receipt` — W1b.
- `AvailableChainKitV2.DutyEngineClock` — W1b.
- `AvailableChainKitV2.DutyRecord` — W1b.
- `AvailableChainKitV2.EngineClock` — W1b.
- `AvailableChainKitV2.Tests.Toy` — W1b.

These 11 failures affect 106 prior GREEN entries through imports.
Additional EXPECTED-FAIL owners: W1b 34, W2b 32, W3 14, P-ShA 13, S-Ap 13.
The final W2a map has 34 TARGETS, 273 GREEN and 176 EXPECTED-FAIL entries.
All 110 W2a store/pin targets stay GREEN. No S1 entry moves to DEFERRED.
The W1b and W3 owners have approved statement repairs in plan r9.
This continuation changes no statement and adds no premise.

Writer checkpoint: DCK PASS (package W2a), with all controls, 109.716 s.
Default-config GREEN build: PASS, 273 module targets, 2.852 s.
Strict FGSA audit: PASS, 822 results, 42.343 s.
Scoped FGSA coverage: PASS, 0 unaccepted exports, 19.902 s.
The coverage inventory is unchanged. Astra review remains with the lead.

## W2b — approved work and stopped items, 2026-10-10

Approval: `sleep-packet-approved.md`, P1–P24; G-S0 passed.
The model text follows the approved `actS` and `fgsa` blocks.
Line breaks in `actS` keep lines at or below 100 characters.
No packet typo was found in these blocks.

- `actS; fgsa` — `P3, P24`, approved.
  `AvailableChainFGSARun/Model/Protocol.lean`.
  Repair: joined HEAD/proposal duties; keep the durable store and Λ.
- `fgsaClock; fgsa_clock_now` — `P3, P24`, approved, types kept.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  Move from ClockLaws to avoid the stopped Protocol and W1b proof imports.
- `fgsaRestoreTimeLaw; fgsa_restore_now` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  Repair: the clock equals the exact wake time.
- `restore_st; restore_rec; fgsa_restore_record` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  `restore_st` replaces `restore_st_retained`; `restore_rec` gains the wake argument.
- `fgsa_restore_restartTime; fgsa_restore_fg; fgsa_restore_rowPool` —
  `P3, P24`, approved, `AvailableChainFGSARun/Proofs/Restore.lean`.
- `fgsa_restore_proposals; fgsa_restore_namedBodies; fgsa_restore_blocks` —
  `P3, P24`, approved, `AvailableChainFGSARun/Proofs/Restore.lean`.
- `fgsa_restore_obligations; fgsa_restore_stableRecord` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
- `fgsa_restore_reachable; fgsa_reachable_stateBefore` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  Use the pre-restart reachability proof, with no W1b declaration.
- `reachable_stateBefore; namedOrigin_reachable` — `P3, P24`, approved, types kept.
  `AvailableChainFGSARun/Proofs/{Reachable,NamedOrigins}.lean`.
  Both reset sites use the compiled retained-store reachability bridge.
  Their whole modules remain blocked by other statements/imports.
- `fgsa_restore_now_retained; fgsa_hrestore_now_retained` — `P3, P24`, superseded.
  `AvailableChainFGSARun/Proofs/ClockLaws.lean`.
  The new exact-wake laws replace the last-tick laws.
- `fgsa_hrestore_retained; fgsa_hrestore_field_retained` — stopped; ruling required.
  `AvailableChainFGSARun/Proofs/ClockLaws.lean`.
  Reset-to-genesis premises no longer apply. Keep their text pending a ruling;
  the new laws already prove the approved retained-field behavior.
- `stored_proposal_delivered` — stopped; meaning ruling required.
  `AvailableChainFGSARun/Proofs/Reachable.lean`.
  The current-epoch conclusion is false when proposals survive restart.
  Keep its text; do not add a premise or weaken the conclusion without a ruling.
- `act_prop` — stopped; meaning ruling required.
  `AvailableChainFGSARun/Proofs/Protocol.lean`.
  Its unconditional result conflicts with the approved joined `actS`.
  `act_prop_zero` needs a proof repair after this item is released.
- `fgsa_stateBefore_bounds` reset site — stopped; integration ruling required.
  `AvailableChainFGSARun/Proofs/Schedule.lean`.
  Its induction uses the superseded retained-clock helper and resets to genesis.
  The module also imports W1b clock proofs and contains the false strict bound below.
- `fgsa_preTick_now_lt; fgsa_release_votes_stamped` — stopped; meaning ruling required.
  `AvailableChainFGSARun/Proofs/Schedule.lean`.
  A wake at a tick time gives pre-tick now = tick time, and replay stamps can equal it.
  `SleepTests.wake_at_tick` is a valid-run counterexample to the strict clock bound.

The package is not closed. The stopped statements and the Schedule reset site
need a lead ruling and W3 integration. No stopped statement has changed meaning.

- `SleepTests.valid` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.non_public_wake` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.receipt_before_tick` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.durable_run` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.retained_not_fresh` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.join_valid` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.join_duties` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.wake_at_tick` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.initial_duties` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.
## W1b — 2026-10-10

Source: approved P2/P3/P24 packet and r9 §2.2, §4.1. The 15 replacement texts
match the packet exactly. No packet typo correction or meaning change was needed.
The old NoRestart and restartFree forms remain. Their companions state restore
preservation or RestoreTimeLaw. The old delivery lower bound adds receiver awake
at its public anchor, as r9 permits. The new full-sleep bound uses ExecutionValid.
Receipt wrappers now require readiness, history safety, and explicit acceptance.

File keys (paths are relative to this repository):
- B1: `AvailableChainGeneric/Proofs/V2/Duty/DeliveryBy.lean`.
- B2: `AvailableChainGeneric/Proofs/V2/Duty/Fields.lean`.
- B3: `AvailableChainGeneric/Proofs/V2/Duty/Induction.lean`.
- B4: `AvailableChainGeneric/Proofs/V2/Duty/Reads.lean`.
- B5: `AvailableChainGeneric/Proofs/V2/Duty/Receipt.lean`.
- B6: `AvailableChainGeneric/Proofs/V2/Duty/Sleep.lean`.
- B7: `AvailableChainGeneric/Proofs/V2/Fields.lean`.
- B8: `AvailableChainGeneric/Proofs/V2/Induction.lean`.
- B9: `AvailableChainGeneric/Proofs/V2/Reads.lean`.
- B10: `AvailableChainGeneric/Proofs/V2/Receipt.lean`.
- B11: `AvailableChainGeneric/Proofs/V2/Sleep.lean`.
- B12: `AvailableChainGeneric/Statements/V2/Duty/DeliveryBy.lean`.
- B13: `AvailableChainGeneric/Statements/V2/Duty/Receipt.lean`.
- B14: `AvailableChainGeneric/Statements/V2/Receipt.lean`.
- B15: `AvailableChainKitV2/DutyEngineClock.lean`.
- B16: `AvailableChainKitV2/DutyExecution.lean`.
- B17: `AvailableChainKitV2/DutyRecord.lean`.
- B18: `AvailableChainKitV2/DutySleep.lean`.
- B19: `AvailableChainKitV2/DutyStable.lean`.
- B20: `AvailableChainKitV2/Emission.lean`.
- B21: `AvailableChainKitV2/EngineClock.lean`.
- B22: `AvailableChainKitV2/Execution.lean`.
- B23: `AvailableChainKitV2/Sleep.lean`.
- B24: `AvailableChainKitV2/Stable.lean`.

Rows include the changed records, wrappers, and exported proof dependencies.
P1 denotes the adopted full-sleep vocabulary; P3 denotes exact restore time.
Status is statement approval; the final report gives build and audit results.

```text
┌──────────────────────────────────────────────────┬───────┬───────────┬────────────┐
│ Declaration                                      │ File  │ Packet    │ Status     │
├──────────────────────────────────────────────────┼───────┼───────────┼────────────┤
│ deliveryWithinOn_of_partialSynchronyBy_statement │ B1    │ P2, P24   │ approved   │
│ deliveryWithinOn_of_healthyPrefixBy_statement    │ B1    │ P2, P24   │ approved   │
│ accepted_by_deadline_on_statement                │ B1    │ P2, P24   │ approved   │
│ accepted_by_deadline_on                          │ B1    │ P2, P24   │ approved   │
│ ownRecord_fold_restart                           │ B2    │ P3, P24   │ approved   │
│ invariant_triple                                 │ B3    │ P3, P24   │ approved   │
│ invariant_clock_free                             │ B3    │ P3, P24   │ approved   │
│ holdsBefore_iff_exists_idx_restore               │ B4    │ P3, P24   │ approved   │
│ timely_of_relay_statement                        │ B5    │ P3, P24   │ approved   │
│ timely_of_relay                                  │ B5    │ P3, P24   │ approved   │
│ historySafeAt_of_fresh                           │ B5    │ P2, P24   │ approved   │
│ historySafeAt_of_processed_mono                  │ B5    │ P2, P24   │ approved   │
│ processed_by_deadline_of_service                 │ B5    │ P2, P24   │ approved   │
│ service_of_readyTrigger                          │ B5    │ P2, P24   │ approved   │
│ ready_broadcast                                  │ B5    │ P2, P24   │ approved   │
│ ready_relay                                      │ B5    │ P2, P24   │ approved   │
│ accepted_by_deadline_statement                   │ B5    │ P2, P24   │ approved   │
│ accepted_by_deadline                             │ B5    │ P2, P24   │ approved   │
│ restartFree_actionCut_idxBefore                  │ B6    │ P1, P3    │ approved   │
│ actionCut_le_idxBefore                           │ B6    │ P1, P3    │ approved   │
│ ownRecord_fold_restart                           │ B7    │ P3, P24   │ approved   │
│ invariant_triple                                 │ B8    │ P3, P24   │ approved   │
│ invariant_clock_free                             │ B8    │ P3, P24   │ approved   │
│ holdsBefore_iff_exists_idx_restore               │ B9    │ P3, P24   │ approved   │
│ timely_of_relay_statement                        │ B10   │ P3, P24   │ approved   │
│ timely_of_relay                                  │ B10   │ P3, P24   │ approved   │
│ historySafeAt_of_fresh                           │ B10   │ P2, P24   │ approved   │
│ historySafeAt_of_processed_mono                  │ B10   │ P2, P24   │ approved   │
│ processed_by_deadline_of_service                 │ B10   │ P2, P24   │ approved   │
│ service_of_readyTrigger                          │ B10   │ P2, P24   │ approved   │
│ ready_broadcast                                  │ B10   │ P2, P24   │ approved   │
│ ready_relay                                      │ B10   │ P2, P24   │ approved   │
│ accepted_by_deadline_statement                   │ B10   │ P2, P24   │ approved   │
│ accepted_by_deadline                             │ B10   │ P2, P24   │ approved   │
│ restartFree_actionCut_idxBefore                  │ B11   │ P1, P3    │ approved   │
│ actionCut_le_idxBefore                           │ B11   │ P1, P3    │ approved   │
│ PartialSynchronyBy                               │ B12   │ P2, P24   │ approved   │
│ HealthyPrefixDeliveryBy                          │ B12   │ P2, P24   │ approved   │
│ DeliveryWithinOn                                 │ B12   │ P2, P24   │ approved   │
│ AcceptedByDeadlineOnStatement                    │ B12   │ P2, P24   │ approved   │
│ AcceptedByDeadlineOnStatement_def                │ B12   │ P2, P24   │ approved   │
│ DeliveryWithin                                   │ B13   │ P2, P24   │ approved   │
│ ReadyTrigger                                     │ B13   │ P2, P24   │ approved   │
│ HistorySafeAt                                    │ B13   │ P2, P24   │ approved   │
│ ProcessedByDeadlineOfServiceStatement            │ B13   │ P2, P24   │ approved   │
│ TimelyOfRelayStatement                           │ B13   │ P3, P24   │ approved   │
│ TimelyOfRelayStatement_def                       │ B13   │ P3, P24   │ approved   │
│ AcceptedByDeadlineStatement                      │ B13   │ P2, P24   │ approved   │
│ AcceptedByDeadlineStatement_def                  │ B13   │ P2, P24   │ approved   │
│ DeliveryWithin                                   │ B14   │ P2, P24   │ approved   │
│ ReadyTrigger                                     │ B14   │ P2, P24   │ approved   │
│ HistorySafeAt                                    │ B14   │ P2, P24   │ approved   │
│ ProcessedByDeadlineOfServiceStatement            │ B14   │ P2, P24   │ approved   │
│ TimelyOfRelayStatement                           │ B14   │ P3, P24   │ approved   │
│ TimelyOfRelayStatement_def                       │ B14   │ P3, P24   │ approved   │
│ AcceptedByDeadlineStatement                      │ B14   │ P2, P24   │ approved   │
│ AcceptedByDeadlineStatement_def                  │ B14   │ P2, P24   │ approved   │
│ stateBefore_now_source                           │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_le_event                         │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_mono                             │ B15   │ P3, P24   │ approved   │
│ delivery_now_ge_public                           │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_source_atRestart                 │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_le_event_atRestart               │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_mono_atRestart                   │ B15   │ P3, P24   │ approved   │
│ delivery_now_ge_public_atRestart                 │ B15   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_atRestart               │ B15   │ P3, P24   │ approved   │
│ stateBefore_invariant_atRestart                  │ B15   │ P3, P24   │ approved   │
│ stateBefore_invariant                            │ B15   │ P3, P24   │ approved   │
│ stateBefore_stable_clock                         │ B15   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_restore                 │ B15   │ P3, P24   │ approved   │
│ clock_field_origin                               │ B15   │ P3, P24   │ approved   │
│ clock_field_origin_of_subset                     │ B15   │ P3, P24   │ approved   │
│ stateBefore_field_prefix_restore                 │ B15   │ P3, P24   │ approved   │
│ stateBefore_tick_eq_stateBeforeTime              │ B16   │ P1, P3    │ approved   │
│ index_lt_actionCut_iff                           │ B16   │ P1, P3    │ approved   │
│ stateBefore_tick_eq_stateAfterRestartsAt         │ B16   │ P1, P3    │ approved   │
│ ownRecord_fold_interval_restart                  │ B17   │ P3, P24   │ approved   │
│ ownRecord_fold_restore                           │ B17   │ P3, P24   │ approved   │
│ restart_index_lt_event                           │ B18   │ P1, P3    │ approved   │
│ wake_restart_before_event                        │ B18   │ P1, P3    │ approved   │
│ state_after_restart                              │ B18   │ P1, P3    │ approved   │
│ asleep_state_frozen                              │ B18   │ P1, P3    │ approved   │
│ noRestartOn_of_awakeOn                           │ B18   │ P1, P3    │ approved   │
│ noRestartAfter_of_awakeOnClosed                  │ B18   │ P1, P3    │ approved   │
│ wake_between                                     │ B18   │ P1, P3    │ approved   │
│ stateBefore_stable_restore                       │ B19   │ P3, P24   │ approved   │
│ ownRecord_fold_interval_restart                  │ B20   │ P3, P24   │ approved   │
│ ownRecord_fold_restore                           │ B20   │ P3, P24   │ approved   │
│ stateBefore_now_source                           │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_le_event                         │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_mono                             │ B21   │ P3, P24   │ approved   │
│ delivery_now_ge_public                           │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_source_atRestart                 │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_le_event_atRestart               │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_mono_atRestart                   │ B21   │ P3, P24   │ approved   │
│ delivery_now_ge_public_atRestart                 │ B21   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_atRestart               │ B21   │ P3, P24   │ approved   │
│ stateBefore_invariant_atRestart                  │ B21   │ P3, P24   │ approved   │
│ stateBefore_invariant                            │ B21   │ P3, P24   │ approved   │
│ stateBefore_stable_clock                         │ B21   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_restore                 │ B21   │ P3, P24   │ approved   │
│ clock_field_origin                               │ B21   │ P3, P24   │ approved   │
│ clock_field_origin_of_subset                     │ B21   │ P3, P24   │ approved   │
│ stateBefore_field_prefix_restore                 │ B21   │ P3, P24   │ approved   │
│ stateBefore_tick_eq_stateBeforeTime              │ B22   │ P1, P3    │ approved   │
│ index_lt_actionCut_iff                           │ B22   │ P1, P3    │ approved   │
│ stateBefore_tick_eq_stateAfterRestartsAt         │ B22   │ P1, P3    │ approved   │
│ restart_index_lt_event                           │ B23   │ P1, P3    │ approved   │
│ wake_restart_before_event                        │ B23   │ P1, P3    │ approved   │
│ state_after_restart                              │ B23   │ P1, P3    │ approved   │
│ asleep_state_frozen                              │ B23   │ P1, P3    │ approved   │
│ noRestartOn_of_awakeOn                           │ B23   │ P1, P3    │ approved   │
│ noRestartAfter_of_awakeOnClosed                  │ B23   │ P1, P3    │ approved   │
│ wake_between                                     │ B23   │ P1, P3    │ approved   │
│ stateBefore_stable_restore                       │ B24   │ P3, P24   │ approved   │
└──────────────────────────────────────────────────┴───────┴───────────┴────────────┘
```

`PCCompanion.lean` keeps NoRestart and its field text. Its execution, healthy,
and partialSynchrony dependencies have the new engine meaning. P-Da must include
this dependency change in the SLEEP-1 manifest. The 24 delivery producers keep
their outer signatures and now carry DeliveryDemand. No producer proves receipt.

Writer checks: both libraries and all tests pass `lake build --wfail`.
DCK PASS (package W1b), with all controls enabled. Strict audits pass for all
114 KitV2 and 852 Generic commands. Scoped Generic coverage passes, with zero
unaccepted equation exports. External review and integration are lead-owned.


### W1b fix — P2 pending objects and P3 companion laws (2026-10-10)

P2 text is unchanged. The lead ruling of 2026-10-10 selects a volatile pending
set: a node keeps an object refused for missing dependencies and retries it when
it processes a new object. A restart clears the pending set. Pending traffic after
a wake is covered by delivery counted from max(send, wake). Lean represents a
retry as another handler delivery; the per-anchor DeliveryDemand is this rule's
formal form. FG-SA pin v7 will state the pending set after the sleep migration.

The AcceptanceLaw-derived form is stated once in
`Gen.V2.Duty.AcceptanceLaw.processed_of_not_excluded`: a handled, well-formed
object with dependencies present, an invariant state, and timeliness is processed
if the resulting state does not exclude it. ExecutionValid alone does not supply
Inv or Timely, or the target checks for an object handled through another object.
Protocol owners must supply these inputs at each relevant handler. The companion
`processed_or_retried_of_service` states the current-state-or-retry form using
HistorySafeAt. Without safe history, old processing can meet demand even after
restore erased it. No re-delivery of such an erased receipt follows.

Owners: FG-SA W3/P-ShA prove the relevant acceptance, dependency, invariant,
timeliness, and history obligations. GridCO's protocol owner owns its instance;
GridCO is STABLE in r9 and has no W1b code change. Missing-parent refusal without
exclusion requires a pending retry once dependencies become present. The law does
not assert unconditional acceptance for such a refusal.

P3: both receipt twins add `timely_of_relay_public_actTime`, with public action
times and RestoreTimeLaw and no wake premise. Approved TimelyOfRelay text stays.
W2b/W3 must not use hwake for FG-SA. They must repair timely_of_relay_retained under
RestoreTimeLaw and prove public admission times (multiples of 4Δ, with the required
parameter alignment). Both KitV2 twins add `stateBefore_stable_clock_restartFree`:
Q need not survive restore when its index interval has no restart.

Owner notes from Opus 6–7: P-ShA must use fresh post-join vote anchors or prove
that each relevant receipt survives to the action cut. HEAD votes erased by sleep
cannot supply HistorySafeAt. W3 owns the Receipts clock call repair; W2b supplies
the clock foundation. P-H owns DescentTiming's call. Each must supply awake or use
delivery_now_ge_public_atRestart with full ExecutionValid.

The W1b package map now assigns the ready ReceiptCoverage core, Receipts,
SelfDelivery, AC, AncestorDeadlines, AncestorDeadlinesStore, Protocol, Schedule,
Statements.Receipts, and the final FGSARun audit repair to W3. The public
Statements.ReceiptCoverage text belongs to S-Ap. Map comments record shared work
with W2b; no downstream module is changed here.

Fix validation: the 290-module GREEN build passes --wfail (61.40 s). Scoped
Generic coverage passes (4.75 s). DCK W1b passes with all 24 controls (394.69 s).
Strict audits pass: Generic root 856, KitV2 root 116, DeliveryBy tests 53, and
KitV2 sleep tests 3. All results use only the three permitted axioms.

## W2b continuation — lead rulings applied, 2026-10-10

The earlier stopped rows are history. The 01:22 W2b ruling releases all five stops.
The 01:08 W1b ruling supplies pending-set service and public admission-time timeliness.
All three reset modules are now GREEN. W3 and the family owners keep their integration work.

- `stored_proposal_delivered` — internal statement, lead ruling 10-10.
  Delivery is at an earlier index in any epoch. The exact wire stays in durable storage at each
  index from j+1 through i. All consumers retain the delivery, wire and payload facts. The
  Schedule consumer now carries the storage interval instead of restartFree; every other existing
  consumer discards that final field.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Finality/Receipt.lean:50`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Accountable.lean:531`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Carrier.lean:39`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Sources.lean:252`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:105`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:218`;
  `AvailableChainFGSARun/Proofs/NamedDelivery.lean:50`;
  `AvailableChainFGSARun/Proofs/NamedDelivery.lean:63`;
  `AvailableChainFGSARun/Proofs/Roots.lean:107`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:1008`;
- `act_prop` — internal statement, lead ruling 10-10.
  The equation has exactly the joinedNow guard from approved actS. Its direct proof consumer is
  act_prop_zero. NamedOrigins uses the same guard when it reads successful HEAD and proposal
  emissions.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSARun/Proofs/Protocol.lean:154`;
- `act_prop_zero` — internal statement, lead ruling 10-10.
  The conclusion is kept: slot zero gives none in both joined branches. The proof uses act_prop
  and the slot-zero proposal rule.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_hrestore_retained` — internal statement, lead ruling 10-10.
  A predicate must be preserved by acRestart of its retained input. A pre-state proof then gives
  the post-restore proof at the supplied wake. There is no runtime consumer beyond the audits.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_hrestore_field_retained` — internal statement, lead ruling 10-10.
  Restore introduces no member into a list field that acRestart keeps or clears. Schedule supplies
  acRestart_genuine and nil_subset. Family obligations use acRestart_obligations; saved-pair
  fields use acRestart_genuine; fast-pair fields use acRestart_fastWrite. Each gives the exact
  subset law needed by the clock-field origin consumer.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuation.lean:237`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:323`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:494`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:199`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:379`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:222`;
- `fgsa_preTick_now_lt` — internal statement, lead ruling 10-10.
  The strict bound uses the exact epoch condition: every earlier local restart is strictly before
  this tick. fgsa_preTick_now_lt_iff proves necessity and sufficiency. fgsa_preTick_now_lt_joined
  supplies the strict bound directly for joined reads. fgsa_preTick_now_le covers a wake at the
  tick. The strict conclusions needed by consumers are kept. Family owners must use the joined
  bridge or prove the epoch condition; the .le use in Healing/PostResetRaw:901 can use the
  unconditional companion.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:511`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossNext.lean:289`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossUnanimous.lean:158`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportHeads.lean:153`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportProposal.lean:98`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceGate.lean:152`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:125`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:286`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:901`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:1383`;
  `AvailableChainFGSAProofs/Proofs/Healing/RepairGate.lean:504`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportHeads.lean:216`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportOutput.lean:198`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportProposal.lean:149`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportRelay.lean:92`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:283`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:131`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:144`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:576`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:26`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedReflect.lean:328`;
  `AvailableChainFGSAProofs/Proofs/Shared/SameLabel.lean:206`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:206`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:297`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:493`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:242`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1425`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:544`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:568`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:610`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:778`;
- `fgsa_release_votes_stamped` — internal statement, lead ruling 10-10.
  All vote stamps, including the default stamp, are strictly before release under the exact pre-
  tick epoch condition. The active-view projection equalities are kept. A same-time wake permits
  equality, covered by fgsa_preTick_votes_stamped_le. There is no runtime caller of this export
  beyond the audits.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_stateBefore_bounds` — internal statement, lead ruling 10-10.
  The statement is kept. Its reset case starts from the prior reachable store, applies
  Reachable.restart to wipe, and proves replay reachability and bounds. The wake clock is at least
  the old clock by RestoreTimeLaw and event order. Kept blocks remain within the wake slot;
  accepted replay stamps are within the wake clock. All block-slot and stamp projections used by
  consumers are kept.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:647`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossNext.lean:285`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossUnanimous.lean:154`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrameZero.lean:106`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportHeads.lean:149`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportProposal.lean:94`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceGate.lean:146`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:121`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:282`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:1379`;
  `AvailableChainFGSAProofs/Proofs/Healing/RepairGate.lean:498`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportHeads.lean:212`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportProposal.lean:145`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportRelay.lean:93`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:556`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:724`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:363`;
  `AvailableChainFGSAProofs/Proofs/Shared/HeadAdmit.lean:214`;
  `AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthCausal.lean:47`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:145`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:577`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:35`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedReflect.lean:337`;
  `AvailableChainFGSAProofs/Proofs/Shared/SameLabel.lean:207`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:379`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1564`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:586`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:613`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:783`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:843`;
- `fgsa_stored_block_origin` — internal statement, lead ruling 10-10.
  The origin is in any earlier epoch, with the exact wire retained from j+1 through i. The stored-
  wire, block and delivery projections are kept. Every existing external consumer discards the
  former restartFree field.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Finality/MiddleSupport.lean:757`;
  `AvailableChainFGSAProofs/Proofs/Healing/Promotion.lean:35`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:47`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:897`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:1127`;
- `fgsa_tick_total` — internal statement, lead ruling 10-10.
  Tick existence is conditional on the honest node being awake at the public time, exactly as P1
  and ScheduleWellFormed.tick_total require. The unique-index conclusion is kept; family owners
  supply awake from their approved participation premise.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuation.lean:538`;
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowth.lean:377`;
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowth.lean:572`;
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowthSeed.lean:195`;
  `AvailableChainFGSAProofs/Proofs/Clean/Closure.lean:200`;
  `AvailableChainFGSAProofs/Proofs/Clean/Closure.lean:298`;
  `AvailableChainFGSAProofs/Proofs/Clean/Safety.lean:197`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:212`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:257`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:447`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:566`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:569`;
  `AvailableChainFGSAProofs/Proofs/Finality/RowsPrem.lean:91`;
  `AvailableChainFGSAProofs/Proofs/Finality/TailFrame.lean:383`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSearchTasks.lean:211`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceBody.lean:197`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceOne.lean:29`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetGate.lean:265`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:163`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:592`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:811`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:235`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportHeads.lean:110`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportOutput.lean:261`;
  `AvailableChainFGSAProofs/Proofs/Outage/ArmingBatch.lean:63`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:462`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:465`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:626`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:629`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:820`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:299`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:513`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:519`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:581`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:726`;
  `AvailableChainFGSAProofs/Proofs/Outage/InclusionGate.lean:55`;
  `AvailableChainFGSAProofs/Proofs/Outage/InclusionGate.lean:119`;
  `AvailableChainFGSAProofs/Proofs/Outage/InclusionGateBody.lean:55`;
  `AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:193`;
  `AvailableChainFGSAProofs/Proofs/Shared/ExactService.lean:462`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:269`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:272`;
  `AvailableChainFGSAProofs/Proofs/Shared/HeadAdmit.lean:387`;
  `AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthProposal.lean:32`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:293`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactProposal.lean:214`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:78`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:332`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:203`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:750`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:305`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:308`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepInputs.lean:155`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepService.lean:201`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:44`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:811`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1015`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1488`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1491`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:3074`;
- `fgsa_gate_clock_bridge` — internal statement, lead ruling 10-10.
  The anchored SA clock equation holds on the joined branch. The existing block, headDomain and
  fastWrite expressions are kept. Family consumers of fastWrite must supply joinedness.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Healing/SupportWrite.lean:75`;
  `AvailableChainFGSAProofs/Proofs/Shared/ExactService.lean:218`;
  `AvailableChainFGSAProofs/Proofs/Shared/OpeningSource.lean:49`;
- `fgsa_release_clockPre` — internal statement, lead ruling 10-10.
  The release equation is conditional on the approved joined release guard. The active input and
  release body are unchanged. Healing/SupportTransfer must supply that join test.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossUnanimous.lean:291`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:72`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:306`;
- `fgsa_release_input_votes_stamped` — internal statement, lead ruling 10-10.
  The input view keeps the same votes and stamps. The exact epoch condition gives each accepted
  input vote its required strict release stamp. Its sole proof consumer, release_count_bridge,
  passes that condition.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSARun/Proofs/Schedule.lean:888`;
- `fgsa_release_count_bridge` — internal statement, lead ruling 10-10.
  The raw-pool and cutoff-pool equality and all count expressions are kept under the exact epoch
  condition. There is no runtime consumer beyond the audits.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_gate_saved_result` — internal statement, lead ruling 10-10.
  The genuine confirmation equation applies on the joined branch. fgsa_gate_saved_unjoined
  supplies the exact other branch: some none. Both use the fresh-gate proof and retain the same
  pre-gate active view. Family owners supply the approved gate join condition.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Clean/StateGate.lean:32`;
  `AvailableChainFGSAProofs/Proofs/Shared/Reads.lean:161`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateHistory.lean:139`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepOutput.lean:29`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepService.lean:30`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:91`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransferReceipts.lean:415`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:639`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1877`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:2153`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:2965`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:3121`;
- `timely_of_relay_retained` — internal statement, lead ruling 10-10.
  Relay timeliness now uses RestoreTimeLaw and public actTime through the additive W1b companion.
  No public-wake premise is used. fgsa_admissionTime_public proves every FG-SA admission threshold
  is a public multiple of 4Δ when E.Δ=p.Δ. Receipts:883,985 are W3 call repairs: supply that law
  and fgsaRestoreTimeLaw with the TimelyClock projection.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSARun/Proofs/Receipts.lean:883`;
  `AvailableChainFGSARun/Proofs/Receipts.lean:985`;

The public companions are in Schedule and RetainedClock. SleepContinuationAxioms has one
#print axioms for each new or replaced public proof (25 total). SleepContinuation has seven
valid-run regressions, each with its own #print axioms. No heartbeat option is changed.

NamedOrigins now contains its reset and successful-emission proofs. The two unchanged
trigger-scope helpers move to NamedDelivery, already EXPECTED-FAIL under W3. Their old
handler-only proof does not consume P2's ProcessedByActionCut-or-HandledBetween service.
W3 must repair both those consumers and their exact body-scope preconditions. Their types
are kept; no call or source obligation is removed. The REQUIRED scope is kept.

The obsolete local retained-clock source, bound and invariant helpers are removed from
RetainedClock. W3/Receipts and P-ShA/OutputGrowthCausal must use the shared exact-wake
stateBefore_now_source_atRestart, stateBefore_now_le_event_atRestart and step induction.
The run expected list includes every new public companion and test. The W2b map includes
the five added W1b sleep modules, both new tests, and all three reset sites as GREEN.

- New companions — P1, P3, P24, approved; exact forms of the 10-10 rulings.
  `fgsa_preTick_now_le`, `fgsa_preTick_restartTime_at_wake`,
  `fgsa_preTick_now_lt_joined`, `fgsa_preTick_now_lt_iff`,
  `fgsa_preTick_votes_stamped_le`, `fgsa_gate_saved_unjoined`,
  `fgsa_admissionTime_public`.
  Consumers: SleepContinuation; strict audits; the W3 and family calls listed above.
- `SleepContinuationTests.retained_origin`, `joined_strict`, `same_time_bound`,
  `retained_block_bound`, `wake_epoch_equiv`, `gate_empty`, `admission_public` —
  P1, P3, P24, approved. Consumers: strict audit and W2b GREEN/DCK acceptance.

## W3 — Compose restart laws (2026-10-10)

- P3/P24 approved field types: FGSafetyStoreLaws.restart_good takes the wake time.
  restart_tf now maps membership to the pre-restart TF. SafetyStore induction keeps
  the prior delivery origin. Consumers: safety_good_stateBefore and safety_stateBefore_origin.
- P3/P24 approved field type: FGSafetyClientLaws.restart_record takes the wake time.
  Consumer: safety_client_trace. The lossy and kept record controls take that time.
- P24 approved new record: FGSafetyRestartLaws and its restart_F field. It adds no
  field to FGSafetyStoreLaws. The inventory and SafetyAxioms audit include both names.
- N2 additive theorem: safety_F_mono_all uses restart_F and permits restarts.
  The old NoRestart theorem stays. The new theorem has a SafetyAxioms audit entry.
- Compose and Claims read fixtures now use the time-indexed restore arity.

## W3 — Internal statement repairs in progress (2026-10-10)

- internal statement, W3: ancestorDeadlines_restore used the old Time × RecordOnce
  durable type and concluded that obligations were empty. It now uses State ×
  RecordOnce, the wake time, and AncestorDeadlines of the pre-restart store.
  acRestart_obligations supplies the exact preserved result. Consumers:
  FGSAProofs/Proofs/Foundations/Leases.lean and FGSARun/Tests/Axioms.lean.
- internal statement, W3: fgsa_emits_head and fgsa_emits_proposal omitted the join
  guard of actS. The exact emission equations now include joinedNow of the clocked
  store. Run consumers: EmissionWellFormed, Receipts, and Roots. Family consumers:
  Shared/ExactService, HeadAdmit, OutputGrowthProposal, RetainedPersist,
  RetainedConsumers, Count, ScoreRun; Clean/StepGate; Finality/CoreServices;
  Outage/ExactProposal, ArmingDuty, PersistenceRelease, ContinuationReceipt;
  WeakContinuation/Proposal, StepGateBatch; WeakContinuationGrowth/Dynamics.
  Family owners must supply the joined premise only when they construct emissions.
- internal statement, W3: spec_restart_durable_retained and
  spec_restart_clock_retained asserted the old last-tick restore clock. They now
  use the complete durable store and the exact wake time. Consumers: run axiom audit.
- internal statement, W3: spec_prune_execution_valid and
  spec_revised_target_execution omitted SleepWellFormed. They now require that
  condition and preserve it through delivery pruning. Consumers: the latter uses
  the former; the run axiom audit uses both. No external proof consumer was found.
- internal statement, W3: spec_restart_retained_block_trace used now = 8 after
  the restart at 9. Its exact clock equation is now = 9. Consumer:
  Spec/Transfer.spec_restart_matched_cut_agreement discards that clock field.
