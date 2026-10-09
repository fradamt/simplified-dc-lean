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
