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
  and ScheduleWellFormed.tick_total require. The unique-index conclusion is kept. The review
  handoff below identifies each exact awake source and each missing consumer premise.
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
  release body are unchanged. SupportTransfer.release_rows has no source for that join test;
  its arbitrary-store type needs the conditional repair in the review handoff below.
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

## W3 — Sources, join bridges and provenance (2026-10-10)

- N11: fgsa_fgAction_unjoined_source_none uses saved-label provenance, tick
  uniqueness, and CStoreInv.fastDom. These give label freshness without a separate
  latest-wake search. A fresh unjoined gate writes an empty fast set for rR.
- N7: fgsa_joinedNow_of_joinedEnv uses the explicit restart clause in the approved
  joinedAt text. fgsa_joinedNow_of_caughtUp uses its marker and gate-time clauses.
  S-Ap can apply these without importing the future Claims/Statements/Join module
  into Run. The awake-closed companion also requires RestartsAtWakes.
- internal statement, W3: rowPool_provenance formerly concluded restartFree after
  its handler. That is false when a durable row crosses a restart. The exact new
  form keeps the handler origin and states row membership at every later index
  through the read. Consumers: SelfDelivery.fgsa_emitted_row_fresh;
  Foundations/Accountable; NonVacuity/HealingPackages. All discard the last field.
  The proof and its store helpers move to Run/Proofs/RowHistory.lean.
- N10 row core: fgsa_emitted_row_no_prior_processed covers every receiver and every
  index at or before the emitting tick. Retained row origin, unforgeable signatures,
  and durable send-once exclude an earlier occurrence.
- STOP N10 proposal form under ExecutionValid alone: a constant digest is permitted
  by Params. A valid run holds a slot-1 proposal of root 2 before the honest slot-2
  proposal of root 2 is emitted. processedS tests only that root and returns true.
  Evidence: Tests/EmissionFreshness.emitted_proposal_already_processed and its
  full ExecutionValid proof. A true freshness form needs an additional root/scope
  condition. Do not change an approved public statement to add it without a ruling.

## W3 — Approved-core STOP and exact AC forms (2026-10-10)

- STOP P23 fgsa_receiptCoverage_ready: receiver readiness does not fix the root-only
  processing exemption. Tests/ReceiptAlias proves DeliveryWithinOn, every unchanged
  ReceiptCoveragePremises field, full receiver readiness, ExecutionValid,
  NamedRootCollisionFree, and NoRestart on a concrete trace. The new required body
  is not stored at its deadline. The legacy coverage conclusion is false on that
  same ready trace. The proposed ready core has exactly that conclusion, so it is
  false too. This needs a lead decision about the approved public boundary. No
  premise, conclusion, quantifier, public protocol function, or statement was changed.
- The N10 proposal counterexample also satisfies NamedRootCollisionFree. Its scope
  contains genesis and the delivered slot-1 body; it does not contain the emitted
  slot-2 body. Changing named scope to include that emission changes public meaning.
- The handler-only NamedDelivery trigger helpers depend on the same missing exact
  body scope. Their old statement cannot be repaired from current P2 history alone.
  Keep them as a visible stopped item. Unrelated, true named-origin proofs move
  unchanged to Run/Proofs/NamedHistory. Roots and the safety adapter use that module.
- internal statement, W3: fgsaAC_gate_write now takes joinedNow on clockPre. The old
  unguarded gate equation is false for unjoined gates. Other-label preservation
  uses gateStep_other. Consumers: AC slot reads; Shared/Gate; Clean/StateGate,
  GateOutput; Healing/PostResetHealed, RepairGate, SupportOutput;
  Outage/InclusionGateBounds; WeakContinuation/Inclusion, StepOutput, StepService;
  WeakContinuationGrowth/Dynamics. Family owners use N7 at the read that they need.
- internal statement, W3: fgsaAC_laws and fgsaAC_slot_gate_reads now take the join
  clause at every gate in their returned aggregate. This is required by the
  unchanged Generic ACLaws record. No proof consumer outside AC was found; the
  audit commands keep their names. The old unconditional aggregate is false.
- fgsaAC_output_step keeps its statement. Restart uses the preserved-output branch.
- Shared/FGCompose now imports the needed Claims definitions directly and proves
  its source selector equation locally. It does not import the later Shared
  channel producers. Shared safety laws and their early audit now compile.

## W3 — Final internal receipt and append forms (2026-10-10)

- internal statement, W3: fgsa_vote_stamp_source and fgsa_block_stamp_source formerly
  asserted only a network origin through restart. Their network-only forms now
  take NoRestart. The exact general suppliers are fgsa_vote_stamp_source_or_restart
  and fgsa_block_stamp_source_or_restart. They add local replay or restamp origins
  with the actual wake time. They assert no network acceptance at restart.
  Consumers: Receipts vote/read/cap/acceptance suppliers; Shared/ReceiptFacts,
  GateReceipt, ScoreRun; WeakContinuation/ExactProposal and its family copies.
  Restart consumers use the general supplier. NoRestart consumers use the wrapper.
- R8: fgsa_block_accepted_origin keeps the original network acceptance through every
  restart epoch. fgsa_replayed_head_delivery_origin supplies the original delivered
  proposal and structural HEAD carriage, with no fabricated HEAD handler.
- internal statement, W3: fgsa_vote_accepted_before and fgsa_block_accepted_before
  now take ExecutionValid, rather than ScheduleWellFormed alone. An asleep raw
  receiver may have a stale clock under ScheduleWellFormed. Full sleep validity
  and RestoreTimeLaw give the exact public-time bound at a real delivery. The vote
  form keeps its NoRestart premise; the block form still permits restarts.
  Consumers: Shared/ReceiptFacts, GateReceipt, ScoreRun and family deadline readers.
- internal statement, W3: fgsa_head_cap_sources takes NoRestart for its network-only
  cap witnesses. Its only proof consumer in Run is fgsa_honest_head_receipt, which
  already has that premise. General stamp/replay suppliers cover restart consumers.
- internal statement, W3: fgsa_head_receipt and fgsa_honest_head_receipt take the
  receiver's AwakeOn window and dl t ≤ horizon. The old within premise is vacuous
  outside those guards. Their HEAD/stamp conclusions stay. Consumers: public
  ReceiptCoverage wrapper (stopped P23), Shared and family HEAD receipt readers.
- internal statement, W3: fgsa_proposal_receipt takes the same awake/horizon guards
  and NamedProposalInRun of the exact required body. Root-only history does not
  supply that body scope. The stored-body conclusion stays. Consumers: P23 core
  (STOP), Shared proposal receipt readers and their Clean/Outage/WC/WCG copies.
- internal statement, W3: proposal_trigger_in_scope and its root-scope projection
  now use DeliveryService plus an exact historical-scope callback. A handled
  service keeps the original handler origin; past root processing alone cannot
  scope the new body. Consumers: WeakContinuation/ExactProposal and
  Assembly/WeakContinuationGrowth must discharge that callback after the P23 ruling.
- internal statement, W3: fgsa_accepted_by_deadline_of_parentStored now follows the
  current generic core: ReadyTrigger, HistorySafeAt, actual horizon, action-cut
  restartFree, HooksSound and a handler Timely callback. Its parent and wire facts
  still supply dependencies. No proof consumer outside the Run audit was found.
- N3: fgsa_processed_by_deadline_ready instantiates the P2 service/acceptance core.
  History is current processing on NoRestart; full validity and the awake window
  supply earlier public ticks. Relay time uses RestoreTimeLaw and public actTime;
  no TimelyOfRelay hwake premise is used. fgsaTimelyClock_clock exposes the needed
  equality to the physical FG-SA clock without changing the clock definition.
- N10 HEAD: fgsa_emitted_head_no_prior_processed holds through sleep and replay.
  A replayed HEAD comes from an earlier carried signature, and its fixed-label
  action time excludes processing before the current scheduled emission.
- internal statement, W3: the requested proposal no-prior-processing form needs
  NamedProposalInRun for the emitted body as well as NamedRootCollisionFree and
  ExecutionValid. fgsa_emitted_proposal_no_prior_processed proves that exact scoped
  form. Consumers that need scope from P2 alone remain STOP under the proved alias.
- Own-row append/cut producers keep both P2 service branches and all demand guards.
  The cut carries full SleepWellFormed. internal statement, W3:
  healthyPrefixDeliveryBy_cut also takes t ≤ rho.horizon; extending the cut horizon
  would otherwise create obligations beyond the old demand domain. Consumers:
  Shared/Regimes at the valid action-time cut. No declaration in that family changed.
- Validation status: 399 GREEN modules compile with --wfail. The fixed package
  domain retains 60 EXPECTED-FAIL entries, including three S-Ap-P23-STOP roots:
  Run, Proofs/ReceiptCoverage and Tests/Axioms. No REQUIRED module is deferred.
  This is not W3 close or a full-run PASS. The lead owns the public P23 ruling.

## W3 — Audit and handoff limits (2026-10-10)

- W3 equation exports were repaired in FGSource and ProposalHistory. Schedule's
  process-bound caller uses a direct slot projection instead of exporting the
  model State.slot equation. No theorem type changed for that caller.
- STOP inherited W2b equation exports: Restore.lean is unchanged in W3, but the
  complete W3 and Shared export checks report 17 unaccepted matcher equations
  from that module (admitBlock, admitRow, process, headLabel?, resolvedBefore).
  The baseline is unchanged. W2b/lead must provide the review fix. This is a checker
  failure, not a project axiom or a failed kernel theorem.
- Run inventory rows use actual compiled owners from W3Axioms generation. Only
  the Run, SharedAxioms, SafetyAxioms and FGSafety sections changed. The late
  FGSafety source audit repeats the two new safety producers, as its coverage
  checker requires. That audit remains a P-Sa family target, not an S1 promotion.
- The Claims read test is an explicit package target outside S1, as r8 permits.
  New Run modules are S1 REQUIRED. No original REQUIRED or DEFERRED entry changed.
- DCK uses all normal controls. No baseline exception or audit exception is used.
  Full Run build remains stopped by the P23 wrapper; the exact ready core cannot
  be written under the approved statement. Root freeze and package close remain
  with the lead after both STOP items are resolved.

## W3 — Writer validation result (2026-10-10)

- Commit 0b6f3837 contains the completed W3 implementation, tests and explicit STOP map.
- Final DCK W3 PASS: 147.01 s, 399 GREEN modules, 30 strict audit roots,
  2,473 axiom commands/results, and all 24 normal controls. No audit exception.
- The map has 61 EXPECTED-FAIL entries. Three are the S-Ap P23 stopped roots;
  the late FGSafety audit remains P-Sa. The other entries retain their family owners.
- Final export check: 17 unaccepted exports, all in unchanged W2b Restore.lean.
  New W3 modules and the repaired Schedule caller have no unaccepted export.
- The P23 ready core is still STOP. No approved public text or stopped wrapper changed.
  DCK PASS certifies the explicit GREEN partition. It does not close W3 or G-S1.
- Full report: local, excluded claude-files/sleep-w3-report.md. Evidence: .lake/sleep-w3/.
## W2b review fixes — consumer handoff

### W3/P-ShA handoff: review use classifications

This replaces the earlier claim that every consumer needs only an argument repair.
Keep all W2b conditions. This is a source handoff; EXPECTED-FAIL consumers are not verified.
References use review base `4b697a95`. Run paths start at `AvailableChainFGSARun/`;
other paths start at `AvailableChainFGSAProofs/`. Each row is one direct proof/test use.
Audit references are proof-only repairs of the print command; they add no premise.
The four NamedOrigins guard splits at :77, :86, :146 and :160 are proof-only repairs.
They unfold the approved actS guard (P24, packet :8204), without changing an emission type.
These audit/guard references are separate from the 170 direct-use counts below.

P = proof-only repair. A = approved change of read/scope. F = false internal consumer type.
M = premise source missing; this is an extra flag, not a fourth classification.
The Owner column applies plan §14.6, with the family split in §8.1/§8.3.
For M rows the owner must trace the new condition through callers to the public boundary.
An added internal premise is a repair specification, not approval to add a public premise.
M records a missing receiver/time or branch source. It remains open with that owner.
No blanket participation inference applies.

Condition/source keys:

- K: keep the used origin/bound projections. No new condition is needed.
- Z: split joinedNow in act_prop_zero. Both branches give none; no new condition is needed.
- S: supply the restart subset law. Leases:323 uses acRestart_obligations equality;
  Leases:494 uses acRestart_fastWrite = []; the other saved-pair uses acRestart_genuine = [].
  Schedule:222 already supplies acRestart_genuine and nil_subset.
- L: use fgsa_preTick_now_le. Preserve the consumer conclusion: now ≤ tick, then slot
  monotonicity, or now ≤ tick < the live deadline. No awake/join condition is needed.
- E: keep strict now < tick with hEpoch = ∀ j w, j < i →
  rho.events[j]? = some (.restart v w) → w < t. Current NoRestart contradicts the event.
  For a sleep interface, derive hEpoch from joinedAtTime at this same tick; no inference
  from awake alone is valid. That sleep change must obtain its scope from the family packet.
- I: the Run caller already passes hEpoch, derives it from joinedAtTime, or proves the iff.
- J: the strict late-pool helper keeps its existing conclusion with hEpoch at its gate tick
  as an added premise (or joinedAtTime p pre.restartTime gateTime = true).
  No source exists inside its schedule-only type. Its callers have hN : NoRestart rho;
  pass hEpoch by contradicting each restart event. No new public premise is needed there.
- G: use the executed gate read from P11/D015, approved packet :4265–4274.
  Exact equation: savedGenuine post.base s = some (if joinedAtTime p pre.restartTime
  (SA.gateTime p.toParams s) then rawConfirmation else none). The same guard controls fastSet.
  Split the guard and use fgsa_gate_saved_result / fgsa_gate_saved_unjoined.
  A nonempty executed gateResult, gateResultAt, or GateService result implies this guard.
  A raw confirmation or a gate event alone does not. P11/D016 :4293 uses enabledGateAt;
  its exact definition at :4594–4598 supplies the marker bound w ≤ slotStartZ p s.
- GF: healing_support_fastWrite must require joinedAtTime at its gate and then keep
  its raw fastSet equality; alternatively give fastWriteAt post s = some
  (if joinedAtTime p pre.restartTime gateTime then fastSet p anchor view s else []).
  Its current schedule + gate type has no source for the joined branch. Its callers
  with a nonempty executed result/fast-write use G; the guarded equation needs no new premise.
- GR: clean_gate_raw must require the same gate guard for its raw equation, or state
  the guarded G equation. Its current schedule + gate type has no joined source:
  premise source missing. The approved guarded read does not prove an unconditional raw equality.
- RR: healing_support_release_rows must require joinedAtTime p st.restartTime
  (SA.releaseTime p.toParams s) = true. Then keep row ∈ (actView st1).obligations and
  releaseCount ... s row.1 < row.2.1. Without the guard the exact conclusion is conditional:
  row survives expiry and (joinedAtTime ... = true → releaseCount ... < row.2.1).
  An arbitrary store plus a surviving lease supplies no guard. Its three current callers
  can pass the guard from hrec.base.noRestart or hN (see caller checks below).
  Under sleep, use the conditional form for callers that need only expiry membership;
  a caller that needs the strict count must prove the release guard, as specified in RN.
- RN: current NoRestart gives pre.restartTime = none and thus the release guard.
  DescentLossUnanimous:291 uses hrec.base.noRestart; SupportTransfer:306 uses hN.
  The sleep form uses P8 RecoverySleep₂.suffixNoRestart (packet :2935–2941), bounds
  all earlier restarts by GST, and needs GST ≤ slotStartZ p v at releaseTime v.
  P8's τ scope (:2284) supplies that cutoff after recoveryStart; the old bound
  GST ≤ voteTime v alone is not that cutoff. Pass the guard also to release_rows.
- C: Schedule:888 passes its hEpoch without change.
- RT: Receipts uses fgsaRestoreTimeLaw for its aligned TimelyClock and
  fgsa_admissionTime_public with E.Δ = p.Δ. Keep actTime ≤ pubFloor(receiptTime).
  No public-wake premise is used. This is W3 integration with unchanged consumer conclusions.

`stored_proposal_delivered`:

```text
┌────────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                    │ Type │ Source │ Owner │ Open │
├────────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Finality/Receipt.lean:50                   │ P    │ K      │ P-Fi  │ —    │
│ Foundations/Accountable.lean:531           │ P    │ K      │ P-Fd  │ —    │
│ Foundations/Carrier.lean:39                │ P    │ K      │ P-Fd  │ —    │
│ Foundations/Sources.lean:252               │ P    │ K      │ P-Fd  │ —    │
│ Shared/ScoreRun.lean:105                   │ P    │ K      │ P-ShA │ —    │
│ Shared/ScoreRun.lean:218                   │ P    │ K      │ P-ShA │ —    │
│ Tests/NonVacuity/FinalityClaims.lean:1012  │ P    │ K      │ P-As  │ —    │
│ Tests/NonVacuity/HealingClaims.lean:1008   │ P    │ K      │ P-As  │ —    │
│ Tests/NonVacuity/HealingPackages.lean:1003 │ P    │ K      │ P-As  │ —    │
│ Tests/NonVacuity/HealingRun.lean:1007      │ P    │ K      │ P-As  │ —    │
│ Run/Proofs/NamedDelivery.lean:50           │ P    │ K      │ W3    │ —    │
│ Run/Proofs/NamedDelivery.lean:63           │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Roots.lean:107                  │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:1008              │ P    │ K      │ W3    │ —    │
│ Run/Tests/SleepContinuation.lean:18        │ P    │ K      │ W3    │ —    │
└────────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:171; Run/Tests/SleepContinuationAxioms.lean:9.

`act_prop`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Run/Proofs/Protocol.lean:154 │ P    │ Z      │ W3    │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:72; Run/Tests/SleepContinuationAxioms.lean:5.

`act_prop_zero`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:73; Run/Tests/SleepContinuationAxioms.lean:6.

`fgsa_hrestore_retained`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:48; Run/Tests/SleepContinuationAxioms.lean:7.

`fgsa_hrestore_field_retained`:

```text
┌──────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                  │ Type │ Source │ Owner │ Open │
├──────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Assembly/WeakContinuation.lean:237       │ P    │ S      │ P-As  │ —    │
│ Foundations/Leases.lean:323              │ P    │ S      │ P-Fd  │ —    │
│ Foundations/Leases.lean:494              │ P    │ S      │ P-Fd  │ —    │
│ WeakContinuation/StepFacts.lean:199      │ P    │ S      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:379 │ P    │ S      │ P-WC  │ —    │
│ Run/Proofs/Schedule.lean:222             │ P    │ S      │ W3    │ —    │
└──────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:49; Run/Tests/SleepContinuationAxioms.lean:8.

`fgsa_preTick_now_lt`:

```text
┌───────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                   │ Type │ Source │ Owner │ Open │
├───────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Clean/StepGate.lean:511                   │ P    │ E      │ P-Cl1 │ —    │
│ Healing/DescentLossNext.lean:289          │ P    │ L      │ P-H1  │ —    │
│ Healing/DescentLossUnanimous.lean:158     │ P    │ L      │ P-H1  │ —    │
│ Healing/FrontierSupportHeads.lean:153     │ P    │ L      │ P-H1  │ —    │
│ Healing/FrontierSupportProposal.lean:98   │ P    │ L      │ P-H1  │ —    │
│ Healing/OpeningServiceGate.lean:152       │ P    │ L      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:125    │ P    │ L      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:286    │ P    │ L      │ P-H2  │ —    │
│ Healing/PostResetRaw.lean:901             │ P    │ L      │ P-H1  │ —    │
│ Healing/PostResetRaw.lean:1383            │ P    │ L      │ P-H1  │ —    │
│ Healing/RepairGate.lean:504               │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportHeads.lean:216             │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportOutput.lean:198            │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportProposal.lean:149          │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportRelay.lean:92              │ F    │ J      │ P-H1  │ —    │
│ Outage/ContinuationReceipt.lean:283       │ P    │ E      │ P-Ou  │ —    │
│ Shared/GateReceipt.lean:131               │ P    │ E      │ P-ShA │ —    │
│ Shared/Relay.lean:144                     │ F    │ J      │ P-ShA │ —    │
│ Shared/Relay.lean:576                     │ P    │ E      │ P-ShA │ —    │
│ Shared/RetainedEndpoint.lean:26           │ P    │ L      │ P-ShA │ —    │
│ Shared/RetainedReflect.lean:328           │ P    │ L      │ P-ShA │ —    │
│ Shared/SameLabel.lean:206                 │ F    │ J      │ P-ShA │ —    │
│ WeakContinuation/Inclusion.lean:206       │ P    │ L      │ P-WC  │ —    │
│ WeakContinuation/Proposal.lean:297        │ P    │ E      │ P-WC  │ —    │
│ WeakContinuation/Proposal.lean:493        │ P    │ L      │ P-WC  │ —    │
│ WeakContinuation/StepGateBatch.lean:242   │ P    │ E      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1425 │ P    │ E      │ P-WC  │ —    │
│ Run/Proofs/Schedule.lean:544              │ P    │ I      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:568              │ P    │ I      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:610              │ P    │ I      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:778              │ P    │ I      │ W3    │ —    │
└───────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:226; Run/Tests/SleepContinuationAxioms.lean:16.

`fgsa_release_votes_stamped`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:227; Run/Tests/SleepContinuationAxioms.lean:21.

`fgsa_stateBefore_bounds`:

```text
┌───────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                   │ Type │ Source │ Owner │ Open │
├───────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Clean/StepGate.lean:647                   │ P    │ K      │ P-Cl1 │ —    │
│ Healing/DescentLossNext.lean:285          │ P    │ K      │ P-H1  │ —    │
│ Healing/DescentLossUnanimous.lean:154     │ P    │ K      │ P-H1  │ —    │
│ Healing/FrameZero.lean:106                │ P    │ K      │ P-H1  │ —    │
│ Healing/FrontierSupportHeads.lean:149     │ P    │ K      │ P-H1  │ —    │
│ Healing/FrontierSupportProposal.lean:94   │ P    │ K      │ P-H1  │ —    │
│ Healing/OpeningServiceGate.lean:146       │ P    │ K      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:121    │ P    │ K      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:282    │ P    │ K      │ P-H2  │ —    │
│ Healing/PostResetRaw.lean:1379            │ P    │ K      │ P-H1  │ —    │
│ Healing/RepairGate.lean:498               │ P    │ K      │ P-H1  │ —    │
│ Healing/SupportHeads.lean:212             │ P    │ K      │ P-H1  │ —    │
│ Healing/SupportProposal.lean:145          │ P    │ K      │ P-H1  │ —    │
│ Healing/SupportRelay.lean:93              │ P    │ K      │ P-H1  │ —    │
│ Outage/ContinuationReceipt.lean:556       │ P    │ K      │ P-Ou  │ —    │
│ Outage/ContinuationReceipt.lean:724       │ P    │ K      │ P-Ou  │ —    │
│ Shared/GateReceipt.lean:363               │ P    │ K      │ P-ShA │ —    │
│ Shared/HeadAdmit.lean:214                 │ P    │ K      │ P-ShA │ —    │
│ Shared/OutputGrowthCausal.lean:47         │ P    │ K      │ P-ShA │ —    │
│ Shared/Relay.lean:145                     │ P    │ K      │ P-ShA │ —    │
│ Shared/Relay.lean:577                     │ P    │ K      │ P-ShA │ —    │
│ Shared/RetainedEndpoint.lean:35           │ P    │ K      │ P-ShA │ —    │
│ Shared/RetainedReflect.lean:337           │ P    │ K      │ P-ShA │ —    │
│ Shared/SameLabel.lean:207                 │ P    │ K      │ P-ShA │ —    │
│ WeakContinuation/StepGateBatch.lean:379   │ P    │ K      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1564 │ P    │ K      │ P-WC  │ —    │
│ Run/Proofs/Schedule.lean:586              │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:613              │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:783              │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:843              │ P    │ K      │ W3    │ —    │
└───────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:225; Run/Tests/SleepContinuationAxioms.lean:14.

`fgsa_stored_block_origin`:

```text
┌─────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base         │ Type │ Source │ Owner │ Open │
├─────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Finality/MiddleSupport.lean:757 │ P    │ K      │ P-Fi  │ —    │
│ Healing/Promotion.lean:35       │ P    │ K      │ P-H1  │ —    │
│ Shared/RetainedEndpoint.lean:47 │ P    │ K      │ P-ShA │ —    │
│ Shared/ScoreRun.lean:897        │ P    │ K      │ P-ShA │ —    │
│ Shared/ScoreRun.lean:1127       │ P    │ K      │ P-ShA │ —    │
└─────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:236; Run/Tests/SleepContinuationAxioms.lean:29.

`fgsa_tick_total`:

```text
┌──────────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                      │ Type │ Source │ Owner │ Open │
├──────────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Assembly/WeakContinuation.lean:538           │ F    │ T01    │ P-As  │ M    │
│ Assembly/WeakContinuationGrowth.lean:377     │ F    │ T02    │ P-As  │ M    │
│ Assembly/WeakContinuationGrowth.lean:572     │ F    │ T03    │ P-As  │ M    │
│ Assembly/WeakContinuationGrowthSeed.lean:195 │ F    │ T04    │ P-As  │ M    │
│ Clean/Closure.lean:200                       │ F    │ T05    │ P-Cl1 │ M    │
│ Clean/Closure.lean:298                       │ F    │ T06    │ P-Cl1 │ M    │
│ Clean/Safety.lean:197                        │ F    │ T07    │ P-Cl1 │ M    │
│ Clean/StepGate.lean:212                      │ F    │ T08    │ P-Cl1 │ M    │
│ Clean/StepGate.lean:257                      │ P    │ T09    │ P-Cl1 │ —    │
│ Clean/StepGate.lean:447                      │ F    │ T10    │ P-Cl1 │ M    │
│ Clean/StepGate.lean:566                      │ P    │ T11    │ P-Cl1 │ —    │
│ Clean/StepGate.lean:569                      │ F    │ T12    │ P-Cl1 │ M    │
│ Finality/RowsPrem.lean:91                    │ P    │ T13    │ P-Fi  │ —    │
│ Finality/TailFrame.lean:383                  │ P    │ T14    │ P-Fi  │ —    │
│ Healing/FrontierSearchTasks.lean:211         │ P    │ T15    │ P-H2  │ —    │
│ Healing/OpeningServiceBody.lean:197          │ P    │ T16    │ P-H2  │ —    │
│ Healing/OpeningServiceOne.lean:29            │ F    │ T17    │ P-H2  │ M    │
│ Healing/PostResetGate.lean:265               │ P    │ T18    │ P-H2  │ —    │
│ Healing/PostResetOpening.lean:163            │ P    │ T19    │ P-H2  │ —    │
│ Healing/PostResetRaw.lean:592                │ P    │ T20    │ P-H1  │ —    │
│ Healing/PostResetRaw.lean:811                │ P    │ T21    │ P-H1  │ —    │
│ Healing/PostResetService.lean:235            │ P    │ T22    │ P-H2  │ —    │
│ Healing/SupportHeads.lean:110                │ F    │ T23    │ P-H1  │ M    │
│ Healing/SupportOutput.lean:261               │ P    │ T24    │ P-H1  │ —    │
│ Outage/ArmingBatch.lean:63                   │ F    │ T25    │ P-Ou  │ M    │
│ Outage/ContinuationReceipt.lean:462          │ P    │ T26    │ P-Ou  │ —    │
│ Outage/ContinuationReceipt.lean:465          │ F    │ T27    │ P-Ou  │ M    │
│ Outage/ContinuationReceipt.lean:626          │ P    │ T28    │ P-Ou  │ —    │
│ Outage/ContinuationReceipt.lean:629          │ F    │ T29    │ P-Ou  │ M    │
│ Outage/ContinuationReceipt.lean:820          │ F    │ T30    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:299        │ F    │ T31    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:513        │ P    │ T32    │ P-Ou  │ —    │
│ Outage/ExactProposalRetained.lean:519        │ F    │ T33    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:581        │ F    │ T34    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:726        │ F    │ T35    │ P-Ou  │ M    │
│ Outage/InclusionGate.lean:55                 │ F    │ T36    │ P-Ou  │ M    │
│ Outage/InclusionGate.lean:119                │ F    │ T37    │ P-Ou  │ M    │
│ Outage/InclusionGateBody.lean:55             │ F    │ T38    │ P-Ou  │ M    │
│ Shared/ExactHead.lean:193                    │ F    │ T39    │ P-ShA │ M    │
│ Shared/ExactService.lean:462                 │ F    │ T40    │ P-ShA │ M    │
│ Shared/GateReceipt.lean:269                  │ P    │ T41    │ P-ShA │ —    │
│ Shared/GateReceipt.lean:272                  │ F    │ T42    │ P-ShA │ M    │
│ Shared/HeadAdmit.lean:387                    │ P    │ T43    │ P-ShA │ —    │
│ Shared/OutputGrowthProposal.lean:32          │ P    │ T44    │ P-ShA │ —    │
│ Shared/RetainedEndpoint.lean:293             │ F    │ T45    │ P-ShA │ M    │
│ WeakContinuation/ExactProposal.lean:214      │ F    │ T46    │ P-WC  │ M    │
│ WeakContinuation/Inclusion.lean:78           │ F    │ T47    │ P-WC  │ M    │
│ WeakContinuation/Inclusion.lean:332          │ F    │ T48    │ P-WC  │ M    │
│ WeakContinuation/Proposal.lean:203           │ F    │ T49    │ P-WC  │ M    │
│ WeakContinuation/Proposal.lean:750           │ F    │ T50    │ P-WC  │ M    │
│ WeakContinuation/StepGateBatch.lean:305      │ P    │ T51    │ P-WC  │ —    │
│ WeakContinuation/StepGateBatch.lean:308      │ F    │ T52    │ P-WC  │ M    │
│ WeakContinuation/StepInputs.lean:155         │ F    │ T53    │ P-WC  │ M    │
│ WeakContinuation/StepService.lean:201        │ F    │ T54    │ P-WC  │ M    │
│ WeakContinuation/StepTransfer.lean:44        │ F    │ T55    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:811     │ F    │ T56    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:1015    │ F    │ T57    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:1488    │ P    │ T58    │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1491    │ F    │ T59    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:3074    │ F    │ T60    │ P-WC  │ M    │
│ Tests/InclusionGate.lean:71                  │ F    │ T61    │ P-Ou  │ M    │
└──────────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:215; Run/Tests/SleepContinuationAxioms.lean:12.

`fgsa_gate_clock_bridge`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Healing/SupportWrite.lean:75 │ F    │ GF     │ P-H1  │ —    │
│ Shared/ExactService.lean:218 │ A    │ G      │ P-ShA │ —    │
│ Shared/OpeningSource.lean:49 │ A    │ G      │ P-ShA │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:224; Run/Tests/SleepContinuationAxioms.lean:13.

`fgsa_release_clockPre`:

```text
┌───────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base               │ Type │ Source │ Owner │ Open │
├───────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Healing/DescentLossUnanimous.lean:291 │ P    │ RN     │ P-H1  │ —    │
│ Healing/SupportTransfer.lean:72       │ F    │ RR     │ P-H1  │ —    │
│ Healing/SupportTransfer.lean:306      │ P    │ RN     │ P-H1  │ —    │
└───────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:229; Run/Tests/SleepContinuationAxioms.lean:23.

`fgsa_release_input_votes_stamped`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Run/Proofs/Schedule.lean:888 │ P    │ C      │ W3    │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:230; Run/Tests/SleepContinuationAxioms.lean:24.

`fgsa_release_count_bridge`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:232; Run/Tests/SleepContinuationAxioms.lean:26.

`fgsa_gate_saved_result`:

```text
┌────────────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                        │ Type │ Source │ Owner │ Open │
├────────────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Clean/StateGate.lean:32                        │ F    │ GR     │ P-Cl1 │ M    │
│ Shared/Reads.lean:161                          │ A    │ G      │ P-ShA │ —    │
│ WeakContinuation/StepGateHistory.lean:139      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepOutput.lean:29            │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepService.lean:30           │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepTransfer.lean:91          │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepTransferReceipts.lean:415 │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:639       │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1877      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:2153      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:2965      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:3121      │ A    │ G      │ P-WC  │ —    │
└────────────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:235; Run/Tests/SleepContinuationAxioms.lean:27.

`timely_of_relay_retained`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Run/Proofs/Receipts.lean:883 │ P    │ RT     │ W3    │ —    │
│ Run/Proofs/Receipts.lean:985 │ P    │ RT     │ W3    │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/SleepContinuationAxioms.lean:10.

Exact awake obligations (T01–T61):

A(v,t) means `E.awake v t = true`. The true tick consumer form is the existing
schedule, honesty, public-time and horizon premises plus A(v,t), giving
`∃! i, rho.events[i]? = some (.tick v t)`. Each T row supplies the exact v and t.
For an F row, this is the required replacement of the false unconditional tick subclaim;
the owner must propagate it through the enclosing helper and callers. It does not certify
all other sleep obligations of that enclosing theorem. Public premise changes need a ruling.
The three generic helpers keep their current existential conclusions after adding:
opening_action_tick: A(x,a(r)); healing_support_vote_tick: A(z,v(i));
arming_tick_exists: A(y,t), where t=mΔ. None currently has a public source for A.

Here a(r)=p.actionTime r, v(s)=SA.voteTime p.toParams s,
d(s)=SA.gateTime p.toParams s, e(s)=SA.earlyTime p.toParams s,
f(s)=SA.freezeTime p.toParams s, q(s)=SA.releaseTime p.toParams s,
t(s)=SA.proposalTime p.toParams s, and R=p.R. All times use p.Δ.
`seat(head s,k)` means rho.seatOf (.base (.head s)) k;
`proposer(s)` means V2.D.proposerOf rho (fgsaInterface p c) s.
Recovery sources use the unchanged Recovery₂.awake (approved P8, packet :2288–2325).
The cited H0Reset sources use synchronous and label (P8/D041, packet :2571–2597).

- T01: A(x,v(w.u+1)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T02: A(x,v(pt.s)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T03: A(x,d(pt.s)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T04: A(x,v(w.u+1)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T05: A(x,d(s)). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T06: A(y,v(s+1)). Source: premise source missing; P-Cl1 must supply A at this exact time or
  avoid this tick.
- T07: A(x,d(l)). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T08: A(x,2Δ). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T09: A(seat(head0,k),v(0)). Source: hka from (hH k).mp hk, at voteTime 0.
- T10: A(x,d(s)). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T11: A(y,v(s+1)). Source: the explicit hawake for selected voter y, at voteTime (s+1).
- T12: A(x,e(s+1)). Source: premise source missing; P-Cl1 must supply A at this exact time or
  avoid this tick.
- T13: A(y,v((pt.r+2)R)). Source: hK.set.awake y hy _ hGSTq (kmid_slot_horizon hK le_rfl).2.1.
- T14: A(y,v((pt.r+1)R)). Source: hT.set.awake y hy _ hGST hhorZ.2.1.
- T15: A(x,a(rG+2)). Source: hrec.awake x hx u₀ (hdelay implies GST ≤ u₀) hhor; hu₀ fixes a(rG+2).
- T16: A(y,a(r)). Source: hrec.awake y hy a(r); GST ≤ u ≤ proposalTime q ≤ a(r); har.trans hvh.
- T17: A(x,a(r)). Source: premise source missing; P-H2 must supply A at this exact time or avoid
  this tick.
- T18: A(x,d(s)). Source: hrec.awake x hx d(s); hgst bounds voteTime s, which is ≤ d(s);
  hGateHorizon.
- T19: A(x,v(v)). Source: hrec.awake x hx v(v); H0Reset.synchronous and w.sStar+2 ≤ v give GST ≤
  v(v); hh.
- T20: A(y,d(s+1)). Source: hrec.awake y hy d(s+1); hgst ≤ voteTime s ≤ d(s+1); hguard.
- T21: A(x,q(w.sStar)). Source: hrec.awake x hx q(w.sStar); h0r.synchronous ≤ q(w.sStar);
  hqg.trans hhor.
- T22: A(x,d(v)). Source: hrec.awake x hx d(v); postReset_synchronous_window hreset hv ≤ d(v);
  hGateHorizon.
- T23: A(z,v(i)). Source: premise source missing; P-H1 must supply A at this exact time or avoid
  this tick.
- T24: A(y,d(s+1)). Source: hrec.awake y hy d(s+1); hgst1 ≤ voteTime(s+1) ≤ d(s+1); hhor.
- T25: A(y,t=mΔ). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T26: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T27: A(x,e(s)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T28: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T29: A(x,e(s)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T30: A(x,f(s)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T31: A(x0,d(q)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T32: A(seat(head(q+1),w),v(q+1)). Source: (hH w).mp hw: selected honest awake voter at voteTime
  (q+1).
- T33: A(x,e(q+1)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T34: A(y,e(q+1)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T35: A(x,v(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.
- T36: A(y,v(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.
- T37: A(y,d(s-1)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T38: A(x,d(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.
- T39: A(y,v(s)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T40: A(x,d(v)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T41: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T42: A(x,e(s)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T43: A(seat(head s,a),v(s)). Source: hawake _ hy, from the caller's all-selected-voters awake
  premise, at voteTime s.
- T44: A(proposer(s),t(s)). Source: ha for the chosen proposer at proposalTime s; he identifies
  this time.
- T45: A(y,v(s)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T46: A(x,v(pt.s)). Source: premise source missing; P-WC must supply A at this exact time or
  avoid this tick.
- T47: A(x,v(pt.s)). Source: premise source missing; P-WC must supply A at this exact time or
  avoid this tick.
- T48: A(x,d(pt.s)). Source: premise source missing; P-WC must supply A at this exact time or
  avoid this tick.
- T49: A(y,d(s-2)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T50: A(x,e(q+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T51: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T52: A(x,e(s)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T53: A(y,d(s-1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T54: A(y,d(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T55: A(y,v(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T56: A(y,d(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T57: A(y,d(s-1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T58: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T59: A(x,e(s)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T60: A(y,v(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T61: A(x,d(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.

P6 joined participation (packet :2080–2082, :2094–2097, :2110–2112) counts
joinedHonest at a specified time. Membership gives A at that time via joinedAt
(packet :4092–4097); it does not give A for an arbitrary honest receiver or another time.
Where a proof needs only an existential honest tick, choose its witness from a nonempty
counted awake/joined set at that requested time. Where it names a receiver, retain that
receiver and require its approved Ready/receiver window. No listed M row currently contains
that exact receiver/time premise, so this handoff does not claim that P6 closes it.


Tick existence also does not prove a duty emission. The approved HEAD target is
`∀ x ∈ rho.honest, joinedAt p E rho x s (SA.voteTime p.toParams s) → Q x`,
where Q is the kept HEAD/receipt conclusion (P10, packet :3876–3887).
A joinedAt witness supplies A at that vote time and both wake/restart bounds
(:4092–4097). A proposal emission needs the proposer's joinedDuty at proposalTime s
(P7, packet :2238), not only its awake premise. An executed gate conclusion uses
`enabledGateAt j x s → Q j x s` (P11, packet :4379–4381); its gate event supplies
that tick directly, and its marker bound supplies G. These are approved scope forms.
They do not supply earlier early/freeze ticks for a receiver. Those calls still need
A at the exact earlier times in T01–T61, or a proof that does not require those ticks.
No M row is closed by merely substituting an awake or counted-set fact at another time.

For G rows in WC/WCG, the current NoRestart also proves the marker is none.
The sleep port must instead use enabledGateAt or a nonempty executed result, with the
P11 guard above. In StepGateHistory:139, a raw nonempty confirmation is not an executed
result; establish enabledGateAt first. If its future sleep premises do not establish it,
that family owner must mark the premise source missing rather than infer it from raw data.
For Shared/ExactService:218 and OpeningSource:49, unfold GateService's executed result
through fgsaAC and guarded gateResult; the nonempty result is the source of the gate guard.
S-Ap writes the guarded public read; P-ShA proves the read bridge. The raw read remains diagnostic.

False helper caller checks (source only; these caller files stay with their owners):

- SupportTransfer.release_rows: DescentLossUnanimous:292, SupportTransfer:307,
  PostResetRawStep:205. Pass the same release guard. Recovery + τ or an executed joined
  receiver window can supply it; arbitrary survival cannot. DescentLossUnanimous:292
  and PostResetRawStep:205 have hrec.base.noRestart; SupportTransfer:307 has hN.
  PostResetRawStep:205 uses only the expiry-membership projection, so the conditional
  release_rows form also suffices. Owner P-H1/P-H2 (§14.6/§8.3).
- SupportWrite.fastWrite: SupportWrite:117, FrontierSupportTransfer:55, FrontierRead:81,
  SupportLease:273. Keep an unconditional equation only with the guard on fastSet.
  SupportWrite:117 and FrontierRead:81 have hres = some(some C), so G supplies joinedness.
  FrontierSupportTransfer:55 has hrec.base.noRestart; SupportLease:273 has hB in the
  actual fastWrite row. Gate freshness + the unjoined empty-row law makes that a joined witness.
  A raw fs equation cannot supply it. Owners P-H1/P-H2 must trace each premise (§14.6).
- StateGate.clean_gate_raw: StateGate:79,96,134,147,192; Transfer:63; GateOutput:41;
  StepGate:74,298,740; TransferFrame:133,320. Executed result some(some B) gives G.
  Calls that construct a result from raw confirmation must first establish enabledGateAt.
  P-Cl1 owns that source check (§14.6); a gate event alone leaves the premise source missing.
- OpeningServiceOne.opening_action_tick: OpeningServiceOne:86, FrontierOpen:172,
  Require A(x,a(r)); the applicable Recovery.awake plus
  GST ≤ a(r) ≤ horizon must be passed at each call. P-H2 owns these checks (§8.3/§14.6).
- SupportHeads.vote_tick: all callers in Healing must pass A at their requested voteTime.
  A counted voter supplies its own awake membership; Recovery/H0Reset must prove the
  exact lower and horizon bounds for other receivers. Owners P-H1/P-H2 (§14.6).
- ArmingBatch.arming_tick_exists: ArmingBatch:181,183 and ArmingGate:316.
  Require A(y,earlyTime(l+1)), A(q,voteTime(l+1)), A(y,gateTime(l+1)), respectively.
  Awake counted voter membership can supply the middle call only for that selected q;
  receiver readiness at one time does not cover the two other times. P-Ou owns the
  missing receiver/window sources (§14.6, family owner).
- Strict gate-late helpers: SupportRelay:92, Shared/Relay:144, Shared/SameLabel:206.
  Keep their strict lateVotes conclusion with J. Relay callers :626,628,629 use current
  NoRestart; SupportRelay:171,173,174 and SameLabel:295,297,298 must prove hEpoch
  or use an approved joined gate scope. P-H1 and P-ShA own those checks (§14.6).

Counts cover the 170 direct uses; M overlaps F. Audit commands and guard splits are excluded.

```text
┌───────────────────────────────┬───────┐
│ Classification                │ Count │
├───────────────────────────────┼───────┤
│ proof-only repair             │ 110   │
│ approved change of read/scope │ 13    │
│ false internal consumer type  │ 47    │
│ premise source missing        │ 42    │
└───────────────────────────────┴───────┘
```

### Other W2b review fixes

- P1/P3 valid-run test: Sleep.own_valid (:179) proves full ExecutionValid for ownRun.
  Sleep.own_record_retained (:248) checks an own FG row at time 28, nonempty sent entries
  before sleep on [31,35), and equal sent entries and full Λ after wake 35.
  Both new theorem audits use only propext, Classical.choice and Quot.sound.
- SleepContinuation.gate_empty (:64) is API coverage. Its raw fixture result is also empty;
  no discriminating skipped-versus-executed confirmation claim is made.
- Package map (§1.4/§8.1/§8.2): NamedDelivery and RetainedClock are TARGETS.
  ReceiptCoverage Statements is S-Ap; owners are W3 52, P-ShA 45, S-Ap 14.

## S-Ap part 1 — public statement slice (2026-10-10)

- Approved P5–P7, P10–P16, P18, P21/P22 vocabulary: Join, executed gate reads,
  joined participation and recurrence, recovery readiness, and store/frame companions.
- P23 and DECISION P23-A changes wait for part 2 and W3's new root definitions.
- Import routing: gatePassedAt moves from Reads to Join with the exact P11 body.
  Join needs Reads for IsGateTick/storeAt; the reverse import would form a cycle.
  Channels imports Join. Public names and predicate meanings stay as approved.
- Packet elaboration context: schedule-only parameters p/c are implicit when they
  occur only in rho's type. Read predicates keep the explicit packet arguments.
  Reads supplies a local Decidable instance for the optional restart cutoff.
- Packet typo, r9 form (P10/P11 slot-labelled caught-up gate): caughtUpAtIdx's `∃ s j` infers s : Int
  from `(s : Int)` before gateTime requires Slot. Use `∃ (s : Slot) (j : Nat)`.
  This is a type annotation; its gate label, cutoff and quantifiers are unchanged.
- Slice validation: all 58 manifest source modules build with --wfail; layers have
  zero new findings. Claims.Tests.Axioms builds with the added statement audits.
- Manifest generation uses an untracked copy of V2Manifest.lean with only the
  facade-import loop omitted. Every source module in all four public prefixes
  and FGSAClaims.FGSAClaims is still scanned; hashing and entry selection are unchanged.
  The full facades import unfinished fixtures/P23. No checker or baseline is changed.
  The regenerated document also records inherited W1–W3 changes. Allow pins change
  only for entries in S-Ap source files; P-Da owns the remaining baseline reconciliation.

### S-Ap part 1 — remaining public companions

- P8/P9: recoveryStart routes the ready windows, old-row cap, H0Reset,
  healing/reset horizons, finality premises and WC recovery endpoint through tauC.
- P10/P20: output service, growth, LiveDC and healed statement readers use the
  approved joined/confirmed scopes. The family Claims conclusions stay with their owners.
- P12–P18: OutageContinuationSleepPrem and the derived receipt/E1 contracts are added.
  OutageContinuationConcl and its Claims wrapper stay with P-Ou as family conclusion text.
- P19: CleanContinuationSleep₂, CleanGrowthContinuationSleep₂ and SourcePendingReceipt
  route the public WC/WCG regime, delivery and bounded-recovery types as approved.
- P21(a): FinalizedMonotonicityRestartClaim replaces the aggregate field type.
  FinalizedMonotonicityClaim and its NoRestart premise are retained byte for byte.
- P22: FGFoundation and FGFoundationNext use RStoreDurable/RStoreEpoch, RMonoAll,
  and RFrameNextEpoch. Old R6 definitions and equations are unchanged.
- Source check: all 121 packet blocks marked to keep old text are present unchanged.
  P23, all DECISION P23-A root-premise changes, and the two W3-owned files are deferred.
- Structural test transfer (02:45 ruling): the two unchanged Axioms equality examples
  for ServedFromGateAt/InclusionAt and JointGrowthAt/AvailableGrowthConcl move to
  Tests.OutageAlignment. The production aggregate supplies their family claims.
  P-Ou owns their EXPECTED-FAIL until its approved P10/P20 claim text lands.
  Their statements and rfl proofs are unchanged. No exception/baseline is added.
- P7/P8 rename the obsolete gapWin and formWinAt exports to gapWinReady and
  formWinAtReady as approved. The matching audit commands use the new names.
- Claims.Tests.Axioms inventory regenerated from 813 compiled command owners.
  Only that audit key changes in scripts/proof-audit-coverage.txt.
  Complete compiled coverage: zero unaccepted exports; the equation baseline is unchanged.

### S-Ap part 1 — validation result

- GREEN: 432 modules, lake build --wfail PASS (4.76 s final run).
- S-Ap DCK: PASS (151.89 s), 35 strict audits / 3,276 results and all 24 controls.
  Only propext, Classical.choice and Quot.sound appear.
- Complete export/coverage check: PASS (6.73 s), zero unaccepted exports.
  Tracked Claims coverage check: PASS (4.67 s), 813 command/owner rows.
- Layers: 72 accepted findings, zero new (0.61 s).
- Source checks: 113 selected Statements blocks match, 121 fixed blocks unchanged;
  new Lean lines at most 100; no sorry/admit/axiom; W3-owned files unchanged.
- EXPECTED-FAIL: 50 modules with explicit owners. The only new test handoff is
  OutageAlignment to P-Ou (unchanged equality examples; failure confirmed in 7.25 s).
- Manifest generation: 58-module slice 84.64 s; 59-module companion surface 104.32 s.
  No package-full or G-S3 claim is made; P23 and family work remain with their owners.
## W3 — P23-A receipt scope and bridge (2026-10-10)

- DECISION P23-A, lead 04:05: keep P23 option (a). The receipt idealization includes
  honest emitted bodies and their named ancestors. It replaces the old root premise
  in receipt suppliers. No per-required NamedProposalInRun premise is added to P23.
  This decision closes the W3 core stop recorded above. The old ReceiptAlias trace
  remains a counterexample to the old form; it fails the new receipt idealization.
- New internal statements, P23-A: NamedProposalReceiptScope and
  NamedReceiptRootCollisionFree in Run/Statements/Roots. The old direct and ancestor
  scopes are unchanged. The docstrings state that a global form over all values is
  false because root is a free field. This is an idealization under valid execution.
- New internal statements, P23-A: namedReceiptScope_of_namedScope embeds old scope;
  namedReceiptScope_emitted includes each honest emitted body and its ancestors;
  namedReceiptScope_ancestor closes that scope under ancestry.
  NamedReceiptRootCollisionFree.toNamedRootCollisionFree supplies root_injective,
  including both old tips' ancestor alternatives. Consumers: NamedDelivery,
  Receipts, the ready core, and S-Ap's pending Base2.idealization projection.
- New internal statements, P23-A: proposal_trigger_in_receipt_scope splits emission
  from relay source acceptance. proposal_processed_in_scope extracts the exact
  named body of a processed FG root (genesis or MetaInv.treeWire/wireTree), gives
  that witness old scope, and identifies it with the receipt-scoped required body.
  It needs an honest receiver; it needs no history persistence or deadline receipt.
  emitted_proposal_history_in_scope applies this extraction to ProcessedByActionCut
  for an honest emission. proposal_trigger_service_in_scope uses the history bridge
  in DeliveryService's history arm, proposal_handle_in_scope in its handled arm,
  and the source acceptance in the relay arm. The anchor may be after emission.
  Consumers: Receipts, the ready core, WC/WCG scope readers, and family sleep readers.
- Changed internal statement, P23-A: fgsa_proposal_receipt replaces hRoots with
  NamedReceiptRootCollisionFree and drops hScope. Its Trigger supplies receipt scope;
  processing at the deadline and proposal_processed_in_scope supply old scope.
  AwakeOn, horizon, validity, NoRestart, deadlines, and the exact receipt remain.
  The new ready core is its active in-package caller. The old ReceiptCoverage
  wrapper is unchanged for S-Ap's explicit option (a) retirement.
- Out-of-package proposal callers: replace the root argument with receipt collision
  freedom, keep the approved readiness/horizon inputs, and remove any hScope input.
  Base2 callers use receiptIdealization after S-Ap changes that field. Flat argument
  lists must carry the stronger premise. These are family-owned argument swaps:

```text
┌────────┬─────────────────────────────────────────────────────────────────────┐
│ Owner  │ AvailableChainFGSAProofs/Proofs caller                               │
├────────┼─────────────────────────────────────────────────────────────────────┤
│ P-ShA  │ Shared/HeldReceipt.lean:80; Shared/GateReceipt.lean:198                │
│ P-ShA  │ Shared/ScoreRun.lean:497                                             │
│ P-Ou   │ Outage/ExactProposal.lean:71                                         │
│ P-WC   │ WeakContinuation/ExactProposal.lean:233                               │
│ P-As   │ Assembly/WeakContinuationGrowth.lean:397                             │
│ P-H1   │ Healing/PromotionReceipt.lean:128,200                                │
│ P-H2   │ Healing/RiseOneAccept.lean:93                                        │
│ P-H2   │ Healing/SupportRelay.lean:380; Healing/DescentLossNext.lean:128        │
│ P-H2   │ Healing/PostResetRaw.lean:1291; Healing/PostResetLeaseMove.lean:102    │
│ P-H2   │ Healing/SourceTiming.lean:293; Healing/PhaseRelay.lean:145,435         │
└────────┴─────────────────────────────────────────────────────────────────────┘
```

- WC ExactProposal:254 and Assembly/WeakContinuationGrowth:418 can use
  proposal_trigger_service_in_scope with the same ready service, or supply
  emitted_proposal_history_in_scope to the existing scope callback. Relay readers
  can still use proposal_handle_in_scope directly. Their old helpers stay available.
- INTENTIONAL DC divergence: P2 permits a processed-root service instead of another
  handler. Main's handler delivery excluded the alias trace only implicitly.
  PC-SA has the same root-keyed processedS pattern. Its P2 receipt port remains an
  open PC-SA-owned item; apply route A there. No PC-SA declaration changes here.
- S-Ap owns Base2.receiptIdealization, its old idealization projection, the public
  sleep statement/equation, public assumption lists, and retirement of the three
  legacy P23 names. Safety-only statements retain NamedRootCollisionFree. Families
  own stronger fixture evidence and their caller changes. No FGSAClaims statement
  or Base2 declaration is changed by W3.

## W3 — P23-A ready core, tests, and owners (2026-10-10)

- New internal statement, P23-A: fgsa_receiptCoverage_ready in
  Run/Proofs/ReceiptCoverageReady. It replaces NamedRootCollisionFree with
  NamedReceiptRootCollisionFree and adds the approved awake receipt windows.
  ReceiptCoveragePremises is unchanged. There is no per-required scope argument.
  The full finality/output/HEAD/lease/path/stamp conclusion is unchanged. Proposal
  receipt uses the exact processed-body bridge; the deadline and horizon bounds
  follow from the unchanged record. New proofs use default heartbeats.
- The core is in a separate module so S-Ap can retire the old wrapper and statement
  files under option (a). The Run facade imports the new core, but its legacy import
  remains until that retirement. The legacy files are unchanged by this job.
- Family coverage argument swaps: Shared/Count.lean:169 (P-ShA) and
  Outage/ContinuationReceipt.lean:128,178 (P-Ou) replace fgsa_receiptCoverage with the
  ready core or the S-Ap sleep wrapper. Pass receipt collision freedom and the
  approved readiness inputs; do not add per-required scope to the public form.
  The concrete ReceiptCoveragePremises producers and their required predicates
  stay unchanged. Their sleep migration remains with the family owners.
- Kernel controls: Tests/EmissionFreshness.receipt_roots_false refutes the new
  idealization on the original valid alias run. Tests/ReceiptAlias is unchanged
  and retains the negative control for the old form. Tests/ReceiptReady supplies
  full ExecutionValid and receipt collision freedom on a nonempty trace ending
  before the colliding emission. Its nonempty required predicate names the accepted
  slot-1 proposal. coverage_ready applies the new core and obtains its exact body
  in the receiver's tree at deadline 9.
- Registration: ReceiptCoverageReady and ReceiptReady are S1 REQUIRED and W3
  TARGETS/GREEN. Roots and NamedScope are explicit W3 targets. W3Axioms prints every
  new public theorem and both new definitions. The full Run audit and fixed owner
  inventory contain the same new production declarations. Test-local audits print
  the negative control and positive validity/root/premise/coverage results.
- The three current S-Ap-P23-STOP map owners are replaced by S-Ap: Run,
  Proofs/ReceiptCoverage, and Tests/Axioms remain EXPECTED-FAIL for public retirement.
  The other S-Ap and family-owned EXPECTED-FAIL entries are unchanged. Historic STOP
  records above describe the old boundary; P23-A closes the W3 scope/core item.
- Restore export fix 672dbc93 is present through lead merge 2eba122b. The complete
  export check will rerun against this fix and the new ready core, with no new
  baseline, allow-list, or exception entry.

## W3 — P23-A final validation (2026-10-10)

- Implementation commits: 53112f9f (scope/bridge), 82bf0910 (ready core/tests/maps).
- Final validation passes on 406 GREEN modules. The map retains 61 owned
  EXPECTED-FAIL modules. No W3 P23-A STOP remains. S-Ap still owns the legacy
  public retirement and full Run/audit roots; family argument swaps remain owned.
- DCK PASS: 35 strict roots, 2,482 results, all 24 controls. Only propext,
  Classical.choice, and Quot.sound occur. ReceiptReady prints all seven public laws.
- Complete W3 export/audit coverage PASS: 116 proof modules, 250 exports,
  0 unaccepted. The generated inventory has 97 entries across W3Axioms and the
  three receipt controls. It uses the same explicit-root boundary as prior W3
  checks, now including the ready core and controls. The default roots still
  reach the S-Ap-owned legacy wrapper. The 17 Restore exports are removed.
- No baseline, checker, protocol/model, FGSAClaims, Base2, or legacy P23 file
  changed. Layer check: 72 findings, 0 new. New proofs use default heartbeats.

```text
┌────────────────────────────────────┬────────┬───────────┐
│ Check                              │ Result │ Wall (s)  │
├────────────────────────────────────┼────────┼───────────┤
│ Focused core/tests/audit --wfail   │ PASS   │ 6.58      │
│ Complete GREEN --wfail             │ PASS   │ 54.51     │
│ Final GREEN --wfail                │ PASS   │ 10.91     │
│ W3 DCK + strict audits + controls  │ PASS   │ 403.38    │
│ Layers: 72 findings, 0 new         │ PASS   │ 0.39      │
│ Complete export/audit coverage     │ PASS   │ 38.20     │
└────────────────────────────────────┴────────┴───────────┘
```

## P-ShA — independent core and S-Ap handoff (2026-10-10)

- R6: Shared/StoreRun.fgsa_store_durable keeps TF, blocks, proposals and rowPool
  across restarts. fgsa_store_cumulative_on keeps the complete six-field tuple
  on restartFree rho x i j. The legacy fgsa_store_cumulative statement stays
  fixed and follows from the epoch form. Index endpoints are i ≤ k < j.
- N4 core: Shared/CatchUp.fgsa_catchUp_before_freeze uses the exact ReadyTrigger,
  HistorySafeAt, service law and receiver epoch. Its deadline is at or before
  freeze. Processing at the strict-before deadline persists to the strict-before
  freeze. The ready handler branch has a receipt strictly before the deadline.
  The retained-history branch needs HistorySafeAt; wake alone supplies no history.
  A fresh post-join anchor can use historySafeAt_of_fresh instead.
  Count, HeadAdmit and retained-proposal adapters remain open until the S-Ap slice.
- N7 supplier: fgsa_gate_joined_of_joinedEnv takes the approved environment
  restart bound at this exact gate and returns joinedAtTime on its pre-tick store.
  Consumers P-Cl1, P-Ou and P-WC can pass the restart projection of joinedAt.
  fgsa_joinedNow_noRestart keeps the legacy callers working at an existing tick.
- P11 bridge: fgsa_gate_saved_guarded proves the saved equation in both join
  branches. Its unjoined result is some none. Shared/Reads remains EXPECTED-FAIL
  until S-Ap installs the guarded executed read. The candidate adapter is in
  claude-files/psha-reads-after-sap.patch; it has not been compiled.
- internal statement, lead ruling 10-10: Relay.relay_gate_late and
  SameLabel.sl_gate_late were false with schedule alone. They now require hEpoch
  at their gate and keep the same strict late-pool conclusion. Every current
  caller supplies hEpoch from its existing NoRestart premise. Consumers:
  Relay.relay_head_witness and SameLabel.sl_relay (private).
- internal statement, lead ruling 10-10: fgsa_vote_accepted_before_head_read now
  takes ExecutionValid, since the exact receipt clock uses the awake delivery
  and wake laws. Its consumer relay_head_witness already has that premise.
- internal statement, lead ruling 10-10: the two OutputGrowthProposal helpers
  ending in _of_awake_slot need the approved joined proposer restart bound.
  Awake alone allows a restart at the proposal tick, which gates the emission.
  The conclusion is fixed. Sources are the joined proposer clauses in P6 and
  the family packet. Consumers: Shared/Claims; Outage/Growth;
  WeakContinuation/Growth; WeakContinuationGrowth/Empty; Finality/MiddleSupport;
  Healing/PromotionCarrier, LiveDC and Repair. Those family ports remain open.
- P23-A: GateReceipt and ScoreRun now use NamedReceiptRootCollisionFree for
  proposal receipts. Their callers pass the same receipt premise. A safety-only
  equality in ScoreRun projects toNamedRootCollisionFree. No hScope is added.
- Receipt caller repair: GateReceipt, Relay, SameLabel and ScoreRun supply the
  exact receiver awake interval and horizon bound. In the legacy NoRestart
  route, ExecutionValid at the existing receiver tick gives the interval.
  GateReceipt T41 uses its explicit selected-voter hawake. Its early actor tick
  follows from the existing gate tick and NoRestart. This does not close the
  sleep T42 route; that route must use the enabled-gate source below.
- Proof-only K/L repairs keep origin fields and use the exact wake clock law.
  OutputGrowthCausal splits tick and restart clock sources. Slot bounds use
  non-strict now ≤ tick where strictness is unnecessary.
- Validation scope: 14 former P-ShA failures are GREEN, together with the new
  CatchUp module, five support modules, Tests/BoundsW and Tests/SharedAxioms.
  No remaining owned EXPECTED-FAIL repair is closed. Package inputs retain the
  W3-owned and S-Ap-owned classifications. Default heartbeats are unchanged.
- Core validation: the 22-module green build passed --wfail (3.880 s).
  P-ShA DCK passed with all controls (259.627 s). The complete export check
  scanned 138 proof modules / 251 exports: 0 unaccepted (4.556 s).
  The green proof audit checked 149/149 results: only propext, Classical.choice
  and Quot.sound (3.224 s). SharedAxioms has 20 strict results.
  check-layers reports 0 new findings. The broad transparency check still has
  two inherited ClientTrace findings; W3 owns that file and its review fix.

## P-ShA — prepared files, not closed (2026-10-10)

- P23-A forwarding is prepared in Count, ExactHead, ExactService, HeadAdmit,
  RetainedPersist, RetainedReflect, RetainedEndpoint and Regimes. Receipt routes
  take NamedReceiptRootCollisionFree. Regimes forwards base.receiptIdealization.
  These modules remain EXPECTED-FAIL and have not been compiled against S-Ap.
- T39 RESTRUCTURE: exactService_head_of_proposal now has the approved joined HEAD
  reader scope. Its two Regimes adapters keep that scope. There is no live public
  caller on this tree. T45 is the active retained-proposal route.
- T45 SOURCED: exactService_head_of_retained_proposal and its Regimes adapters
  now require the approved joined HEAD reader at voteTime s. joinedAt.1 supplies
  the exact awake tick. P10 ExactProposalAt and P11 ExactService supply this scope.
  Recovery can also use its explicit awake clause. WC/WCG must retain this guard.
- T40 SOURCED, still open: ExactService's gate reader must use confirmedReaderAtIdx
  at gateTime v, whose first projection is awake there. Recovery's awake clause
  supplies the same exact tick with the existing GST and horizon bounds.
- T42 SOURCED, still open: recovery uses its explicit awake clause. Clean/WC/WCG
  pass the actor's enabled gate at gateTime s; cutoff slotStartZ s and the awake
  gate tick give the earlyTime s actor tick. Pass this source through
  exactService_gate_receipts_of_head and exactService_gate_raw_of_head.
  confirmed gate-reader scopes also produce this enabled gate. No universal
  participation inference is permitted.
- internal statement, lead ruling 10-10, prepared: healing_held_block_receipt
  takes the receipt collision premise and the receiver's awake state at its
  deadline. An arbitrary honest sleeping receiver is outside the delivery bound.
  Its legacy NoRestart route derives the earlier exact awake interval from that
  state. Consumers: Healing/PostResetConeReceipts, SourceTiming and FrameRelay;
  Finality/TailMixed. Their public scoped sources still need verification.
- RetainedReflect and RetainedEndpoint slot bounds now use now ≤ tick. Their
  conclusions stay fixed. HeadAdmit's early receipt gets its horizon and awake
  interval from the existing early tick; T43 keeps the selected voter's hawake.
- Remaining work after S-Ap: compile these prepared files; apply and compile the
  executed Reads and SameLabel extraction patches; port R1–R3/R7, exact gate
  guards and epochs; thread the N4 service proof through Count, HeadAdmit and the
  retained-proposal route. Keep all 31 owned proof failures and nine test failures
  visible until each target passes. No approved public meaning change was made.
## S-Ap part 1 — public statement slice (2026-10-10)

## S-Ap Round 2 — review pin repair (2026-10-10)

Updated all 253 stale exact-hash pins to the current `docs/FGSA-API.md`.
The allow-name set and frozen baseline are unchanged. The frozen manifest
check passes (6.04 s). This closes review finding 1 before DECISION P23-A.

## S-Ap Round 2 — public fixture classification (2026-10-10)

Replaced the removed `Base₂.noRestart` field in Claims tests Regimes,
HealingW, and FinalitySafety with `restartsAtWakes`.
The fixture probe still fails: sleep-validity fields and the P2 delivery
contract need repair; FinalitySafety also needs `CleanSleep₂`.
Regimes and HealingW have horizon zero, so they do not prove useful read
inhabitation. Their replacement sleep generator belongs to P-Fx. The
FinalitySafety run and receipt-scope table witness belong to P-As.

- GREEN: 432 modules, lake build --wfail PASS (4.76 s final run).
- S-Ap DCK: PASS (151.89 s), 35 strict audits / 3,276 results and all 24 controls.
  Only propext, Classical.choice and Quot.sound appear.
- Complete export/coverage check: PASS (6.73 s), zero unaccepted exports.
  Tracked Claims coverage check: PASS (4.67 s), 813 command/owner rows.
- Layers: 72 accepted findings, zero new (0.61 s).
- Source checks: 113 selected Statements blocks match, 121 fixed blocks unchanged;
  new Lean lines at most 100; no sorry/admit/axiom; W3-owned files unchanged.
- EXPECTED-FAIL: 50 modules with explicit owners. The only new test handoff is
  OutageAlignment to P-Ou (unchanged equality examples; failure confirmed in 7.25 s).
- Manifest generation: 58-module slice 84.64 s; 59-module companion surface 104.32 s.
  No package-full or G-S3 claim is made; P23 and family work remain with their owners.

### P-ShA round 2 — guarded reads and compiled consumer ports

Base: da94c7c2, with the S-Ap part 1 slice at 7538ca0f. No Claims statement changed.
Base₂ stays with S-Ap. The receiptIdealization field is not in this tree yet.

- Reads.gateResult_eq_saved now equates the executed result in both join branches.
  The empty result is saved when the gate is disabled. gateResultAt_eq_gateResult
  keeps the same guard at the event index. SameLabel and Roots extract the raw
  branch only through Reads.fgsa_gate_raw_of_nonempty, which derives the raw branch
  and joined test from the executed saved result. It avoids exports of the home
  module's local Decidable matcher equations. No baseline is changed.
- N7: CatchUp.fgsa_gate_joined_of_enabled uses enabledGateAt at the exact gate tick.
  fgsa_enabledGate_noRestart supplies the same gate scope for legacy NoRestart callers.
  Gate.fgsa_gate_of_coveringBatch and fgsa_S_eq_of_exact require that enabled gate.
  Every OpeningSource gateService adapter passes it to fgsa_gate_clock_bridge.
  The source actor, event index, and gate label stay the same through each call.
- P23-A: Count.fgsa_active_path_of_coverage now calls fgsa_receiptCoverage_ready.
  Its added hAwake supplies the receiver's entire required-object service window.
  Its conclusion is unchanged. The old wrapper is no longer in Count's imports.
  Clean/StepGate, Clean/TransferFrame, WC/StepGateBatch, WC/StepTransferReceipts,
  and WCG/Dynamics must supply hAwake when they port their callers. Their owners
  already own the old ReceiptCoverage-to-ready migration. No sleep closure is claimed.
- Count's honest HEAD identity and awake facts now follow network or replay provenance.
  A replay is traced to the retained proposal's earlier delivery and carried signature;
  it is not called a fresh HEAD acceptance. No new NoRestart premise was added there.
- Compose.HealAC.tsMono uses ScopedMono at the event-prefix reader scope.
  HealAC.tExact takes confirmedReaderAtIdx at afterTicksIdx of the exact gate time.
  Healed.same_time uses confirmedReaderIdx for both readers at the same event index.
  OutputGrowthReads.fgsa_healed_output_mono takes that scope at both inclusive reads.
  These are the approved S-Ap scopes. Caller owners must retain them in their ports.
- ProposalRead and RowReads extract proposal content after the joined duty guard.
  RetainedConsumers passes the guarded proposal's payload projection to geometry.
  RetainedScores and its consumer families use NamedReceiptRootCollisionFree.
  The RetainedEndpoint test now keeps joinedAt at voteTime s and the receipt root form.
- ExactService passes enabled gates through Gate and OpeningSource; it returns the
  enabled event witness and gatePassedAt. The general gate reader uses the awake
  projection of confirmedReaderAtIdx at gateTime v (T40). Its retained NoRestart
  premise supplies the existing enabled gate. HeadTargetAtEmission's safety equality
  uses toNamedRootCollisionFree. Its public ExactService result keeps the joined HEAD
  and confirmed gate-reader scopes. This legacy route is compiled, not a new epoch port.
- SelfDelivery preserves restartsAtWakes through row append and prefix cut.
  Its current constructor still uses the old idealization field. After S-Ap part 2,
  it needs receiptIdealization and receipt-scope preservation through append and cut.
- Regimes.fgsa_clean_delivery_iff compares deadlines at every nonnegative ready anchor,
  not only at the send time. Prefix cuts pass their event-derived horizon bound.
  These source repairs compile up to the remaining regime adapter failures.

### P-ShA round 2 — exact remaining obligations

- HeadAdmit.fgsa_action_walk_batch still calls inclusion_head_receipt_early with
  hb.noRestart (line 406) and hb.receiptIdealization (line 404). The latter waits for
  S-Ap part 2. Base₂ permits restarts: the former needs the N4 service/epoch port,
  joined selected HEAD voters, and the receiver's exact early-read service scope.
  Awake at voteTime alone does not supply the joined duty guard.
- Shared.Export.fgsa_sameLabelClaim and fgsa_releaseClaim still request
  h.set.noRestart (lines 18, 37). Their core producers need the approved local epoch
  scopes from the restarted regime; restoring a global NoRestart field is invalid.
- Shared.Regimes has twelve open adapters: gate receipts, retained scores,
  suffix ghost transfer, proposal HEADs, retained HEADs, and exact service,
  each for clean and recovery. Their calls still request h.base.noRestart and
  h.base.receiptIdealization. The receipt field waits for S-Ap part 2. The other
  premise needs local receiver epochs, ready service, safe retained history, and N4.
  Keep T39/T45 joined HEAD scopes; pass T42's enabled source gate and T40's exact
  confirmed receiver scope. No blanket honesty-to-awake inference is authorized.
- Tests.RetainedConsumers is blocked by its import of Shared.Regimes. Its three
  production consumer imports compile. No test exception or baseline was added.
- The external ReceiptCoverage wrapper, FGSARun root, and Run.Tests.Axioms remain
  S-Ap-owned EXPECTED-FAIL. No P-ShA green target imports that wrapper now.
- No approved public statement was found false by this run. No new public STOP was
  asserted. N4's generic bridge is compiled, but threading it through restarted
  Count, HeadAdmit and retained proposal families is not closed.
All three modules are now EXPECTED-FAIL in S-Ap with those owners.
The FGSAInhabit witness modules and tests, OutageContinuationInhabit, and
RowPermission are also classified with P-Fx/P-As. Positive inhabitants for
HealthyPrefixSleep₂, CleanPrefixSleep₂, CleanSleep₂, RecoverySleep₂,
OutageSleep₂, OutageContinuationSleepPrem, and both continuation companions
remain OPEN until the owner evidence is available. A type audit is not an
inhabitation proof. No premise was weakened to make a fixture pass.

## S-Ap Round 2 — DECISION P23-A (2026-10-10)

- DECISION P23-A: retired `ReceiptCoverageStatement`,
  `ReceiptCoverageStatement_def`, and `fgsa_receiptCoverage`. Removed both
  theorem audit commands and their inventory rows. The old proof module is
  an import-only compatibility path to `ReceiptCoverageReady`.
- DECISION P23-A: installed the approved `ReceiptCoverageSleepPremises`,
  `ReceiptCoverageSleepStatement`, and its home equation. The statement and
  equation use `NamedReceiptRootCollisionFree`; neither has a per-required
  `NamedProposalInRun` premise. `ReceiptCoveragePremises` is unchanged.
- DECISION P23-A: `Base₂` has one `receiptIdealization` field.
  `Base₂.idealization` is now a theorem with the old safety result. Its local
  ancestor proof keeps Claims independent of proof-module imports.
- DECISION P23-A: all 17 full emission-supplier telescopes in each of WC
  and WCG use the receipt premise, from Init through SeededFramePath.
  This keeps the shared validity/delivery/receipt assumptions consistent
  across the intermediate supplier stages. Standalone LowFinalized and
  WCFinalityTargetEarlier interfaces retain the old root premise.
  Safety-only Claims text is unchanged. Clean/ExactProposal, HealingInput/
  HTime, GST availability and growth, and finality-liveness public premises
  obtain the stronger field through Base₂. Family owners must update proof
  caller arguments; those proof implementations are outside this edit.
- DECISION P23-A: docstrings state why a global premise over all values is
  false (root is a free field), and why the P2/DC difference is intentional.
- DECISION P23-A: ReceiptAlias keeps the exact retired contract under the
  test-only name `ReceiptAliasTests.legacyReceiptCoverageStatement`.
  Its kernel counterexample remains. No production code imports that test.
- DECISION P23-A: regenerated all 59 public manifest modules. Updated three
  existing pins (two retirements and Base₂.mk); all 919 existing allow pins
  match. No allow name or frozen/deep/frame/layer baseline changed.
- DECISION P23-A: added separate Run and proof-interface P23 axiom audits.
  The full Run audit has five inherited stale names and remains assigned to
  W2b-audit. This does not hide those failures in the package map.

### DECISION P23-A — fixture evidence and remaining owners

FinalitySafety now constructs receipt collision freedom from a kernel-checked
emission/store table. Its P2 delivery proof uses a handler before receipt and
processed history after receipt. The concrete run has horizon 17, a non-genesis
proposal, an enabled proposal gate before the horizon, and an audited confirmed
reader at time 11. It constructs HealthyPrefixSleep₂, CleanPrefixSleep₂,
CleanSleep₂, and RecoverySleep₂, with joined recurrence. It is GREEN.

Regimes and HealingW now compile with the receipt field, sleep validity, P2
anchors, and sleep regime constructors. Their horizon-zero evidence remains
insufficient for useful-read validation, so their package classification stays
EXPECTED-FAIL/P-Fx until the sleep generator replaces it. This classification
records missing validation, even though the current modules compile.

OutageSleep₂ and OutageContinuationSleepPrem need the P-Fx sleep generator;
OutageContinuationInhabit is EXPECTED-FAIL/P-Fx. The two continuation companions
need the W1 witness and remain OPEN/P-As through the FGSAInhabit modules.
RowPermission remains EXPECTED-FAIL/P-As. No public premise was weakened.

### DECISION P23-A — final validation

S-Ap DCK PASS in 169.90 s: 440 GREEN modules, 39 strict audits,
3,342 axiom results, and all 24 controls. Only propext, Classical.choice,
and Quot.sound occur. The separate GREEN build passed in 26.91 s.
The standard frozen manifest check passed in 24.01 s; all 919 pins match.
Complete Claims, Run P23, WC, and WCG export checks have zero unaccepted
exports. check-layers reports 72 accepted findings and zero new (0.32 s).
The three changed fixtures build with --wfail (18.10 s); strict smoke audits
also pass, without claiming useful reads from their horizon-zero runs.
Default heartbeats, no proof placeholders, no baseline changes.

The full supplier telescope changes cover these suffixes under both WC and
WCG, each ending in Statement: Init, StepDelivery, StepNoGateTick, StepGateTick,
StepRestart, Step, SeededInduction, Service4, SeededFrame, FinalBelow,
ProposalPivot, ProposalAdmission, ExactProposal, Inclusion6, Retrospective,
SeededFrameLive, and SeededFramePath.


## P-ShA round 3 — local receiver receipt APIs, with open targets

Base: 46a95cad (S-Ap parts 1 and 2; P-Fx). P-ShA is not closed.
The Base₂ receipt field now exists. No FGSAClaims statement or S-Ap proof was edited.

- Shared/SelfDelivery: Base₂.snoc_ownRow and Base₂.cutAt preserve the single
  receiptIdealization field. Delivered and held scope use the existing named-scope
  restrictions. Honest emitted scope uses emits_snoc_deliver_iff and emits_cut_iff.
- Shared/Release: fgsa_release_bound_restart uses the network signature source of
  an accepted or replayed HEAD. Replay obtains the earlier carried delivery from
  fgsa_replayed_head_delivery_origin. No receipt deadline or NoRestart is needed.
  The legacy API remains as a wrapper. Shared/Export's ReleaseClaim uses this core.
- Shared/CatchUp: fgsa_historySafeAt_of_emitted_head supplies safe history for the
  exact fresh emitted HEAD at its action cut. fgsa_head_receipt_on threads the
  exact ReadyTrigger, HistorySafeAt and restartFree from actionCut a to idxBefore
  freeze through N4. It returns current processing at the deadline and freeze.
- Shared/GateReceipt: fgsa_gateReceipt_stamps_on preserves vote and block stamps
  under restartFree rho x j i. The legacy wrapper derives that local interval.
- Tests/RestartEpochs: two kernel checks use local copies of the existing valid
  SleepTests fixtures. A bare HEAD processed before sleep need not be processed
  after restart; an awake HEAD tick need not pass joinedNow. The original full
  validity proofs remain in Run/Tests/Sleep, with no cross-test import added.

STOP: fgsa_action_walk_batch still concludes a WalkBatch over all honest selected
HEAD seats from hawake alone. Let the single honest validator wake and restart at
voteTime s, with horizon earlyTime s and no retained proposal or received HEAD.
Choose s = q * R + 1, Q = genesis, and the initial finalized floor. The two public
awake ticks exist, Base₂ and LabelSyncOn hold, and the batch count exceeds zero.
The HEAD duty is suppressed by joinedNow; the HEAD pool is empty. The WalkBatch
membership conclusion is false. This target needs joined selected voters and the
receiver's exact service scope. No changed public statement was installed.

STOP: fgsa_gateReceipt_clean and fgsa_gateReceipt_recovery quantify awake selected
HEAD voters and conclude their actual HEAD emission. A selected voter waking at
voteTime s has joinedNow = false and emits no HEAD. For Clean, keep other honest
validators awake so the strict prefix participation bound holds. For Recovery,
choose GST = voteTime s and wake the selected voter at GST; keep it awake thereafter.
Take genesis floors and covered prefix so the geometry implications hold. Delivery
cannot supply a nonexistent emission. Both adapters need the joined voter scope.

No false conclusion was established for the other ten Regimes adapters or for
SameLabelClaim. Their local receiver epoch and service ports remain unfinished.
Their current calls still request the removed Base₂.noRestart field. Do not infer
safe history for arbitrary retained HEADs: the tested valid ownRun fixture processes
ownHead at state index 12, but loses it at the restart action cut at time 35.
The exact retained service/history obligations must be discharged, not assumed.
Tests.RetainedConsumers still waits for a compiled Regimes module; its local
Composes statement also retains the old unguarded honest-reader quantifiers.

S-Ap input status: the retired ReceiptCoverage import path compiles in this merge.
Run.Tests.Axioms fails on fgsa_restore_now_retained, fgsa_hrestore_now_retained,
restore_st_retained, spec_prune_restart_mem and spec_prune_sleep. Run's facade
imports that audit. P23Axioms compiles. No S-Ap file was edited. The ReceiptCoverage
EXPECTED-FAIL map entry remains under S-Ap ownership after automatic review rejected
its proposed status change. The P-ShA map adds the required merged P23 audit input.

Validation and exact source locations are in claude-files/sleep-psha-report.md,
Round 3. Only compiled green modules are covered by the successful checks.

## P-H1 — internal helper repairs (2026-10-10)

Base: 1c777e973b07b6824debbe8e775401dabc6feb08, branch sleep-ph1.
The writer brief assigns FrameRelay and the other depth 0–12 Healing proof
modules to P-H1. FGSAClaims statements remain with S-Ap and are unchanged.
The job explicitly permits an internal statement that is false under sleep to
be replaced by its exact true form, with this ledger row. Lean `public` visibility
of a proof helper does not make it an approved FGSAClaims public statement.

- FrameSource/FrameZero: restart keeps the block store and clears fast writes.
  The induction uses the predecessor invariant, not an initial-store invariant.
  A fresh gate appends an empty fast row when its join guard is false.
- SupportSaved: gateStep_other preserves each other saved label in both branches.
- SupportWrite: healing_support_fastWrite needs the exact joinedAtTime guard at
  the gate. healing_support_phaseBody_of_write derives it from its executed
  nonempty gate result. A same-time wake can suppress an otherwise nonempty raw
  fast set, so the old unconditional equality is false (GF).
- SupportTicks: healing_support_vote_tick needs awake at its exact node and vote
  time. healing_support_honest_emits also needs joinedNow at that tick. A wake
  at the vote tick supplies awake but suppresses the HEAD duty (T23/JOINED-VOTER).
  The declarations move from SupportHeads into an independent owned helper.
- SupportRelease: healing_support_release_rows needs joinedAtTime at the release.
  The old strict count is false when a wake suppresses release. The declaration
  moves from SupportTransfer into an independent owned helper (RR).
- SupportRelay: healing_support_gate_late needs the gate epoch/join guard for
  strict stamps. Receipt suppliers use NamedReceiptRootCollisionFree (P23-A).
  Retained receipt paths keep explicit NoRestart; no retained history is inferred
  from earlier processing. No family sleep receipt closure is claimed.
- FrameRelay, proposed exact internal form: receiver awake at the receipt
  deadline guards healing_witness_relay and healing_witness_relay_phase.
  Counterexample to the old form: an honest receiver stays asleep throughout a
  no-restart prefix while a different honest source holds a non-genesis witness.
  Its initial finality is below the witness, but no delivery to that receiver is
  required. The unchanged source and frame premises cannot give receipt.
  Consumers: SupportFrame.healing_witness_relay_settled and
  SupportFrame.healing_head_witness_relay supply recovery awake at that deadline.
  No FGSAClaims statement or approved public meaning changes. This internal
  correction is within the job's explicit replacement rule; it is not a new
  premise on the approved public recovery claim.

### P-H1 prepared audit and exact forms

- PhaseRelay and SupportFrame: retained receipt consumers keep receiver awake at
  the exact deadline. The second evidence-spread arm derives earlier awake from
  its actual later receiver tick only with valid execution and explicit NoRestart.
- DescentTiming.healing_delivery_clock: valid execution supplies the public-action
  clock bound with exact wake-time restore. Mere ScheduleWellFormed does not
  require sleeping ticks to execute. The callers already provide valid execution.
- Tests/HealingDescentTiming: the restart at time 7 has clock 7, not the earlier
  action time 6. The fixture retains its event list and schedule/non-NoRestart checks.
- Time: the recovery-start horizon is used by HTimeStatement. Its composition
  retains the old stronger producer statements and proves GST ≤ recoveryStart.
  The proof has no exported generated equation and changes no FGSAClaims text.
- Strict prepared audit: 62 exported theorems from 14 owned core modules.
  Complete export check: 147 proof modules, 252 exports, 0 unaccepted.
  Global inventory and facade edits are serial lead work. The owned fragment is
  scripts/dev-pkg/P-H1.coverage-fragment.txt, under the existing full audit key.

### P-H1 PREPARED on sleep-ph1 (2026-10-10)

The prepared map has 98 targets: 75 assigned proof modules, 20 assigned tests,
two independent helpers, and one local strict audit. Its S1 REQUIRED union TARGETS
classification has 494 GREEN and 72 EXPECTED-FAIL entries. Later targets retain
P-H1 ownership; inherited REQUIRED failures retain P-ShA or S-Ap ownership.

- Final GREEN lake build --wfail: PASS, 5.03 s.
- DCK PASS (package P-H1), default controls: 433.59 s; 24 controls passed.
- Strict audits: 39 roots, 2,859 results; only the three permitted axioms.
- Complete prepared exports and coverage: 147 proof modules, 252 exports,
  0 unaccepted; 8.93 s. Local Healing audit: 62 results.
- Layers: 72 findings, 0 new; 0.35 s. git diff --check: PASS.

This status covers the checked prepared set on this branch. It does not assert
integration, review, family closure, or a full gate. P-ShA round 4, S-Ap roots,
P-Fd lease/service inputs, P-Fi MiddleSupport, later H1 epoch ports, and the lead's
serial audit integration remain open. No requested external or public-claim edit
was made. No protocol declaration, default heartbeat, checker, baseline, or
allowance changed. Evidence is under .lake/sleep-ph1/.

### P-H1 — prepared consumer extension (2026-10-10)

- PromotionCarrier.healing_promotion_slot_proposal needs the exact proposer
  restart/join bound. Awake alone is false: a proposer can wake at its proposal
  tick and have its duty suppressed. No proposal exists to carry its rows.
  The internal gap producer now takes RecoverySleep₂; it derives the selected
  proposer's join bound from suffixNoRestart and the existing lower proposal bound.
- FrontierSearchAge.frontierSearch_age_service uses the same approved sleep
  companion. Its carrier lower bound places the previous slot start after GST.
  It derives the exact join bound without a global NoRestart premise.
- LiveDC.healing_liveDCFromWindows proves the existing approved statement.
  It selects through joinedGap, restricts stable comparisons to confirmedReader,
  and preserves finality and strict-before acceptance through durable restore.
  It does not construct a new RMonoAll companion or change a public claim.
- PhaseRelay, SupportFrame, PromotionCarrier, PromotionRows, LiveDC, and
  FrontierSearchAge passed --wfail and move from P-H1 EXPECTED-FAIL to GREEN.
- Eight existing named awake witnesses are threaded through owned T23 callers.
  These later modules remain EXPECTED-FAIL. Joined duty and receiver epoch ports
  still need the P-ShA round 4 interfaces and the P-Fd producers.
- The expanded local strict audit has 81 commands. The serial integration
  fragment stays under the existing full audit key. No key or allowance is added.

### P-H1 final prepared extension — validation (2026-10-10)

Status: PREPARED on sleep-ph1; not CLOSED. The map still has all 98 TARGETS.
The final classification has 500 GREEN and 66 EXPECTED-FAIL entries: 38 assigned
GREEN targets, 60 assigned P-H1 targets still open, and 6 REQUIRED supplier failures
(counts corrected by the lead from the map, rev-ph1-astra finding 2).
No REQUIRED entry moved to DEFERRED or to a different repair owner.
H2 handoff: the complete caller checklist is rev-ph1-astra findings 1 and 6
(/Users/francesco/.claude/jobs/22f59f85/tmp/tmp/rev-ph1/review.md): held receipt, promotion
slot proposal restart bound, 19 healing_support_vote_tick calls, and the other changed interfaces.

- Final GREEN lake build --wfail: PASS, 2.49 s.
- Final DCK PASS (package P-H1): 179.93 s; all 24 default controls passed.
- Strict audits: 39 roots, 2,878 results; only the three permitted axioms.
- Expanded local strict audit and complete coverage: 81 declarations.
- Complete exports: 160 proof modules, 252 exports, 0 unaccepted; 7.30 s.
- Layers: 72 findings, 0 new; 0.60 s. git diff --check: PASS.

Closure still needs the P-ShA round 4 interfaces, S-Ap roots, P-Fd companion
producers, P-Fi MiddleSupport, remaining H1 epoch/caller ports, and serial audit
integration. The report lists each GREEN and EXPECTED-FAIL target, the changed
files and declarations, all internal replacements, and the exact caller audit.
The optional SupportRecovery module is not present: automatic approval review
rejected it as outside the prepared scope, and the text approval request is pending.
No FGSAClaims statement, protocol declaration, checker, baseline, allowance, or
heartbeat changed. Report: claude-files/sleep-ph1-report.md.
## P-Fd — durable and epoch Foundations suppliers (2026-10-10)

Base: 1c777e97, with sleep-int 8c838f3b and P-ShA rounds 1–3.
Only P-Fd proof, test, map, and ledger files are changed. S-Ap retains
Claims/Foundations.lean until its serial transfer. Public meaning STOP: none.

- RStoreDurable: fgsa_rStoreDurable uses Shared.fgsa_store_durable for TF,
  blocks, proposal wires, and signed rows across all restarts.
- RStoreEpoch: fgsa_rStoreEpoch uses fgsa_store_cumulative_on on the exact
  restartFree rho x i j interval for block and vote stamp prefixes.
- RMonoAll: fgsa_rMonoAll keeps F, (h_j, J), and h_max through acRestart_fg.
  RMono stays as the legacy NoRestart wrapper.
- RFrameNextEpoch: fgsa_rFrameNextEpoch keeps the existing local frame equations,
  uses durable proposal/row prefixes, and scopes stamp prefixes to the local epoch.
- Finalized monotonicity: the P21 restart companion uses the W3 kept-F restart law.
  FinalizedSafety uses RMonoAll and keeps the public conclusion.
- Lease K/S uses: retained obligations keep their actual gate source and deadlines;
  restart fast pairs are empty by acRestart_fastWrite. No empty-lock assumption
  remains. The target bound and ancestor deadlines survive retained-store replay.
- K origins in Accountable, Carrier, and Sources retain origin and bound projections.
  Emitted carriage/source proofs split the joined duty guard; no premise is added.
- RowPermission: lock carriers use durable TF membership. The actual RecoverySleep₂
  suffix supplies confirmedReaderAtIdx at an exact gate after its join cutoff;
  OpeningCovered and OpeningCoveredLower consume that evidence.
- Tests.RowPermission: the one-validator tick fixture supplies SleepWellFormed,
  RestartsAtWakes, and NamedReceiptRootCollisionFree. Its receipt scope has only
  genesis: there is no delivered proposal and no emitted object.

Internal statement replacement: fgsa_leaseOrigins_lastWrite now restricts the later
key exclusion to a joined pre-gate state. At an unjoined gate the retained view can
have raw confirmationFrom and gateWriteKeys, but the executed gate writes no lease.
The old raw-key exclusion does not follow. The source, deadline, chain, fast-write,
and ancestor conclusions are kept. Consumers: Healing SupportWrite/PostReset/Frontier/
RiseOne, Assembly Healing/ResetArrival, their tests, and NonVacuity.HealingRun.
They must pass the joined guard when they reason about the later executed gate.

Internal statement replacement: fgsa_rowService_receipt and T-ROWS producers use
P8's all-honest awake suffix. A permanent sleeper satisfies the old NoRestart and
vacuous P2 demand, but has no row at the deadline. Pre-GST sends use max(send, GST).
fgsa_rowsReceipt_carriage has the same conclusion and no NoRestart requirement;
it uses durable row and proposal prefixes.

The package-local FoundationsAxioms root checks all changed public theorem bodies.
The complete audit inventory and canonical-root registration are handed to the lead
as a fragment; no new canonical coverage key or allowance is installed.
Preparation validation and status are recorded below after the checks finish.

P-Fd PREPARED: DCK PASS on 490 GREEN modules and 7 EXPECTED-FAIL modules
(174.82 s), with 38 strict audit roots and the default controls PASS.
The local root has 108 audit commands. Complete exports and complete local
coverage: 147 proof modules, 251 exports, 0 unaccepted (6.23 s).
Layers: 72 baseline findings, 0 new (0.38 s). No allowance or baseline changed.
CLOSED still waits for the S-Ap Claims/Foundations transfer and P-ShA round 4.
The remaining owned RowService restart adapter is continued after this checkpoint.

### P-Fd — restart-safe row service follow-up

fgsa_rowService_receipt_sleep, fgsa_tRowsReceipt_sleep, fgsa_tRowsSync_sleep,
and fgsa_tRows_sleep use the exact receiver epoch from actionCut(max(send, GST))
to idxBefore(deadline). A restart at the anchor is already in the action cut.
Safe row history follows from durable rowPool prefixes, not from a claim about
retained HEAD processing. The valid run's exact wake clock proves row timeliness.
The prepared NoRestart interfaces remain wrappers with the approved awake suffix.

rowService_epoch_of_recovery derives the post-GST epoch from Recovery₂.awake
and Base₂.restartsAtWakes. Thus fgsa_tRows_recovery proves all three row clauses
from Recovery₂, with no global NoRestart assumption. RecoverySleep₂ can use it
through toRecovery₂.

The unchanged Foundations.Export target has three remaining ports: the
FGFoundationNext companion tuple, the approved P8 awake suffix, and the
RowServiceClaim call to fgsa_tRows_recovery. Four serial export fragments,
including the P21 public restart companion and the exact P8 predicate, compile
in isolation with strict permitted axioms (12.64 s). They are handed to the lead;
Claims/Foundations remains S-Ap-owned. No public meaning change is requested.
Final package validation is recorded below after the DCK finishes.

P-Fd follow-up validation: DCK PASS, 490 GREEN / 7 EXPECTED-FAIL, 38 strict
roots, 114 local audit commands, all default controls PASS (168.53 s).
Complete exports and complete local coverage: 147 proof modules, 251 exports,
0 unaccepted (5.19 s). Layers: 72 baseline findings, 0 new (0.46 s).
The package remains PREPARED. CLOSED requires the S-Ap claim transfer and
P-ShA closure. Archived P-ShA round 4 (8384eb34) is NOT CLOSED: Shared.Export,
Shared.Regimes and Tests.RetainedConsumers remain open. That supplier commit
is not installed here; this branch keeps its base classifications and interfaces.

### P-H2 — sleep wave 3 prepared scope

Base: sleep-ph2 at 60cdcf652308640f3fadc39360e2b2042879f633.
P-H1 and P-Fd are PREPARED inputs. P-H2 is PREPARED; CLOSED stays open.

Internal T17 replacement: opening_action_tick requires awake at the exact opening.
An honest node that stays asleep has no tick there. Recovery supplies awake from
GST through the exact horizon. OpeningTicks holds the scheduled-run helper;
OpeningServiceOne and FrontierOpen pass their existing time bounds.

GF consumers: a nonempty scheduled fast write proves the exact gate join guard.
OpeningGateRead uses freshness, the unjoined empty row, and fast-label uniqueness.
It derives enabledGateAt before constructing GateService. An executed nonempty
result supplies its raw branch through fgsa_gate_raw_of_nonempty. The direct W3
clockPre gate-view bridge keeps its type. The slot bound uses non-strict pre-tick
clock order; it does not need a join premise merely to compare slots.

RR consumer: PostResetRawStep needs expiry membership only. ReleaseScope proves
that membership in both join branches. It does not infer a strict release count
from an unjoined clock. Strict release consumers still need their exact guard.

T23: all 19 H2 calls now pass awake at the exact node and vote. T15, T16, T18,
T19 and T22 also pass their exact recovery awake witnesses. These blocked high-depth
files remain EXPECTED-FAIL; source edits alone do not close their proofs.

H1 handoff: the held-receipt caller passes deadline awake and receipt idealization.
The three slot-proposal callers derive the exact proposer restart cutoff from
RecoverySleep₂.suffixNoRestart and their lower proposal bounds. RiseOneRise also
uses RecoverySleep₂. Named receipt callers use receiptIdealization where required.
Legacy NoRestart receipt and transfer suppliers remain explicit open inputs.

RecoveryScope consumes RStoreDurable, RMonoAll and RStoreEpoch as supplied channels.
Its proofs use exact event indices from actionCut to idxBefore for the receiver
stamp epoch. A restart at GST is permitted. No global NoRestart is inferred.
The direct Foundations.Store import was removed to keep the Healing layer valid.
P-Fd supplies the concrete producers through the package assembly interface.

Prepared validation: 85 TARGETS; 468 GREEN; 85 EXPECTED-FAIL. The target split is
6 GREEN and 79 open. Six REQUIRED supplier failures retain P-ShA/S-Ap ownership.
DCK PASS: 37 strict roots, 2,812 results, all 24 controls PASS.
Complete compiled exports: 111 proof modules, 251 exports, 0 unaccepted.
Layers: 72 baseline findings, 0 new. No public statement, protocol declaration,
checker, baseline, or allowance changed. The canonical audit fragment is in
scripts/dev-pkg/P-H2.coverage-fragment.txt for serial integration at close.
