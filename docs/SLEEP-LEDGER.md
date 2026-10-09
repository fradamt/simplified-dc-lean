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
