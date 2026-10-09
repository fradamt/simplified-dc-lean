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
