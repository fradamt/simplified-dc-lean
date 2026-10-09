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
or extra theorem premise is proposed. The proof and fixture edits are not yet checked.

P3 is blocked: both approved `World.step` branches use `.restart v _` and then
refer to the unbound `t`. The plan uses `.restart v t`. The branch edit is stopped
pending approval of that correction. The old branch remains in both Run files.

File keys (all relative to the repository):
- Lift: `AvailableChainEngineV2/Conditions/Duty/Lift.lean`.
- Self: `AvailableChainEngineV2/Laws/SelfDelivery.lean`.
- DSelf: `AvailableChainEngineV2/Laws/Duty/SelfDelivery.lean`.
- Run/DRun: `AvailableChainEngineV2/Engine/{Run,Duty/Run}.lean`.
- Schedule/DSchedule: `AvailableChainEngineV2/Conditions/{Schedule,Duty/Schedule}.lean`.
- Delivery/DDelivery: `AvailableChainEngineV2/Conditions/{Delivery,Duty/Delivery}.lean`.
- Clock/DClock: `AvailableChainKitV2/{ClockLaws,DutyClockLaws}.lean`.

`approved; unbuilt` records text approval only. It does not close W1a.
The Lift theorem names below have the prefix `AvailableChain.V2.D.`.

```text
┌────────────────────────────────────────────┬────────────┬───────────┬────────────────────┐
│ Declaration                                │ File       │ Packet    │ Status             │
├────────────────────────────────────────────┼────────────┼───────────┼────────────────────┤
│ sleepWellFormed_toD_iff                    │ Lift       │ P1(a)     │ approved; unbuilt  │
│ restartsAtWakes_toD_iff                    │ Lift       │ P1        │ approved; unbuilt  │
│ noRestartOn_toD_iff                        │ Lift       │ P1        │ approved; unbuilt  │
│ noRestartAfter_toD_iff                     │ Lift       │ P1        │ approved; unbuilt  │
│ linkReadyOn_toD_iff                        │ Lift       │ P1, P2    │ approved; unbuilt  │
│ processedByActionCut_toD_iff               │ Lift       │ P1, P2    │ approved; unbuilt  │
│ handledBetween_toD_iff                     │ Lift       │ P2        │ approved; unbuilt  │
│ deliveryService_toD_iff                    │ Lift       │ P2        │ approved; unbuilt  │
│ deliveryDemand_toD_iff                     │ Lift       │ P2        │ approved; unbuilt  │
│ scheduleWellFormed_toD_iff                 │ Lift       │ P1(a)     │ approved; unbuilt  │
│ partialSynchrony_toD_iff                   │ Lift       │ P2        │ approved; unbuilt  │
│ healthyPrefixDelivery_toD_iff              │ Lift       │ P2        │ approved; unbuilt  │
│ executionValid_toD_iff                     │ Lift       │ P1(a)     │ approved; unbuilt  │
│ ExecutionValid.snoc_selfDelivery           │ Self       │ P1(a)     │ approved; unbuilt  │
│ ExecutionValid.snoc_selfDelivery           │ DSelf      │ P1(a)     │ approved; unbuilt  │
│ ExecutionValid (sleep parent)              │ Schedule   │ P1(a)     │ approved; unbuilt  │
│ ExecutionValid (sleep parent)              │ DSchedule  │ P1(a)     │ approved; unbuilt  │
│ PartialSynchrony / HealthyPrefixDelivery   │ Delivery   │ P2        │ approved; unbuilt  │
│ PartialSynchrony / HealthyPrefixDelivery   │ DDelivery  │ P2        │ approved; unbuilt  │
│ World.step restart                         │ Run        │ P3        │ blocked: binder    │
│ World.step restart                         │ DRun       │ P3        │ blocked: binder    │
│ RestoreTimeLaw                             │ Clock      │ P3        │ approved; unbuilt  │
│ RestoreTimeLaw                             │ DClock     │ P3        │ approved; unbuilt  │
└────────────────────────────────────────────┴────────────┴───────────┴────────────────────┘
```
