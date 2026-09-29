# V2 API manifest

_Frozen at the Phase 2a gate (plan `docs/plans/2026-09-29-phase2a-engine-v2-core.md`,
Task 7), 2026-09-29._

This file lists the frozen v2 API: every public declaration of engine v2
(`AvailableChainEngineV2`: `Engine`, `Conditions` and `Laws`) and of
Kit v2 (`AvailableChainKitV2`, without `Tests`), by fully qualified name
and grouped by module.

## Freeze rule

After the gate, no declaration in this file changes its name, type or body
(DC N6). A 2a structure never gains a field, a 2a inductive never gains a
constructor, and a 2a definition never gains a parameter. Later stages (2b,
2c) only ADD declarations or separate structures.

- **Engine v2 entries are locked.** The value of
  `AvailableChain.Framework.V2.anchor` (`AvailableChainFramework/V2/Anchor.lean`)
  references each engine entry. `scripts/CatalogLock.lean` locks the module
  prefix `AvailableChainFramework.V2`, so the lock line of the anchor hashes
  the closure of every engine entry. A change to an engine entry gives a
  `CHANGED` line. As everywhere in the lock, a theorem contributes its
  statement only: a new proof keeps the hash. A change to a model module in
  the closure (for example `AvailableChainModel.Objects.Time`) also changes
  the anchor line.
- **Kit v2 entries are frozen by rule, not locked.** The Kit is L5, and the
  Framework does not import it. No tool finds a change to a Kit entry; a
  review must find it.

## Scope

An entry is a declaration of a scope module that Lean did not generate, by
the rule of `scripts/CatalogLock.lean` (`generated`). Thus the list
includes structure constructors and fields (projections) and derived
instances, and excludes recursors, `casesOn`, `noConfusion`, matchers,
equation lemmas, `injEq`, `sizeOf_spec` and private declarations.

- Scope modules: `AvailableChainEngineV2.Engine.*`,
  `AvailableChainEngineV2.Conditions.*`, `AvailableChainEngineV2.Laws.*`,
  and every module `AvailableChainKitV2.*` outside `AvailableChainKitV2.Tests`.
- Not in scope: `AvailableChainEngineV2.Tests.*` and
  `AvailableChainKitV2.Tests.*` (tests, the counterexamples of namespace
  `AvailableChain.V2.Engine.Counterexamples`, and the toy run); the library
  roots (imports only); `AvailableChainEngineV2.Sketch` (namespace
  `AvailableChain.Framework.V2Sketch`, the pre-2a prototype that plan 2a
  keeps; it is not the v2 API).
- Rulings: the Task 5 helpers (`propSeat`, `eq_propSeat`,
  `holder_propLabel`, `Output`, the `OutputsFactor` lemmas) are listed
  and frozen; `Interface.propLabel_injective` is a frozen field; the run
  checks of `AvailableChainKitV2.RunCheck` (`allTicks`, `allDeliveries`,
  `emittedBy` and their `_spec` lemmas) are Kit entries. Every Kit entry is
  frozen; no group is "helpers, not frozen".

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --list` prints the module
  blocks below from the environment, in source order.
- `lake env lean --run scripts/V2Manifest.lean --anchor` prints the body of
  the anchor.
- `lake env lean --run scripts/V2Manifest.lean --check` exits 1 if the anchor
  is missing, if an entry does not exist or is not in the module of its
  heading, if an engine entry is not in the closure of the anchor, if a public
  declaration of a scope module is not listed, or if a scope module has no
  heading.

Each block line is `<kind> <name>`. The kinds are `structure`,
`inductive`, `ctor`, `def` (fields that are data included) and
`theorem` (fields that are proofs included).

## Counts

```text
┌──────────────────────────────────────────────┬─────────┬────────────────────┐
│ Module                                       │ Entries │ Status             │
├──────────────────────────────────────────────┼─────────┼────────────────────┤
│ AvailableChainEngineV2.Engine.Objects        │      15 │ locked (anchor)    │
│ AvailableChainEngineV2.Engine.Run            │      42 │ locked (anchor)    │
│ AvailableChainEngineV2.Engine.Spec           │      28 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Committees │      10 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Delivery   │       8 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Interface  │      19 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Schedule   │      33 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.Hooks            │      16 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.Isolation        │      26 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.Outputs          │      10 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.SelfDelivery     │      17 │ locked (anchor)    │
│ AvailableChainKitV2.ClockLaws                │       9 │ frozen, not locked │
│ AvailableChainKitV2.Emission                 │      10 │ frozen, not locked │
│ AvailableChainKitV2.EngineClock              │      16 │ frozen, not locked │
│ AvailableChainKitV2.Execution                │      10 │ frozen, not locked │
│ AvailableChainKitV2.RunCheck                 │       6 │ frozen, not locked │
│ AvailableChainKitV2.Stable                   │       5 │ frozen, not locked │
├──────────────────────────────────────────────┼─────────┼────────────────────┤
│ Engine v2 total                              │     224 │ locked (anchor)    │
│ Kit v2 total                                 │      56 │ frozen, not locked │
│ Total                                        │     280 │                    │
└──────────────────────────────────────────────┴─────────┴────────────────────┘
```

## Engine v2 (locked through the anchor)

### `AvailableChainEngineV2.Engine.Objects`

```text
inductive AvailableChain.V2.Auth
ctor AvailableChain.V2.Auth.seat
ctor AvailableChain.V2.Auth.none
def AvailableChain.V2.instDecidableEqAuth
def AvailableChain.V2.instDecidableEqAuth.decEq
def AvailableChain.V2.instReprAuth
def AvailableChain.V2.instReprAuth.repr
structure AvailableChain.V2.Signed
ctor AvailableChain.V2.Signed.mk
def AvailableChain.V2.Signed.auth
def AvailableChain.V2.Signed.payload
def AvailableChain.V2.instDecidableEqSigned
def AvailableChain.V2.instDecidableEqSigned.decEq
def AvailableChain.V2.instReprSigned
def AvailableChain.V2.instReprSigned.repr
```

### `AvailableChainEngineV2.Engine.Run`

```text
inductive AvailableChain.V2.Event
ctor AvailableChain.V2.Event.restart
ctor AvailableChain.V2.Event.tick
ctor AvailableChain.V2.Event.deliver
def AvailableChain.V2.instDecidableEqEvent
def AvailableChain.V2.instDecidableEqEvent.decEq
def AvailableChain.V2.Event.time
def AvailableChain.V2.Event.node
def AvailableChain.V2.Event.object?
def AvailableChain.V2.Event.phase
def AvailableChain.V2.Event.key
def AvailableChain.V2.World
def AvailableChain.V2.World.init
structure AvailableChain.V2.Run
ctor AvailableChain.V2.Run.mk
def AvailableChain.V2.Run.honest
def AvailableChain.V2.Run.horizon
def AvailableChain.V2.Run.events
def AvailableChain.V2.Run.seatOf
def AvailableChain.V2.Run.input
def AvailableChain.V2.Run.ownSeats
def AvailableChain.V2.tick
def AvailableChain.V2.World.step
def AvailableChain.V2.Run.stateBefore
def AvailableChain.V2.Run.stateBeforeTime
def AvailableChain.V2.Run.readAt
def AvailableChain.V2.Run.final
def AvailableChain.V2.Run.emitsAt
def AvailableChain.V2.Run.tickIdx?
def AvailableChain.V2.Run.emittedAt
def AvailableChain.V2.Run.emits
def AvailableChain.V2.Run.processes
def AvailableChain.V2.Run.handlesAt
def AvailableChain.V2.Run.acceptsAt
def AvailableChain.V2.Run.holder
theorem AvailableChain.V2.Run.stateBefore_succ
theorem AvailableChain.V2.Run.step_tick_eq
theorem AvailableChain.V2.tick_decomp
theorem AvailableChain.V2.tick_asleep
theorem AvailableChain.V2.Run.tickIdx?_spec
theorem AvailableChain.V2.Run.emittedAt_eq_emitsAt
theorem AvailableChain.V2.Run.mem_emittedAt_iff_emits
```

### `AvailableChainEngineV2.Engine.Spec`

```text
structure AvailableChain.V2.ProtocolSpec
ctor AvailableChain.V2.ProtocolSpec.mk
def AvailableChain.V2.ProtocolSpec.State
def AvailableChain.V2.ProtocolSpec.Label
def AvailableChain.V2.ProtocolSpec.seats
def AvailableChain.V2.ProtocolSpec.Payload
def AvailableChain.V2.ProtocolSpec.Durable
def AvailableChain.V2.ProtocolSpec.init
def AvailableChain.V2.ProtocolSpec.clock
def AvailableChain.V2.ProtocolSpec.actTime
def AvailableChain.V2.ProtocolSpec.duties
theorem AvailableChain.V2.ProtocolSpec.duties_spec
theorem AvailableChain.V2.ProtocolSpec.duties_nodup
def AvailableChain.V2.ProtocolSpec.act
def AvailableChain.V2.ProtocolSpec.gossip
def AvailableChain.V2.ProtocolSpec.process
def AvailableChain.V2.ProtocolSpec.selfVisible
def AvailableChain.V2.ProtocolSpec.recordOwn
def AvailableChain.V2.ProtocolSpec.durable
def AvailableChain.V2.ProtocolSpec.restore
def AvailableChain.V2.ProtocolSpec.wellFormed
def AvailableChain.V2.ProtocolSpec.depsPresent
def AvailableChain.V2.ProtocolSpec.processed
def AvailableChain.V2.ProtocolSpec.excludes
def AvailableChain.V2.ProtocolSpec.handles
def AvailableChain.V2.ProtocolSpec.carries
def AvailableChain.V2.ProtocolSpec.Object
def AvailableChain.V2.ProtocolSpec.objSelfVisible
```

### `AvailableChainEngineV2.Conditions.Committees`

```text
structure AvailableChain.V2.LabelFamilies
ctor AvailableChain.V2.LabelFamilies.mk
def AvailableChain.V2.LabelFamilies.ap
def AvailableChain.V2.LabelFamilies.fresh
def AvailableChain.V2.LabelFamilies.linked
def AvailableChain.V2.CStar
def AvailableChain.V2.Linked
def AvailableChain.V2.SingleSeat
theorem AvailableChain.V2.Linked.toCStar
theorem AvailableChain.V2.CStar.seats_eq
```

### `AvailableChainEngineV2.Conditions.Delivery`

```text
structure AvailableChain.V2.PartialSynchrony
ctor AvailableChain.V2.PartialSynchrony.mk
theorem AvailableChain.V2.PartialSynchrony.broadcast
theorem AvailableChain.V2.PartialSynchrony.relay
structure AvailableChain.V2.HealthyPrefixDelivery
ctor AvailableChain.V2.HealthyPrefixDelivery.mk
theorem AvailableChain.V2.HealthyPrefixDelivery.broadcast
theorem AvailableChain.V2.HealthyPrefixDelivery.relay
```

### `AvailableChainEngineV2.Conditions.Interface`

```text
structure AvailableChain.V2.Interface
ctor AvailableChain.V2.Interface.mk
def AvailableChain.V2.Interface.confirmed
def AvailableChain.V2.Interface.stable
def AvailableChain.V2.Interface.block
def AvailableChain.V2.Interface.opening
def AvailableChain.V2.Interface.propLabel
theorem AvailableChain.V2.Interface.propLabel_single
theorem AvailableChain.V2.Interface.propLabel_injective
def AvailableChain.V2.proposalTime
def AvailableChain.V2.propSeat
def AvailableChain.V2.proposerOf
theorem AvailableChain.V2.eq_propSeat
theorem AvailableChain.V2.holder_propLabel
def AvailableChain.V2.Output
def AvailableChain.V2.outputAt
def AvailableChain.V2.BlockInRun
def AvailableChain.V2.RootInjective
theorem AvailableChain.V2.rootInjective_all
```

### `AvailableChainEngineV2.Conditions.Schedule`

```text
def AvailableChain.V2.PublicTime
structure AvailableChain.V2.ScheduleWellFormed
ctor AvailableChain.V2.ScheduleWellFormed.mk
theorem AvailableChain.V2.ScheduleWellFormed.horizon_nonneg
theorem AvailableChain.V2.ScheduleWellFormed.sorted
theorem AvailableChain.V2.ScheduleWellFormed.nodup
theorem AvailableChain.V2.ScheduleWellFormed.in_horizon
theorem AvailableChain.V2.ScheduleWellFormed.honest_only
theorem AvailableChain.V2.ScheduleWellFormed.tick_public
theorem AvailableChain.V2.ScheduleWellFormed.tick_total
def AvailableChain.V2.NoRestart
def AvailableChain.V2.restartFree
structure AvailableChain.V2.DeliveryWellFormed
ctor AvailableChain.V2.DeliveryWellFormed.mk
theorem AvailableChain.V2.DeliveryWellFormed.wire
theorem AvailableChain.V2.DeliveryWellFormed.deps
theorem AvailableChain.V2.DeliveryWellFormed.fresh
structure AvailableChain.V2.UnforgeableSignatures
ctor AvailableChain.V2.UnforgeableSignatures.mk
theorem AvailableChain.V2.UnforgeableSignatures.unforgeable
theorem AvailableChain.V2.UnforgeableSignatures.carried
structure AvailableChain.V2.ExecutionValid
theorem AvailableChain.V2.ExecutionValid.toDeliveryWellFormed
theorem AvailableChain.V2.ExecutionValid.toScheduleWellFormed
theorem AvailableChain.V2.ExecutionValid.toUnforgeableSignatures
ctor AvailableChain.V2.ExecutionValid.mk
def AvailableChain.V2.SelfDelivery
theorem AvailableChain.V2.ScheduleWellFormed.mem_emittedAt_iff_emits
theorem AvailableChain.V2.restartFree_refl
theorem AvailableChain.V2.not_restartFree_succ_iff
theorem AvailableChain.V2.restartFree.mono
theorem AvailableChain.V2.restartFree.append
theorem AvailableChain.V2.NoRestart.restartFree
```

### `AvailableChainEngineV2.Laws.Hooks`

```text
structure AvailableChain.V2.HooksSound
ctor AvailableChain.V2.HooksSound.mk
theorem AvailableChain.V2.HooksSound.excludes_inert
theorem AvailableChain.V2.HooksSound.excludes_stable
theorem AvailableChain.V2.HooksSound.processed_stable
theorem AvailableChain.V2.HooksSound.deps_stable
theorem AvailableChain.V2.HooksSound.handles_carries
theorem AvailableChain.V2.HooksSound.recordOwn_processed
theorem AvailableChain.V2.HooksSound.recordOwn_deps
theorem AvailableChain.V2.HooksSound.recordOwn_excludes
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_processed
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_deps
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_excludes
theorem AvailableChain.V2.HooksSound.processed_tick
theorem AvailableChain.V2.HooksSound.deps_tick
theorem AvailableChain.V2.HooksSound.excludes_tick
```

### `AvailableChainEngineV2.Laws.Isolation`

```text
def AvailableChain.V2.LabelFamilies.APObject
theorem AvailableChain.V2.LabelFamilies.apObject_seat
theorem AvailableChain.V2.LabelFamilies.apObject_none
structure AvailableChain.V2.Isolation
ctor AvailableChain.V2.Isolation.mk
def AvailableChain.V2.Isolation.Base
def AvailableChain.V2.Isolation.base
def AvailableChain.V2.Isolation.clockB
theorem AvailableChain.V2.Isolation.clock_base
def AvailableChain.V2.Isolation.processB
theorem AvailableChain.V2.Isolation.process_base
theorem AvailableChain.V2.Isolation.recordOwn_base
def AvailableChain.V2.Isolation.actB
theorem AvailableChain.V2.Isolation.act_base
def AvailableChain.V2.Isolation.gossipB
theorem AvailableChain.V2.Isolation.gossip_base
def AvailableChain.V2.Isolation.depsB
def AvailableChain.V2.Isolation.processedB
def AvailableChain.V2.Isolation.excludesB
def AvailableChain.V2.Isolation.handlesB
theorem AvailableChain.V2.Isolation.hooks_base
theorem AvailableChain.V2.Isolation.separation
theorem AvailableChain.V2.Isolation.foldl_recordOwn_base
theorem AvailableChain.V2.Isolation.base_tick
theorem AvailableChain.V2.Isolation.hooks_congr
theorem AvailableChain.V2.Isolation.not_ap_of_selfVisible
```

### `AvailableChainEngineV2.Laws.Outputs`

```text
structure AvailableChain.V2.OutputsFactor
ctor AvailableChain.V2.OutputsFactor.mk
def AvailableChain.V2.OutputsFactor.confirmedB
theorem AvailableChain.V2.OutputsFactor.confirmed_base
def AvailableChain.V2.OutputsFactor.stableB
theorem AvailableChain.V2.OutputsFactor.stable_base
theorem AvailableChain.V2.OutputsFactor.confirmed_recordOwn
theorem AvailableChain.V2.OutputsFactor.stable_recordOwn
theorem AvailableChain.V2.OutputsFactor.confirmed_tick
theorem AvailableChain.V2.OutputsFactor.stable_tick
```

### `AvailableChainEngineV2.Laws.SelfDelivery`

```text
structure AvailableChain.V2.EmitOk
ctor AvailableChain.V2.EmitOk.mk
theorem AvailableChain.V2.EmitOk.wire
theorem AvailableChain.V2.EmitOk.deps
theorem AvailableChain.V2.EmitOk.fresh
theorem AvailableChain.V2.EmitOk.noCarried
theorem AvailableChain.V2.Run.holder_of_mem_tick
theorem AvailableChain.V2.World.step_apply_of_node_ne
theorem AvailableChain.V2.Run.stateBefore_eq_of_node_ne
theorem AvailableChain.V2.selfDelivery_admissible
theorem AvailableChain.V2.Run.getElem?_snoc_of_lt
theorem AvailableChain.V2.Run.tick_snoc
theorem AvailableChain.V2.Run.stateBefore_snoc_of_le
theorem AvailableChain.V2.Run.emitsAt_snoc_of_lt
theorem AvailableChain.V2.Run.emits_snoc
theorem AvailableChain.V2.EmitOk.snoc
theorem AvailableChain.V2.ExecutionValid.snoc_selfDelivery
```

## Kit v2 (frozen by rule, not locked)

### `AvailableChainKitV2.ClockLaws`

```text
structure AvailableChain.V2.Engine.ClockLaws
ctor AvailableChain.V2.Engine.ClockLaws.mk
def AvailableChain.V2.Engine.ClockLaws.now
theorem AvailableChain.V2.Engine.ClockLaws.init
theorem AvailableChain.V2.Engine.ClockLaws.clock
theorem AvailableChain.V2.Engine.ClockLaws.process
theorem AvailableChain.V2.Engine.ClockLaws.recordOwn_now
theorem AvailableChain.V2.Engine.ClockLaws.now_foldl_recordOwn
theorem AvailableChain.V2.Engine.ClockLaws.now_tick
```

### `AvailableChainKitV2.Emission`

```text
theorem AvailableChain.V2.Engine.mem_tick_seat_iff
theorem AvailableChain.V2.Engine.ownSeats_bijSeat
theorem AvailableChain.V2.Engine.emits_bijSeat
theorem AvailableChain.V2.Engine.linked_index_stable
def AvailableChain.V2.Engine.ownReleasedAt
def AvailableChain.V2.Engine.ownReleased
theorem AvailableChain.V2.Engine.ownReleased_self
theorem AvailableChain.V2.Engine.ownReleased_succ
theorem AvailableChain.V2.Engine.ownRecord_fold_interval
theorem AvailableChain.V2.Engine.ownRecord_fold
```

### `AvailableChainKitV2.EngineClock`

```text
theorem AvailableChain.V2.Engine.stateBefore_now_source
theorem AvailableChain.V2.Engine.stateBefore_now_source_noRestart
theorem AvailableChain.V2.Engine.stateBefore_now_le_event
theorem AvailableChain.V2.Engine.stateBefore_now_le_event_noRestart
theorem AvailableChain.V2.Engine.stateBefore_now_mono
theorem AvailableChain.V2.Engine.stateBefore_now_mono_noRestart
theorem AvailableChain.V2.Engine.delivery_now_ge_public
theorem AvailableChain.V2.Engine.stateBefore_invariant
theorem AvailableChain.V2.Engine.stateBefore_invariant_noRestart
theorem AvailableChain.V2.Engine.stateBefore_stable_clock
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_restore
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_noRestart
theorem AvailableChain.V2.Engine.clock_field_origin
theorem AvailableChain.V2.Engine.clock_field_origin_noRestart
theorem AvailableChain.V2.Engine.stateBefore_field_prefix
theorem AvailableChain.V2.Engine.stateBefore_field_prefix_restore
```

### `AvailableChainKitV2.Execution`

```text
theorem AvailableChain.V2.Engine.eventIndex_lt_of_time_lt
theorem AvailableChain.V2.Engine.time_le_of_key_le
theorem AvailableChain.V2.Engine.filter_eq_take
theorem AvailableChain.V2.Engine.filter_false_of_index_ge
theorem AvailableChain.V2.Engine.index_lt_read_length_iff
theorem AvailableChain.V2.Engine.read_length_mono
theorem AvailableChain.V2.Engine.tick_index_lt_delivery
theorem AvailableChain.V2.Engine.readAt_eq_stateBefore
theorem AvailableChain.V2.Engine.stateBefore_other_node
theorem AvailableChain.V2.Engine.stateBefore_tick_eq_stateBeforeTime
```

### `AvailableChainKitV2.RunCheck`

```text
def AvailableChain.V2.Engine.allTicks
def AvailableChain.V2.Engine.allDeliveries
theorem AvailableChain.V2.Engine.allTicks_spec
theorem AvailableChain.V2.Engine.allDeliveries_spec
def AvailableChain.V2.Engine.emittedBy
theorem AvailableChain.V2.Engine.emittedBy_spec
```

### `AvailableChainKitV2.Stable`

```text
theorem AvailableChain.V2.Engine.foldl_recordOwn_preserve
theorem AvailableChain.V2.Engine.tick_preserve
theorem AvailableChain.V2.Engine.recordOwn_preserve_of_base
theorem AvailableChain.V2.Engine.stateBefore_step_induction
theorem AvailableChain.V2.Engine.stateBefore_stable
```
