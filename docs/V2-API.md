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
  Framework does not import it, so the lock does not see it. Each Kit line
  carries a hash of the declaration (the `ownHash` of the lock: kind, name
  and type; for a definition also the value; for a theorem not the proof),
  and `V2Manifest --check` fails when it differs. A new proof keeps the
  hash.

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
  roots (imports only).
- `AvailableChainEngineV2.Sketch` was deleted at the gate; it is not API.
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
  declaration of a scope module is not listed, if a scope module has no
  heading, or if a Kit hash is missing or differs.
- `V2Manifest --check` enforces completeness, so 2b adds a manifest line
  for each new public declaration in a 2a scope module.
- The dependency rules of `V2Manifest` (`generated`, `deps`, the closure
  traversal and `ownHash`) are copies of `scripts/CatalogLock.lean`, so a
  change to one needs the same change in the other.

Each engine block line is `<kind> <name>`; each Kit block line is
`<kind> <name> <hash>`. The kinds are `structure`,
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
structure AvailableChain.V2.Engine.ClockLaws fc09d26a5ca2efe9
ctor AvailableChain.V2.Engine.ClockLaws.mk 963725a997cfe456
def AvailableChain.V2.Engine.ClockLaws.now 0818dc2b5c0580bd
theorem AvailableChain.V2.Engine.ClockLaws.init b0046531e2108564
theorem AvailableChain.V2.Engine.ClockLaws.clock 9a51e21d6a8d6f93
theorem AvailableChain.V2.Engine.ClockLaws.process 320b22468d71b171
theorem AvailableChain.V2.Engine.ClockLaws.recordOwn_now 5b819202d45632ac
theorem AvailableChain.V2.Engine.ClockLaws.now_foldl_recordOwn 6acde894ad2bf95f
theorem AvailableChain.V2.Engine.ClockLaws.now_tick 3d879039e512cff7
```

### `AvailableChainKitV2.Emission`

```text
theorem AvailableChain.V2.Engine.mem_tick_seat_iff 006aec3a630ae0fe
theorem AvailableChain.V2.Engine.ownSeats_bijSeat 07980b4bc97477b3
theorem AvailableChain.V2.Engine.emits_bijSeat 5f46f73d6dc88b27
theorem AvailableChain.V2.Engine.linked_index_stable 1298159da25de1fa
def AvailableChain.V2.Engine.ownReleasedAt f567774a83d69639
def AvailableChain.V2.Engine.ownReleased fbf086a200f7c9a6
theorem AvailableChain.V2.Engine.ownReleased_self bed19c2ef7c9a38b
theorem AvailableChain.V2.Engine.ownReleased_succ 72ae69e106cb83f1
theorem AvailableChain.V2.Engine.ownRecord_fold_interval 887dfb90b0824007
theorem AvailableChain.V2.Engine.ownRecord_fold 55eba987f28e77e4
```

### `AvailableChainKitV2.EngineClock`

```text
theorem AvailableChain.V2.Engine.stateBefore_now_source 0efc0ea1c2300360
theorem AvailableChain.V2.Engine.stateBefore_now_source_noRestart 141908242eda9f99
theorem AvailableChain.V2.Engine.stateBefore_now_le_event 6adf4d6553f1e6a3
theorem AvailableChain.V2.Engine.stateBefore_now_le_event_noRestart 16532f03bd7e0ca5
theorem AvailableChain.V2.Engine.stateBefore_now_mono 1801977662beaa25
theorem AvailableChain.V2.Engine.stateBefore_now_mono_noRestart 2b5a4bde9b4baec9
theorem AvailableChain.V2.Engine.delivery_now_ge_public 4fedd51eea932bf7
theorem AvailableChain.V2.Engine.stateBefore_invariant bea6770976ae27c8
theorem AvailableChain.V2.Engine.stateBefore_invariant_noRestart bbf0729e3d31dd75
theorem AvailableChain.V2.Engine.stateBefore_stable_clock a9525d23838821ff
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_restore 73a3baac5721d3e9
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_noRestart c20b884227330b75
theorem AvailableChain.V2.Engine.clock_field_origin 387a6c5219e03df3
theorem AvailableChain.V2.Engine.clock_field_origin_noRestart 0a4f3eda6462ef6e
theorem AvailableChain.V2.Engine.stateBefore_field_prefix f0c086e1226e1e20
theorem AvailableChain.V2.Engine.stateBefore_field_prefix_restore fdc79d68eb032d68
```

### `AvailableChainKitV2.Execution`

```text
theorem AvailableChain.V2.Engine.eventIndex_lt_of_time_lt 24dab09d913d76da
theorem AvailableChain.V2.Engine.time_le_of_key_le bc105a2b434680eb
theorem AvailableChain.V2.Engine.filter_eq_take 07377680d141acb8
theorem AvailableChain.V2.Engine.filter_false_of_index_ge ca61f198f3f28406
theorem AvailableChain.V2.Engine.index_lt_read_length_iff 02d23c58451a66d5
theorem AvailableChain.V2.Engine.read_length_mono d4ecff500f4ddd08
theorem AvailableChain.V2.Engine.tick_index_lt_delivery 171dbff20346ebf5
theorem AvailableChain.V2.Engine.readAt_eq_stateBefore 120aaf0cfe991c8b
theorem AvailableChain.V2.Engine.stateBefore_other_node 23c1699911a45ffe
theorem AvailableChain.V2.Engine.stateBefore_tick_eq_stateBeforeTime 4b5048229edc779f
```

### `AvailableChainKitV2.RunCheck`

```text
def AvailableChain.V2.Engine.allTicks 07a159715486acf9
def AvailableChain.V2.Engine.allDeliveries 080a6e0b526fce14
theorem AvailableChain.V2.Engine.allTicks_spec 8cb7a8d9cdf51028
theorem AvailableChain.V2.Engine.allDeliveries_spec 2d069feb359f4870
def AvailableChain.V2.Engine.emittedBy c5d965d958512fa4
theorem AvailableChain.V2.Engine.emittedBy_spec b58d339ed13a4e60
```

### `AvailableChainKitV2.Stable`

```text
theorem AvailableChain.V2.Engine.foldl_recordOwn_preserve f3dcff3c1396abea
theorem AvailableChain.V2.Engine.tick_preserve 8eae668bb4316e44
theorem AvailableChain.V2.Engine.recordOwn_preserve_of_base 76c0b752b309cc6f
theorem AvailableChain.V2.Engine.stateBefore_step_induction 4ea8ccb55351ee08
theorem AvailableChain.V2.Engine.stateBefore_stable 9bca2267a8fc5385
```
