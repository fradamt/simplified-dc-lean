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

- **This file is append-only.** A changed or removed line in a diff of this
  file is a freeze break, unless a named user decision allows it. A new
  line is an ADD.
- **Engine v2 entries are locked.** The value of
  `AvailableChain.Framework.V2.anchor` (`AvailableChainFramework/V2/Anchor.lean`)
  references each engine entry. `scripts/CatalogLock.lean` locks the module
  prefix `AvailableChainFramework.V2`, so the lock line of the anchor hashes
  the closure of every engine entry. A change to an engine entry gives a
  `CHANGED` line. As everywhere in the lock, a theorem contributes its
  statement only: a new proof keeps the hash. A change to a model module in
  the closure (for example `AvailableChainModel.Objects.Time`) also changes
  the anchor line.
- **Every entry has its own hash.** Each line of the blocks below ends with
  an entry hash, and `V2Manifest --check` fails when it differs. Thus a
  change to one engine entry is found even in a commit that also has a
  `CHANGED` anchor line, and a change to a Kit entry is found although the
  lock does not see the Kit (L5; the Framework does not import it). The
  entry hash mixes: the own hash of the entry and of every generated or
  private constant in its closure (`deps` rules of the lock) that is in a v2
  module or in the module of the entry (matchers, equation lemmas,
  `_proof_` constants, private helpers), in `Name.lt` order; the binder
  names and binder infos of its type; its reducibility status; and whether
  it is an instance. The own hash is the `ownHash` of the lock (kind, name
  and type; for a definition also the value; for an inductive also the
  constructor names; for a theorem not the proof), after the universe
  parameters are renamed `u0`, `u1`, …. A new proof keeps the hash.
- **Frozen by rule, not checked.** The lock hash does not see binder names,
  binder infos, reducibility or attributes. The entry hash sees binder names
  and binder infos of the type, reducibility and the instance attribute, but
  not other attributes (for example `@[simp]` on
  `LabelFamilies.apObject_seat`) or an instance priority. All of them are
  frozen by rule.

## Anchors

Never edit `anchor`. A later stage adds its engine entries to this file
and one new anchor def in a new module under `AvailableChainFramework/V2/`
(for example `anchor_2b` in `Anchor2b.lean`, imported by the Framework
root); `V2Manifest --anchor` prints its body (the engine entries that no
anchor covers yet). The lock change is then ADDED only. An engine entry is
anchored if it is in the closure of some non-generated declaration of a
module under `AvailableChainFramework.V2`.

## Scope

An entry is a declaration of a scope module that Lean did not generate, by
the rule of `scripts/CatalogLock.lean` (`generated`). Thus the list
includes structure constructors and fields (projections) and derived
instances, and excludes recursors, `casesOn`, `noConfusion`, matchers,
equation lemmas, `injEq`, `sizeOf_spec` and private declarations.

- Scope modules: `AvailableChainEngineV2.Engine.*`,
  `AvailableChainEngineV2.Conditions.*`, `AvailableChainEngineV2.Laws.*`,
  and every module `AvailableChainKitV2.*` outside `AvailableChainKitV2.Tests`.
- Not in scope: the modules `AvailableChainEngineV2.Tests.*` (namespace
  `AvailableChain.V2.Tests`) and `AvailableChainKitV2.Tests.*` (the Kit
  counterexamples, namespace `AvailableChain.V2.Engine.Tests`, and the toy
  run, namespace `AvailableChain.V2.Tests.Toy`); the library roots (imports
  only). The exclusion is by module, not by namespace.
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
  blocks below from the environment, in source order, with the hashes.
- `lake env lean --run scripts/V2Manifest.lean --anchor` prints the body of
  a new anchor def over the engine entries that no anchor covers yet.
- `lake env lean --run scripts/V2Manifest.lean --check` exits 1 if the
  anchor `AvailableChain.Framework.V2.anchor` is missing, if an entry does
  not exist or is not in the module of its heading, if a kind word differs,
  if a hash is missing or differs, if an engine entry is not anchored, if a
  public declaration of a scope module is not listed, or if a scope module
  has no heading. It exits 2 if the declaration ranges (`.olean.server`
  data) are missing.
- `V2Manifest --check` enforces completeness, so 2b adds a manifest line
  for each new public declaration in a 2a scope module.
- `generated`, `deps`, the closure traversal, `kindTag` and `ownHash` in
  `V2Manifest` are copies of `scripts/CatalogLock.lean`, except that
  `ownHash` renames the universe parameters first. A change to one needs
  the same change in the other.

Each block line is `<kind> <name> <hash>`. The kinds are `structure`,
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
inductive AvailableChain.V2.Auth e0749b12d9290b4d
ctor AvailableChain.V2.Auth.seat f6d97cf3e111af9e
ctor AvailableChain.V2.Auth.none e11fb64fcae05f30
def AvailableChain.V2.instDecidableEqAuth 1d428297fc73352e
def AvailableChain.V2.instDecidableEqAuth.decEq fceddc12ce3953bb
def AvailableChain.V2.instReprAuth c2401a2018acad34
def AvailableChain.V2.instReprAuth.repr 394e110703bf8cd2
structure AvailableChain.V2.Signed eb51b595acf689f7
ctor AvailableChain.V2.Signed.mk 8cff11c1b0d37086
def AvailableChain.V2.Signed.auth f31626f250c59e65
def AvailableChain.V2.Signed.payload 7a6a405749882085
def AvailableChain.V2.instDecidableEqSigned bf0b5513bcfbf2b9
def AvailableChain.V2.instDecidableEqSigned.decEq 28803949f7849550
def AvailableChain.V2.instReprSigned 4ecd9ae7fc5dbdff
def AvailableChain.V2.instReprSigned.repr e8c5c6f07ec10d2e
```

### `AvailableChainEngineV2.Engine.Run`

```text
inductive AvailableChain.V2.Event 17fc49f3e3d44f34
ctor AvailableChain.V2.Event.restart 92474f35a882e910
ctor AvailableChain.V2.Event.tick ee6bed1e67349f17
ctor AvailableChain.V2.Event.deliver 0d3fe5a920053bc5
def AvailableChain.V2.instDecidableEqEvent 0b448e365077931b
def AvailableChain.V2.instDecidableEqEvent.decEq 36b9b8af5f20b322
def AvailableChain.V2.Event.time 086db62cc7ad993e
def AvailableChain.V2.Event.node b4af9c756d486963
def AvailableChain.V2.Event.object? 44866cf0dd8e3fb8
def AvailableChain.V2.Event.phase ab3e61fa07d2c99f
def AvailableChain.V2.Event.key d37ad9c14541145e
def AvailableChain.V2.World f57ade52b24cfa64
def AvailableChain.V2.World.init d7b4a3e9d1a2fd65
structure AvailableChain.V2.Run 3370ef0fe40282df
ctor AvailableChain.V2.Run.mk 17c68ddb2b08ddab
def AvailableChain.V2.Run.honest b543988cf8f78c51
def AvailableChain.V2.Run.horizon c427750f04e53280
def AvailableChain.V2.Run.events 6e2e0cc268bc42ae
def AvailableChain.V2.Run.seatOf 1e54338610af0269
def AvailableChain.V2.Run.input f84a1d5e3fcc41f3
def AvailableChain.V2.Run.ownSeats 10ef2c22290b377f
def AvailableChain.V2.tick 1c914e906d124e5d
def AvailableChain.V2.World.step 8cfb45073bc45033
def AvailableChain.V2.Run.stateBefore 763020a483ecab7b
def AvailableChain.V2.Run.stateBeforeTime 885b5f62fd83033a
def AvailableChain.V2.Run.readAt a19e62767c027e22
def AvailableChain.V2.Run.final 395a0ddaa96e4ada
def AvailableChain.V2.Run.emitsAt 349ddf37a2eaac6a
def AvailableChain.V2.Run.tickIdx? 00041c6a69978ce3
def AvailableChain.V2.Run.emittedAt 93404267fa9ca264
def AvailableChain.V2.Run.emits 38adc76ce4d8747b
def AvailableChain.V2.Run.processes 121f6339a5889215
def AvailableChain.V2.Run.handlesAt 3b15bf6380058b0c
def AvailableChain.V2.Run.acceptsAt 0781f9fda35f1be7
def AvailableChain.V2.Run.holder b5414f214a8ee822
theorem AvailableChain.V2.Run.stateBefore_succ c3b25dc169753c9a
theorem AvailableChain.V2.Run.step_tick_eq 21401c3258e05521
theorem AvailableChain.V2.tick_decomp f06760ab3be4be81
theorem AvailableChain.V2.tick_asleep 5575069be0c6bac1
theorem AvailableChain.V2.Run.tickIdx?_spec cb64a07baf46892c
theorem AvailableChain.V2.Run.emittedAt_eq_emitsAt 2c39ca7ab053787f
theorem AvailableChain.V2.Run.mem_emittedAt_iff_emits 8d23924024f36dd4
```

### `AvailableChainEngineV2.Engine.Spec`

```text
structure AvailableChain.V2.ProtocolSpec 391a0211a41fb997
ctor AvailableChain.V2.ProtocolSpec.mk b9237b1b6957e94b
def AvailableChain.V2.ProtocolSpec.State 5d0832010f8f405c
def AvailableChain.V2.ProtocolSpec.Label ba2efb1ee38fd904
def AvailableChain.V2.ProtocolSpec.seats ab698d0fda743362
def AvailableChain.V2.ProtocolSpec.Payload a41f8aaebbd3cd47
def AvailableChain.V2.ProtocolSpec.Durable 7da03717eddc1992
def AvailableChain.V2.ProtocolSpec.init de1d7455b740fdcd
def AvailableChain.V2.ProtocolSpec.clock 875006559feba4bb
def AvailableChain.V2.ProtocolSpec.actTime 76cd58bcf2fda2e9
def AvailableChain.V2.ProtocolSpec.duties 23ba73bc93c85c21
theorem AvailableChain.V2.ProtocolSpec.duties_spec 07be43cb00f8d24e
theorem AvailableChain.V2.ProtocolSpec.duties_nodup 0b7e32802ace2380
def AvailableChain.V2.ProtocolSpec.act 1ffbdbe495b5be61
def AvailableChain.V2.ProtocolSpec.gossip 9d8e8d32480fad72
def AvailableChain.V2.ProtocolSpec.process 80296bc006871137
def AvailableChain.V2.ProtocolSpec.selfVisible 17e08ba7a7bb2a72
def AvailableChain.V2.ProtocolSpec.recordOwn bb26dcecd03fcc07
def AvailableChain.V2.ProtocolSpec.durable e270211d19a513bb
def AvailableChain.V2.ProtocolSpec.restore 05c1f533e4d3d510
def AvailableChain.V2.ProtocolSpec.wellFormed c729122416c37d7b
def AvailableChain.V2.ProtocolSpec.depsPresent 5b856565ba8dc6ad
def AvailableChain.V2.ProtocolSpec.processed f78c8eee849421e4
def AvailableChain.V2.ProtocolSpec.excludes a054d9262c30d468
def AvailableChain.V2.ProtocolSpec.handles ee962816d95527da
def AvailableChain.V2.ProtocolSpec.carries 5c3e1d72f3888f50
def AvailableChain.V2.ProtocolSpec.Object bd98c959f9709ec3
def AvailableChain.V2.ProtocolSpec.objSelfVisible be72efe7d7d4a2a5
```

### `AvailableChainEngineV2.Conditions.Committees`

```text
structure AvailableChain.V2.LabelFamilies eb378268eb8e2019
ctor AvailableChain.V2.LabelFamilies.mk 513fa70b7beaa408
def AvailableChain.V2.LabelFamilies.ap 80808db76d2901dd
def AvailableChain.V2.LabelFamilies.fresh 7565d6f2c151d660
def AvailableChain.V2.LabelFamilies.linked e038b3e424866a81
def AvailableChain.V2.CStar a68134dcea6dfea4
def AvailableChain.V2.Linked f6bb3355a2edd663
def AvailableChain.V2.SingleSeat d796e953232b862f
theorem AvailableChain.V2.Linked.toCStar f3fbb95bd1d9641b
theorem AvailableChain.V2.CStar.seats_eq e8fda8fca528afde
```

### `AvailableChainEngineV2.Conditions.Delivery`

```text
structure AvailableChain.V2.PartialSynchrony ab600c3d0c1d228e
ctor AvailableChain.V2.PartialSynchrony.mk 111e75a4a25bfd44
theorem AvailableChain.V2.PartialSynchrony.broadcast 558a8257f6491bc4
theorem AvailableChain.V2.PartialSynchrony.relay 5e40bc8eb116e44b
structure AvailableChain.V2.HealthyPrefixDelivery 1fe4ff904a5f5101
ctor AvailableChain.V2.HealthyPrefixDelivery.mk f7d52d6d2fa231b6
theorem AvailableChain.V2.HealthyPrefixDelivery.broadcast 6597c0ffed89e259
theorem AvailableChain.V2.HealthyPrefixDelivery.relay 05ad97350db31e58
```

### `AvailableChainEngineV2.Conditions.Interface`

```text
structure AvailableChain.V2.Interface d25a81c97f6adcbf
ctor AvailableChain.V2.Interface.mk 4ef77d5bd1d78d98
def AvailableChain.V2.Interface.confirmed 9baff0e82497d7de
def AvailableChain.V2.Interface.stable d3463f1ba5c43ea3
def AvailableChain.V2.Interface.block a62fc84cecb9193f
def AvailableChain.V2.Interface.opening 57ad048ff7300e5a
def AvailableChain.V2.Interface.propLabel 1665926ec36031f7
theorem AvailableChain.V2.Interface.propLabel_single 4766579f07ff654c
theorem AvailableChain.V2.Interface.propLabel_injective 0fc741c981ac3b8f
def AvailableChain.V2.proposalTime b4243682e4a34ebf
def AvailableChain.V2.propSeat 476242fb6623604e
def AvailableChain.V2.proposerOf 359fce58f245c1fc
theorem AvailableChain.V2.eq_propSeat 3397a97d804900f6
theorem AvailableChain.V2.holder_propLabel 27ec6bd7f446f776
def AvailableChain.V2.Output a8967dbc86e9ed88
def AvailableChain.V2.outputAt 6d65f74a38f549ef
def AvailableChain.V2.BlockInRun 68dcaba80b5e19c3
def AvailableChain.V2.RootInjective 845c03c72958e529
theorem AvailableChain.V2.rootInjective_all ff5d1bbc0c012ead
```

### `AvailableChainEngineV2.Conditions.Schedule`

```text
def AvailableChain.V2.PublicTime b66e00481417d389
structure AvailableChain.V2.ScheduleWellFormed 5e6d43e8916f59d8
ctor AvailableChain.V2.ScheduleWellFormed.mk a5cd76ec7fb2d635
theorem AvailableChain.V2.ScheduleWellFormed.horizon_nonneg 1f9b37d96351c9ec
theorem AvailableChain.V2.ScheduleWellFormed.sorted 03dc3022a0048124
theorem AvailableChain.V2.ScheduleWellFormed.nodup cdf58bfc7678e96a
theorem AvailableChain.V2.ScheduleWellFormed.in_horizon 2722687f96f39290
theorem AvailableChain.V2.ScheduleWellFormed.honest_only b0dac60f5d609933
theorem AvailableChain.V2.ScheduleWellFormed.tick_public 4c448f7c52759fa0
theorem AvailableChain.V2.ScheduleWellFormed.tick_total 6fff89f244a1b613
def AvailableChain.V2.NoRestart e61d0ed64ee146fb
def AvailableChain.V2.restartFree 54d237306430298a
structure AvailableChain.V2.DeliveryWellFormed 63de473754d0d5e5
ctor AvailableChain.V2.DeliveryWellFormed.mk a4247de0aee23a71
theorem AvailableChain.V2.DeliveryWellFormed.wire dd56c158a098f288
theorem AvailableChain.V2.DeliveryWellFormed.deps 8f72b97bce8f6a5a
theorem AvailableChain.V2.DeliveryWellFormed.fresh 1531e7b3d08fc07d
structure AvailableChain.V2.UnforgeableSignatures 5b9d9f3ac7a1c98f
ctor AvailableChain.V2.UnforgeableSignatures.mk 65c487582053bd0c
theorem AvailableChain.V2.UnforgeableSignatures.unforgeable a0415e0d5f8f2665
theorem AvailableChain.V2.UnforgeableSignatures.carried 8aa14a96eb6d1951
structure AvailableChain.V2.ExecutionValid ac0e10a1ebd4aec2
theorem AvailableChain.V2.ExecutionValid.toDeliveryWellFormed 417cebbb9d6e8638
theorem AvailableChain.V2.ExecutionValid.toScheduleWellFormed 2f1ac4ad08804301
theorem AvailableChain.V2.ExecutionValid.toUnforgeableSignatures 17047eeaeb61cfc6
ctor AvailableChain.V2.ExecutionValid.mk 6a0552def58c3d64
def AvailableChain.V2.SelfDelivery 083faf915ed055db
theorem AvailableChain.V2.ScheduleWellFormed.mem_emittedAt_iff_emits f068cecd33503f64
theorem AvailableChain.V2.restartFree_refl 5f03854e731d9a71
theorem AvailableChain.V2.not_restartFree_succ_iff b8a5c09d141b0597
theorem AvailableChain.V2.restartFree.mono 293ff6bbd0b42da4
theorem AvailableChain.V2.restartFree.append 13e8f02bf1446ac3
theorem AvailableChain.V2.NoRestart.restartFree a600ca784a52ed6c
```

### `AvailableChainEngineV2.Laws.Hooks`

```text
structure AvailableChain.V2.HooksSound 0eeb035670cbe6c8
ctor AvailableChain.V2.HooksSound.mk a87e4efc6c04ba83
theorem AvailableChain.V2.HooksSound.excludes_inert a21b4275aa9ce188
theorem AvailableChain.V2.HooksSound.excludes_stable af522cee03bbff9e
theorem AvailableChain.V2.HooksSound.processed_stable 7117974c28e60687
theorem AvailableChain.V2.HooksSound.deps_stable 5000f91ac5d538b3
theorem AvailableChain.V2.HooksSound.handles_carries 829d08e707b75e6a
theorem AvailableChain.V2.HooksSound.recordOwn_processed b78d1d21d28bbe4d
theorem AvailableChain.V2.HooksSound.recordOwn_deps cdb2ef79741a8cb4
theorem AvailableChain.V2.HooksSound.recordOwn_excludes 731032b78ed7bafd
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_processed 34e3aec93302c3e4
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_deps 8dfeff817fda3f03
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_excludes 8dc5491c090571c8
theorem AvailableChain.V2.HooksSound.processed_tick c877c47ffc4a1671
theorem AvailableChain.V2.HooksSound.deps_tick 6492b34635cc39b6
theorem AvailableChain.V2.HooksSound.excludes_tick f5c81a187e49a61c
```

### `AvailableChainEngineV2.Laws.Isolation`

```text
def AvailableChain.V2.LabelFamilies.APObject 1b8b24b15df87550
theorem AvailableChain.V2.LabelFamilies.apObject_seat ca38e22cfe53fc12
theorem AvailableChain.V2.LabelFamilies.apObject_none f4e3608a8e338f01
structure AvailableChain.V2.Isolation 0361f6718bd4db7e
ctor AvailableChain.V2.Isolation.mk 34d112ad94c13bb8
def AvailableChain.V2.Isolation.Base 7a22733b1f66457f
def AvailableChain.V2.Isolation.base 6cbc7adbb8cf47e5
def AvailableChain.V2.Isolation.clockB 7befe41168502298
theorem AvailableChain.V2.Isolation.clock_base 922284d6b4d09823
def AvailableChain.V2.Isolation.processB 43970d363b1c2ca6
theorem AvailableChain.V2.Isolation.process_base c50ac4b9ce413a4e
theorem AvailableChain.V2.Isolation.recordOwn_base fdf223dc12e74790
def AvailableChain.V2.Isolation.actB 8018f983b4810b68
theorem AvailableChain.V2.Isolation.act_base 1dd3a5996553a6e4
def AvailableChain.V2.Isolation.gossipB 55ce7ca0061d859b
theorem AvailableChain.V2.Isolation.gossip_base 0cb7c7a45233ffd2
def AvailableChain.V2.Isolation.depsB ec13140554664fe3
def AvailableChain.V2.Isolation.processedB f14b044c76b9bcdc
def AvailableChain.V2.Isolation.excludesB e510753ccae53685
def AvailableChain.V2.Isolation.handlesB fb11e72bd4bb55b9
theorem AvailableChain.V2.Isolation.hooks_base 19309732a36b5209
theorem AvailableChain.V2.Isolation.separation 046bf995aa5d7a62
theorem AvailableChain.V2.Isolation.foldl_recordOwn_base c91ee9675dc3da2d
theorem AvailableChain.V2.Isolation.base_tick d1332616b346d6a1
theorem AvailableChain.V2.Isolation.hooks_congr 975114aeb7ea700a
theorem AvailableChain.V2.Isolation.not_ap_of_selfVisible 4f65165a75d4cae3
```

### `AvailableChainEngineV2.Laws.Outputs`

```text
structure AvailableChain.V2.OutputsFactor 21161da9096cae75
ctor AvailableChain.V2.OutputsFactor.mk 823d5cabd490cba9
def AvailableChain.V2.OutputsFactor.confirmedB bf31b68ab5018473
theorem AvailableChain.V2.OutputsFactor.confirmed_base 13cbd2e246e09488
def AvailableChain.V2.OutputsFactor.stableB 3f8152530f90bac8
theorem AvailableChain.V2.OutputsFactor.stable_base 9e87e2e962ce83fc
theorem AvailableChain.V2.OutputsFactor.confirmed_recordOwn ec2a2eb1c982659e
theorem AvailableChain.V2.OutputsFactor.stable_recordOwn 84a321b1acf42afa
theorem AvailableChain.V2.OutputsFactor.confirmed_tick 57681f57523becc0
theorem AvailableChain.V2.OutputsFactor.stable_tick e16babbf92381846
```

### `AvailableChainEngineV2.Laws.SelfDelivery`

```text
structure AvailableChain.V2.EmitOk 4b8076da75c1ffb3
ctor AvailableChain.V2.EmitOk.mk eda8a7281ae13a1e
theorem AvailableChain.V2.EmitOk.wire 38500b44baf5ebbd
theorem AvailableChain.V2.EmitOk.deps 42d46124308bfb9d
theorem AvailableChain.V2.EmitOk.fresh a00c66a7c25a0703
theorem AvailableChain.V2.EmitOk.noCarried 8025710775bea479
theorem AvailableChain.V2.Run.holder_of_mem_tick b7e5444e14c788fd
theorem AvailableChain.V2.World.step_apply_of_node_ne cf03d37c2066d6d8
theorem AvailableChain.V2.Run.stateBefore_eq_of_node_ne ae7576b0c2067b3a
theorem AvailableChain.V2.selfDelivery_admissible 69396efbc7dfcc8b
theorem AvailableChain.V2.Run.getElem?_snoc_of_lt 1359dbcf8d8a0d34
theorem AvailableChain.V2.Run.tick_snoc 9eed8afe0895c7ec
theorem AvailableChain.V2.Run.stateBefore_snoc_of_le c92f84f762e2e94e
theorem AvailableChain.V2.Run.emitsAt_snoc_of_lt 3c720f644717cfe2
theorem AvailableChain.V2.Run.emits_snoc d4ce4bc654778f30
theorem AvailableChain.V2.EmitOk.snoc 8b392971816412c5
theorem AvailableChain.V2.ExecutionValid.snoc_selfDelivery c91d07958d942123
```

## Kit v2 (frozen by rule, not locked)

### `AvailableChainKitV2.ClockLaws`

```text
structure AvailableChain.V2.Engine.ClockLaws e6e214315c65e225
ctor AvailableChain.V2.Engine.ClockLaws.mk b8277e0b38dbe661
def AvailableChain.V2.Engine.ClockLaws.now 5506a816124bc6ee
theorem AvailableChain.V2.Engine.ClockLaws.init 80af1315944ce1da
theorem AvailableChain.V2.Engine.ClockLaws.clock 0107374e4bd3e6b4
theorem AvailableChain.V2.Engine.ClockLaws.process 6449c5c328f3416a
theorem AvailableChain.V2.Engine.ClockLaws.recordOwn_now c2e8ee0b50782b7f
theorem AvailableChain.V2.Engine.ClockLaws.now_foldl_recordOwn 2d2bdcf845eb0000
theorem AvailableChain.V2.Engine.ClockLaws.now_tick 780b893be17c3a9b
```

### `AvailableChainKitV2.Emission`

```text
theorem AvailableChain.V2.Engine.mem_tick_seat_iff aee14ae86d085908
theorem AvailableChain.V2.Engine.ownSeats_bijSeat fdd08db67343936b
theorem AvailableChain.V2.Engine.emits_bijSeat c0e75380fcb86ad6
theorem AvailableChain.V2.Engine.linked_index_stable 76fa13690fa80e0c
def AvailableChain.V2.Engine.ownReleasedAt c14528edc3c16054
def AvailableChain.V2.Engine.ownReleased 2d1ddc98fa6dc734
theorem AvailableChain.V2.Engine.ownReleased_self 20b1974943226aee
theorem AvailableChain.V2.Engine.ownReleased_succ d16aa82750b188fd
theorem AvailableChain.V2.Engine.ownRecord_fold_interval e4cd22e2b8215d87
theorem AvailableChain.V2.Engine.ownRecord_fold da06674e0ff6843d
```

### `AvailableChainKitV2.EngineClock`

```text
theorem AvailableChain.V2.Engine.stateBefore_now_source 050ebefb099099d7
theorem AvailableChain.V2.Engine.stateBefore_now_source_noRestart 23301967fa484a37
theorem AvailableChain.V2.Engine.stateBefore_now_le_event de5b9cb19c1d974c
theorem AvailableChain.V2.Engine.stateBefore_now_le_event_noRestart 208bf0b666801a8d
theorem AvailableChain.V2.Engine.stateBefore_now_mono 8a8099d3ee5559a4
theorem AvailableChain.V2.Engine.stateBefore_now_mono_noRestart 284c8754b963f7c3
theorem AvailableChain.V2.Engine.delivery_now_ge_public ca329c58a8a5218f
theorem AvailableChain.V2.Engine.stateBefore_invariant a2c270ad386709a6
theorem AvailableChain.V2.Engine.stateBefore_invariant_noRestart 40ddbddc456586ca
theorem AvailableChain.V2.Engine.stateBefore_stable_clock 4e2b9405e8d19484
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_restore 04f1fc21e0fbcd59
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_noRestart 17fd0016010a4f5b
theorem AvailableChain.V2.Engine.clock_field_origin 10823f6123685853
theorem AvailableChain.V2.Engine.clock_field_origin_noRestart 4244aff749980e4c
theorem AvailableChain.V2.Engine.stateBefore_field_prefix f0b8dbd8377d88a5
theorem AvailableChain.V2.Engine.stateBefore_field_prefix_restore e27dddf48d97b72f
```

### `AvailableChainKitV2.Execution`

```text
theorem AvailableChain.V2.Engine.eventIndex_lt_of_time_lt 1a3206c09108d300
theorem AvailableChain.V2.Engine.time_le_of_key_le 22433293ffefed02
theorem AvailableChain.V2.Engine.filter_eq_take 7a3359a3ea3b0230
theorem AvailableChain.V2.Engine.filter_false_of_index_ge 4d33e7718e5367d0
theorem AvailableChain.V2.Engine.index_lt_read_length_iff 1e9a8711f9785fea
theorem AvailableChain.V2.Engine.read_length_mono fad77e7e86d41d54
theorem AvailableChain.V2.Engine.tick_index_lt_delivery 61c606503439616e
theorem AvailableChain.V2.Engine.readAt_eq_stateBefore 62fe529ddd8a9e7b
theorem AvailableChain.V2.Engine.stateBefore_other_node ea76dfd89556a8e4
theorem AvailableChain.V2.Engine.stateBefore_tick_eq_stateBeforeTime 54b5693e1d755f32
```

### `AvailableChainKitV2.RunCheck`

```text
def AvailableChain.V2.Engine.allTicks e1e3fb730ad651c0
def AvailableChain.V2.Engine.allDeliveries 3b59135d432480b9
theorem AvailableChain.V2.Engine.allTicks_spec b9d493581603c054
theorem AvailableChain.V2.Engine.allDeliveries_spec f1afbb5d723354f5
def AvailableChain.V2.Engine.emittedBy c1857a78618374f3
theorem AvailableChain.V2.Engine.emittedBy_spec 734f3da3325f84b9
```

### `AvailableChainKitV2.Stable`

```text
theorem AvailableChain.V2.Engine.foldl_recordOwn_preserve 184eda9ab9bfc89f
theorem AvailableChain.V2.Engine.tick_preserve 71c482797e3c677e
theorem AvailableChain.V2.Engine.recordOwn_preserve_of_base 7325df94fc4993a5
theorem AvailableChain.V2.Engine.stateBefore_step_induction 5e3c2b725e08e1cb
theorem AvailableChain.V2.Engine.stateBefore_stable 4af72dbd26e63f6a
```
