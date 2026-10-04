# V2 API manifest

_Frozen at the Phase 2a gate (plan `docs/plans/2026-09-29-phase2a-engine-v2-core.md`,
Task 7), 2026-09-29._

This file lists the frozen v2 API: every public declaration of engine v2
(`AvailableChainEngineV2`: `Engine`, `Conditions` and `Laws`) and of
Kit v2 (`AvailableChainKitV2`, without `Tests`), by fully qualified name
and grouped by module.

ROOT-DIGEST W1 exception: user option 3, 2026-10-04 (plan r2 §2 M1).
Remove only `AvailableChain.V2.rootInjective_all` and
`AvailableChain.V2.D.rootInjective_all`. Keep both scope predicates. Remove each
proof reference from its existing Framework anchor body; keep both anchors.
This exception does not permit other engine claims or checker changes.
W3 owns the final generated entries after the interface checkpoint.

ROOT-DIGEST W1c, option-3 class addition (plan r2.1 and r2.2):
the [Gen exception list](GEN-API.md#root-digest-option-3-exception) names the no-eligible-child
and retained-transport statement/equation pairs, their exact tree premises, and kernel evidence.
No v2 walk entry changes. The v2 generated delta remains the two named M1 removals above.
The tool output is `.lake/rdw1c-v2-manifest.md`; its exact delta is
`.lake/rdw1c-v2-manifest-delta.json`. Both Framework anchors remain declared.

ROOT-DIGEST-2 option 3 permits the 64 mode-indexed generic entries and measured
representation dependencies. See the [full exception](FGSA-API.md#root-digest-2-option-3-exception).
Keep the frozen baselines and SHAs. Exact old/new hashes and causes follow at integration.

## Freeze rule

After the gate, no declaration in this file changes its name, type or body
(DC N6). A 2a structure never gains a field, a 2a inductive never gains a
constructor, and a 2a definition never gains a parameter. Later stages (2b,
2c) only ADD declarations or separate structures.

- **The module blocks are append-only.** A changed or removed line in a
  module block below is a freeze break, unless a named user decision allows
  it. A new line is an ADD. The Counts table and the date line change with
  every ADD.
- **Engine v2 entries are locked.** The values of the anchor defs
  (`AvailableChain.Framework.V2.anchor` in
  `AvailableChainFramework/V2/Anchor.lean` for the 2a entries, and one new
  anchor def per later stage; see "Anchors") reference each engine entry.
  `scripts/CatalogLock.lean` locks the module prefix
  `AvailableChainFramework.V2`, so the lock lines of the anchor defs hash
  the closure of every engine entry. A change to an engine entry gives a
  `CHANGED` anchor line. As everywhere in the lock, a theorem contributes its
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
  names (without macro scopes, which depend on earlier declarations of the
  module) and binder infos of its type; its reducibility status; and whether
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
- **Outside v2.** The entry hash does not see a change to a declaration
  outside the v2 libraries that the entry uses (Model, Mathlib). For an
  engine entry the lock line of its anchor sees it; a `CHANGED` anchor line
  with no `CHANGED` entry means such a change. A Model declaration that
  only Kit entries use is seen by neither the lock nor the manifest; it is
  frozen by rule only.

## Anchors

Never edit `anchor`. A later stage adds its engine entries to this file
and one new anchor def in a new module under `AvailableChainFramework/V2/`
(for example `anchor_2b` in `Anchor2b.lean`, imported by the Framework
root); `V2Manifest --anchor` prints its body (the engine entries that no
anchor covers yet). The lock change is then ADDED only. An engine entry is
anchored if it is in the closure of some non-generated declaration of a
module under `AvailableChainFramework.V2`.

Put new declarations AFTER the existing declarations of a 2a module, or in a
new module. Lean reuses a matcher of the same shape within a module, first
come first served: a declaration inserted above a 2a declaration can take
over its matcher, and the ADD then gives `CHANGED` lines.

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
inductive AvailableChain.V2.Auth 6a648fefaf07db83
ctor AvailableChain.V2.Auth.seat e620f6585053119f
ctor AvailableChain.V2.Auth.none 26cd8de5c3579df9
def AvailableChain.V2.instDecidableEqAuth cb6e363e7b392734
def AvailableChain.V2.instDecidableEqAuth.decEq a0344c6e54f9fd4b
def AvailableChain.V2.instReprAuth bb347e931a7e66ba
def AvailableChain.V2.instReprAuth.repr 31fba12b7e0d0ddb
structure AvailableChain.V2.Signed 83f9b62e6e5cf26f
ctor AvailableChain.V2.Signed.mk a3fe01e1c5d714b9
def AvailableChain.V2.Signed.auth 599d3904350e41ee
def AvailableChain.V2.Signed.payload e170cdc9151753df
def AvailableChain.V2.instDecidableEqSigned 8c6004fed206f7d9
def AvailableChain.V2.instDecidableEqSigned.decEq e5ef0f38b5da0b07
def AvailableChain.V2.instReprSigned fd8687e973ad88a3
def AvailableChain.V2.instReprSigned.repr ffab279525ec2b5c
```

### `AvailableChainEngineV2.Engine.Run`

```text
inductive AvailableChain.V2.Event 17fc49f3e3d44f34
ctor AvailableChain.V2.Event.restart 92474f35a882e910
ctor AvailableChain.V2.Event.tick ee6bed1e67349f17
ctor AvailableChain.V2.Event.deliver 0d3fe5a920053bc5
def AvailableChain.V2.instDecidableEqEvent 0785c5691b6deb98
def AvailableChain.V2.instDecidableEqEvent.decEq a437f8c390ea8f2f
def AvailableChain.V2.Event.time f3599702b42d1edc
def AvailableChain.V2.Event.node 0c62d0f728af2931
def AvailableChain.V2.Event.object? ade613cc320bdfbe
def AvailableChain.V2.Event.phase 05885ef1b3d485fd
def AvailableChain.V2.Event.key d37ad9c14541145e
def AvailableChain.V2.World f57ade52b24cfa64
def AvailableChain.V2.World.init d7b4a3e9d1a2fd65
structure AvailableChain.V2.Run 3370ef0fe40282df
ctor AvailableChain.V2.Run.mk b16813fa5e4b250f
def AvailableChain.V2.Run.honest b543988cf8f78c51
def AvailableChain.V2.Run.horizon c427750f04e53280
def AvailableChain.V2.Run.events 6e2e0cc268bc42ae
def AvailableChain.V2.Run.seatOf e59f8db73483d969
def AvailableChain.V2.Run.input fc25a5b207e3182e
def AvailableChain.V2.Run.ownSeats d5ffb9d7ac08af47
def AvailableChain.V2.tick b74a0ff2bc5eeda8
def AvailableChain.V2.World.step 61c3888991c3c786
def AvailableChain.V2.Run.stateBefore e69ee50b1945f7c2
def AvailableChain.V2.Run.stateBeforeTime bd9ac288e06e8b73
def AvailableChain.V2.Run.readAt 53a7e52b5bd60b7a
def AvailableChain.V2.Run.final 9f4cdb4ca6e8a088
def AvailableChain.V2.Run.emitsAt 5b01dad2195a238d
def AvailableChain.V2.Run.tickIdx? 9545d8696d6d22fb
def AvailableChain.V2.Run.emittedAt 3aa3dd0aad30ba1c
def AvailableChain.V2.Run.emits 12bf691cf3d671fe
def AvailableChain.V2.Run.processes 121f6339a5889215
def AvailableChain.V2.Run.handlesAt 7fbc1790ce987ec8
def AvailableChain.V2.Run.acceptsAt 92a8b377e1548f5d
def AvailableChain.V2.Run.holder ae5cf5c47d97cca2
theorem AvailableChain.V2.Run.stateBefore_succ 3688d99e3a927567
theorem AvailableChain.V2.Run.step_tick_eq e0484c3c3467cc7b
theorem AvailableChain.V2.tick_decomp 4bd8a1d808ebf05a
theorem AvailableChain.V2.tick_asleep 65bcba79778cef6c
theorem AvailableChain.V2.Run.tickIdx?_spec 10fe4d974d6f153a
theorem AvailableChain.V2.Run.emittedAt_eq_emitsAt 2bc184d0192f87ba
theorem AvailableChain.V2.Run.mem_emittedAt_iff_emits dcef2fd0150686c0
```

### `AvailableChainEngineV2.Engine.Spec`

```text
structure AvailableChain.V2.ProtocolSpec 391a0211a41fb997
ctor AvailableChain.V2.ProtocolSpec.mk 4a1a2fcce486f463
def AvailableChain.V2.ProtocolSpec.State 5d0832010f8f405c
def AvailableChain.V2.ProtocolSpec.Label ba2efb1ee38fd904
def AvailableChain.V2.ProtocolSpec.seats d65b172f946af29a
def AvailableChain.V2.ProtocolSpec.Payload a41f8aaebbd3cd47
def AvailableChain.V2.ProtocolSpec.Durable 7da03717eddc1992
def AvailableChain.V2.ProtocolSpec.init de1d7455b740fdcd
def AvailableChain.V2.ProtocolSpec.clock 47100d518da5f759
def AvailableChain.V2.ProtocolSpec.actTime 494fcf07963dae41
def AvailableChain.V2.ProtocolSpec.duties a92ebf6137196ac4
theorem AvailableChain.V2.ProtocolSpec.duties_spec 07be43cb00f8d24e
theorem AvailableChain.V2.ProtocolSpec.duties_nodup 0b7e32802ace2380
def AvailableChain.V2.ProtocolSpec.act 926481b001667b94
def AvailableChain.V2.ProtocolSpec.gossip 1d66035a0d8262dd
def AvailableChain.V2.ProtocolSpec.process 73833b971950db9b
def AvailableChain.V2.ProtocolSpec.selfVisible 851a2e4a6486e12a
def AvailableChain.V2.ProtocolSpec.recordOwn f230b0937fa2942b
def AvailableChain.V2.ProtocolSpec.durable 4e9f5cee68bbbeea
def AvailableChain.V2.ProtocolSpec.restore 05fdecc7025c21c1
def AvailableChain.V2.ProtocolSpec.wellFormed 3710e54b9cc5e293
def AvailableChain.V2.ProtocolSpec.depsPresent eea4ea41129c2e94
def AvailableChain.V2.ProtocolSpec.processed aa7908941dec9f5d
def AvailableChain.V2.ProtocolSpec.excludes 9cef1da2422800a9
def AvailableChain.V2.ProtocolSpec.handles 367cc2ca1656622b
def AvailableChain.V2.ProtocolSpec.carries d2ea87f7a9de6d3a
def AvailableChain.V2.ProtocolSpec.Object bd98c959f9709ec3
def AvailableChain.V2.ProtocolSpec.objSelfVisible be72efe7d7d4a2a5
```

### `AvailableChainEngineV2.Conditions.Committees`

```text
structure AvailableChain.V2.LabelFamilies eb378268eb8e2019
ctor AvailableChain.V2.LabelFamilies.mk 84834f0cbb249413
def AvailableChain.V2.LabelFamilies.ap a66fbf4d74f37651
def AvailableChain.V2.LabelFamilies.fresh 1e7235d276af0c34
def AvailableChain.V2.LabelFamilies.linked fba012ebd2d71b6d
def AvailableChain.V2.CStar 06326ca972828e12
def AvailableChain.V2.Linked d1000b2faefeea3d
def AvailableChain.V2.SingleSeat 098fbb9319ae6d0c
theorem AvailableChain.V2.Linked.toCStar 017bcc0c5226a9af
theorem AvailableChain.V2.CStar.seats_eq 94c06fc0f2ef8ba8
```

### `AvailableChainEngineV2.Conditions.Delivery`

```text
structure AvailableChain.V2.PartialSynchrony 6c5f8faee5991ae5
ctor AvailableChain.V2.PartialSynchrony.mk 2c07f39edb4a1390
theorem AvailableChain.V2.PartialSynchrony.broadcast 3fbbbc22d26f72d8
theorem AvailableChain.V2.PartialSynchrony.relay abeb664554bf897a
structure AvailableChain.V2.HealthyPrefixDelivery d42df44c8517b350
ctor AvailableChain.V2.HealthyPrefixDelivery.mk 181ebddcc213902b
theorem AvailableChain.V2.HealthyPrefixDelivery.broadcast 3f6657be25dfb184
theorem AvailableChain.V2.HealthyPrefixDelivery.relay 4ddef8327cc34828
```

### `AvailableChainEngineV2.Conditions.Interface`

```text
structure AvailableChain.V2.Interface d25a81c97f6adcbf
ctor AvailableChain.V2.Interface.mk a80ad66ae61fcda1
def AvailableChain.V2.Interface.confirmed be1d250edf57272a
def AvailableChain.V2.Interface.stable f598f599de0fbcdf
def AvailableChain.V2.Interface.block 18038cb7ce3b0fce
def AvailableChain.V2.Interface.opening 7aec55ff60182c46
def AvailableChain.V2.Interface.propLabel 9128e3fe443de95e
theorem AvailableChain.V2.Interface.propLabel_single 4766579f07ff654c
theorem AvailableChain.V2.Interface.propLabel_injective 0fc741c981ac3b8f
def AvailableChain.V2.proposalTime b4243682e4a34ebf
def AvailableChain.V2.propSeat 476242fb6623604e
def AvailableChain.V2.proposerOf 359fce58f245c1fc
theorem AvailableChain.V2.eq_propSeat 3397a97d804900f6
theorem AvailableChain.V2.holder_propLabel 27ec6bd7f446f776
def AvailableChain.V2.Output a8967dbc86e9ed88
def AvailableChain.V2.outputAt 570216ff32904b17
def AvailableChain.V2.BlockInRun 0b71fbf3d775323a
def AvailableChain.V2.RootInjective ec4fa66dac4b0c45
```

### `AvailableChainEngineV2.Conditions.Schedule`

```text
def AvailableChain.V2.PublicTime b66e00481417d389
structure AvailableChain.V2.ScheduleWellFormed 5e6d43e8916f59d8
ctor AvailableChain.V2.ScheduleWellFormed.mk 380c4d099589e15e
theorem AvailableChain.V2.ScheduleWellFormed.horizon_nonneg 1f9b37d96351c9ec
theorem AvailableChain.V2.ScheduleWellFormed.sorted 03dc3022a0048124
theorem AvailableChain.V2.ScheduleWellFormed.nodup cdf58bfc7678e96a
theorem AvailableChain.V2.ScheduleWellFormed.in_horizon b3aa25056fa74d23
theorem AvailableChain.V2.ScheduleWellFormed.honest_only 848b51ee5a34aba0
theorem AvailableChain.V2.ScheduleWellFormed.tick_public a89081f33df54e60
theorem AvailableChain.V2.ScheduleWellFormed.tick_total 31a8369576e45f31
def AvailableChain.V2.NoRestart e61d0ed64ee146fb
def AvailableChain.V2.restartFree 54d237306430298a
structure AvailableChain.V2.DeliveryWellFormed 159f5dbfb73d1586
ctor AvailableChain.V2.DeliveryWellFormed.mk 8c12e92ebe3fd5cc
theorem AvailableChain.V2.DeliveryWellFormed.wire 708a9114dd13ece0
theorem AvailableChain.V2.DeliveryWellFormed.deps 246ff9fad8d29a5b
theorem AvailableChain.V2.DeliveryWellFormed.fresh 23fb484c57c9aac4
structure AvailableChain.V2.UnforgeableSignatures 0667ce76728c329a
ctor AvailableChain.V2.UnforgeableSignatures.mk d8eacfc75bb9c4fb
theorem AvailableChain.V2.UnforgeableSignatures.unforgeable 18cc6ba937b89482
theorem AvailableChain.V2.UnforgeableSignatures.carried b8e0c69bb1bf8864
structure AvailableChain.V2.ExecutionValid b07e3ffaa028d151
theorem AvailableChain.V2.ExecutionValid.toDeliveryWellFormed 066dd49ec3db9df7
theorem AvailableChain.V2.ExecutionValid.toScheduleWellFormed 7bde498b7f2ec00b
theorem AvailableChain.V2.ExecutionValid.toUnforgeableSignatures dd22d8e9c9245021
ctor AvailableChain.V2.ExecutionValid.mk 1132fa011975a4fd
def AvailableChain.V2.SelfDelivery 79998bf4ec94005c
theorem AvailableChain.V2.ScheduleWellFormed.mem_emittedAt_iff_emits d923a39d892bd5a1
theorem AvailableChain.V2.restartFree_refl 5f03854e731d9a71
theorem AvailableChain.V2.not_restartFree_succ_iff b8a5c09d141b0597
theorem AvailableChain.V2.restartFree.mono 293ff6bbd0b42da4
theorem AvailableChain.V2.restartFree.append 13e8f02bf1446ac3
theorem AvailableChain.V2.NoRestart.restartFree a600ca784a52ed6c
```

### `AvailableChainEngineV2.Laws.Hooks`

```text
structure AvailableChain.V2.HooksSound 0eeb035670cbe6c8
ctor AvailableChain.V2.HooksSound.mk 9125820adcd56b65
theorem AvailableChain.V2.HooksSound.excludes_inert b853954b9d6b84dc
theorem AvailableChain.V2.HooksSound.excludes_stable 25a373072f8e6caf
theorem AvailableChain.V2.HooksSound.processed_stable d90c55b1a8f0743e
theorem AvailableChain.V2.HooksSound.deps_stable 180e3c2f07ffaa0a
theorem AvailableChain.V2.HooksSound.handles_carries 7671f426d4ee5b31
theorem AvailableChain.V2.HooksSound.recordOwn_processed b78d1d21d28bbe4d
theorem AvailableChain.V2.HooksSound.recordOwn_deps cdb2ef79741a8cb4
theorem AvailableChain.V2.HooksSound.recordOwn_excludes 9e57d80f39203d16
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_processed 34e3aec93302c3e4
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_deps 8dfeff817fda3f03
theorem AvailableChain.V2.HooksSound.foldl_recordOwn_excludes 66d537a4d76ab19f
theorem AvailableChain.V2.HooksSound.processed_tick b4cdc9c8edec3973
theorem AvailableChain.V2.HooksSound.deps_tick 005050524cc5138c
theorem AvailableChain.V2.HooksSound.excludes_tick bd7375c464377727
```

### `AvailableChainEngineV2.Laws.Isolation`

```text
def AvailableChain.V2.LabelFamilies.APObject 1b8b24b15df87550
theorem AvailableChain.V2.LabelFamilies.apObject_seat ca38e22cfe53fc12
theorem AvailableChain.V2.LabelFamilies.apObject_none f4e3608a8e338f01
structure AvailableChain.V2.Isolation 0361f6718bd4db7e
ctor AvailableChain.V2.Isolation.mk ea22f6fde5435804
def AvailableChain.V2.Isolation.Base 7a22733b1f66457f
def AvailableChain.V2.Isolation.base fd6ce3ec38950c16
def AvailableChain.V2.Isolation.clockB defa80c444883e11
theorem AvailableChain.V2.Isolation.clock_base 922284d6b4d09823
def AvailableChain.V2.Isolation.processB 132ea22abaa59721
theorem AvailableChain.V2.Isolation.process_base c50ac4b9ce413a4e
theorem AvailableChain.V2.Isolation.recordOwn_base fdf223dc12e74790
def AvailableChain.V2.Isolation.actB fe29eda3691a58c2
theorem AvailableChain.V2.Isolation.act_base b6b7fea7c679749c
def AvailableChain.V2.Isolation.gossipB 524fdf376f84131e
theorem AvailableChain.V2.Isolation.gossip_base 0cb7c7a45233ffd2
def AvailableChain.V2.Isolation.depsB dfcbe16c6969a475
def AvailableChain.V2.Isolation.processedB 6fbe110658ba7a22
def AvailableChain.V2.Isolation.excludesB e64a0db36217b453
def AvailableChain.V2.Isolation.handlesB 8467199b05bfc9b3
theorem AvailableChain.V2.Isolation.hooks_base 9c1d585e4c71080f
theorem AvailableChain.V2.Isolation.separation d4bc4cf1cb35a087
theorem AvailableChain.V2.Isolation.foldl_recordOwn_base c91ee9675dc3da2d
theorem AvailableChain.V2.Isolation.base_tick c0c22d2aea5123c4
theorem AvailableChain.V2.Isolation.hooks_congr a2f083c8ca8e30f3
theorem AvailableChain.V2.Isolation.not_ap_of_selfVisible 4f65165a75d4cae3
```

### `AvailableChainEngineV2.Laws.Outputs`

```text
structure AvailableChain.V2.OutputsFactor 21161da9096cae75
ctor AvailableChain.V2.OutputsFactor.mk 9b37b19a62ad4a71
def AvailableChain.V2.OutputsFactor.confirmedB 5700d441b06d0403
theorem AvailableChain.V2.OutputsFactor.confirmed_base 13cbd2e246e09488
def AvailableChain.V2.OutputsFactor.stableB 425469626f269a78
theorem AvailableChain.V2.OutputsFactor.stable_base 9e87e2e962ce83fc
theorem AvailableChain.V2.OutputsFactor.confirmed_recordOwn ec2a2eb1c982659e
theorem AvailableChain.V2.OutputsFactor.stable_recordOwn 84a321b1acf42afa
theorem AvailableChain.V2.OutputsFactor.confirmed_tick e82140a78c005eae
theorem AvailableChain.V2.OutputsFactor.stable_tick 10e6f98665fe1081
```

### `AvailableChainEngineV2.Laws.SelfDelivery`

```text
structure AvailableChain.V2.EmitOk d1dfe10953689aee
ctor AvailableChain.V2.EmitOk.mk a61e51221cf7d516
theorem AvailableChain.V2.EmitOk.wire 880383e26cf194fd
theorem AvailableChain.V2.EmitOk.deps f4d8c804752296af
theorem AvailableChain.V2.EmitOk.fresh c82afd38c8532742
theorem AvailableChain.V2.EmitOk.noCarried 5b7073ab840217fd
theorem AvailableChain.V2.Run.holder_of_mem_tick b53acae5d64b5601
theorem AvailableChain.V2.World.step_apply_of_node_ne 95e7c8dae8d2afd1
theorem AvailableChain.V2.Run.stateBefore_eq_of_node_ne 8b46200c23ba8596
theorem AvailableChain.V2.selfDelivery_admissible 350d8a1e973b20aa
theorem AvailableChain.V2.Run.getElem?_snoc_of_lt 1359dbcf8d8a0d34
theorem AvailableChain.V2.Run.tick_snoc 0def792c9e011e1d
theorem AvailableChain.V2.Run.stateBefore_snoc_of_le 403accfc9a82d5e7
theorem AvailableChain.V2.Run.emitsAt_snoc_of_lt b2d62736072ec17e
theorem AvailableChain.V2.Run.emits_snoc f0ba9efdf9c2acd8
theorem AvailableChain.V2.EmitOk.snoc 8fc39a009b014396
theorem AvailableChain.V2.ExecutionValid.snoc_selfDelivery bf61c2187dcc1ebc
```

## Kit v2 (frozen by rule, not locked)

### `AvailableChainKitV2.ClockLaws`

```text
structure AvailableChain.V2.Engine.ClockLaws e6e214315c65e225
ctor AvailableChain.V2.Engine.ClockLaws.mk 93bb2724cab51b8e
def AvailableChain.V2.Engine.ClockLaws.now cebca394e7f00a5a
theorem AvailableChain.V2.Engine.ClockLaws.init 80af1315944ce1da
theorem AvailableChain.V2.Engine.ClockLaws.clock 0107374e4bd3e6b4
theorem AvailableChain.V2.Engine.ClockLaws.process 6449c5c328f3416a
theorem AvailableChain.V2.Engine.ClockLaws.recordOwn_now c2e8ee0b50782b7f
theorem AvailableChain.V2.Engine.ClockLaws.now_foldl_recordOwn 2d2bdcf845eb0000
theorem AvailableChain.V2.Engine.ClockLaws.now_tick 6b175aea52fe4ac4
```

### `AvailableChainKitV2.Emission`

```text
theorem AvailableChain.V2.Engine.mem_tick_seat_iff fac256bdf3e6a2aa
theorem AvailableChain.V2.Engine.ownSeats_bijSeat 19866508baa82dc5
theorem AvailableChain.V2.Engine.emits_bijSeat 1c12b6ab0fefe868
theorem AvailableChain.V2.Engine.linked_index_stable 34d851834d75e445
def AvailableChain.V2.Engine.ownReleasedAt e722fa65923efa3a
def AvailableChain.V2.Engine.ownReleased a1508b756e2b7be6
theorem AvailableChain.V2.Engine.ownReleased_self ef1e2c61d686e391
theorem AvailableChain.V2.Engine.ownReleased_succ 2131433d10647550
theorem AvailableChain.V2.Engine.ownRecord_fold_interval a7556a63265d3602
theorem AvailableChain.V2.Engine.ownRecord_fold 0934842b570241ff
```

### `AvailableChainKitV2.EngineClock`

```text
theorem AvailableChain.V2.Engine.stateBefore_now_source 9c80fcceff232fd8
theorem AvailableChain.V2.Engine.stateBefore_now_source_noRestart 52661bea6807182e
theorem AvailableChain.V2.Engine.stateBefore_now_le_event 3b49b87b9abe02b9
theorem AvailableChain.V2.Engine.stateBefore_now_le_event_noRestart 72244c16c0ce21b4
theorem AvailableChain.V2.Engine.stateBefore_now_mono a5113e8e573379f2
theorem AvailableChain.V2.Engine.stateBefore_now_mono_noRestart 94ba60b4f7a08758
theorem AvailableChain.V2.Engine.delivery_now_ge_public 21b4b2a18edf7c8d
theorem AvailableChain.V2.Engine.stateBefore_invariant 7c1e2e0a8066a4d7
theorem AvailableChain.V2.Engine.stateBefore_invariant_noRestart a2040e41514c5b5b
theorem AvailableChain.V2.Engine.stateBefore_stable_clock 96d0b18a4cffe72d
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_restore 2dc657a0a55cd699
theorem AvailableChain.V2.Engine.stateBefore_stable_clock_noRestart 0f5d3314fc7c1d7b
theorem AvailableChain.V2.Engine.clock_field_origin 990437b00296ba4f
theorem AvailableChain.V2.Engine.clock_field_origin_noRestart ca95c0f2f9d37f7f
theorem AvailableChain.V2.Engine.clock_field_origin_of_subset c8458d33c65921ae
theorem AvailableChain.V2.Engine.stateBefore_field_prefix 7b725593ef3e900a
theorem AvailableChain.V2.Engine.stateBefore_field_prefix_restore 11b0e702792d7c40
```

### `AvailableChainKitV2.Execution`

```text
theorem AvailableChain.V2.Engine.eventIndex_lt_of_time_lt 1a3206c09108d300
theorem AvailableChain.V2.Engine.time_le_of_key_le 22433293ffefed02
theorem AvailableChain.V2.Engine.filter_eq_take db553376e1ac6489
theorem AvailableChain.V2.Engine.filter_false_of_index_ge fcbca2291532b3d7
theorem AvailableChain.V2.Engine.index_lt_read_length_iff 1e9a8711f9785fea
theorem AvailableChain.V2.Engine.read_length_mono fad77e7e86d41d54
theorem AvailableChain.V2.Engine.tick_index_lt_delivery 61c606503439616e
theorem AvailableChain.V2.Engine.readAt_eq_stateBefore a94a03f005a5e010
theorem AvailableChain.V2.Engine.stateBefore_other_node eabe2539f63fff91
theorem AvailableChain.V2.Engine.stateBefore_tick_eq_stateBeforeTime e61c627380ab3c46
```

### `AvailableChainKitV2.RunCheck`

```text
def AvailableChain.V2.Engine.allTicks 56580aca6fd9de56
def AvailableChain.V2.Engine.allDeliveries 4f158812c9be3e2e
theorem AvailableChain.V2.Engine.allTicks_spec f7d4d600c708b01a
theorem AvailableChain.V2.Engine.allDeliveries_spec 37a4864a942c2d62
def AvailableChain.V2.Engine.emittedBy 51a84fca0f935606
theorem AvailableChain.V2.Engine.emittedBy_spec f0f5eb5ccdc7c0ad
```

### `AvailableChainKitV2.Stable`

```text
theorem AvailableChain.V2.Engine.foldl_recordOwn_preserve 6853979b58f7aa6d
theorem AvailableChain.V2.Engine.tick_preserve 25dd1cd1f8575d64
theorem AvailableChain.V2.Engine.recordOwn_preserve_of_base 32bb8b30a9a25510
theorem AvailableChain.V2.Engine.stateBefore_step_induction f3b1b9fd91dc85ac
theorem AvailableChain.V2.Engine.stateBefore_stable cbda5e2adf3c1d8a
```

### `AvailableChainEngineV2.Engine.Duty.Lift`

```text
def AvailableChain.V2.ProtocolSpec.toD 16c3e6e8219141f2
def AvailableChain.V2.Run.toD a1e5da756c537df7
def AvailableChain.V2.D.Run.ofD fbc88297aa4409ec
theorem AvailableChain.V2.D.Run.toD_ofD e7d07f8d93d65421
theorem AvailableChain.V2.D.Run.ofD_toD 4734e8439df483cb
theorem AvailableChain.V2.D.dutiesInjectiveAt_toD 34d1686872cfe992
theorem AvailableChain.V2.D.objSelfVisible_toD ac5e19223b5a4e97
theorem AvailableChain.V2.D.tick_toD 157609e740bcd9dc
theorem AvailableChain.V2.D.world_init_toD 1a46899545c6d9d2
theorem AvailableChain.V2.D.world_step_toD e9710b69b08b1d35
theorem AvailableChain.V2.D.stateBefore_toD 4291cd42172a44b9
theorem AvailableChain.V2.D.stateBeforeTime_toD 217f48efb02c5032
theorem AvailableChain.V2.D.readAt_toD 202845b0b09362e9
theorem AvailableChain.V2.D.final_toD 750f2f3041e53382
theorem AvailableChain.V2.D.emitsAt_toD c5cbd8011eb39974
theorem AvailableChain.V2.D.tickIdx_toD 6ffa63febd7353c0
theorem AvailableChain.V2.D.emittedAt_toD 133216a53ce217c6
theorem AvailableChain.V2.D.emits_toD 9eb2635c1eb17e61
theorem AvailableChain.V2.D.processes_toD ad800ba0bebd0de6
theorem AvailableChain.V2.D.handlesAt_toD afb4eddbcd8e833b
theorem AvailableChain.V2.D.acceptsAt_toD a246dc17134f729a
theorem AvailableChain.V2.D.holder_toD 6ee8ccdcbafd0933
```

### `AvailableChainEngineV2.Engine.Duty.Run`

```text
def AvailableChain.V2.D.World aee2e665f8f16de5
def AvailableChain.V2.D.World.init d98f1f908959e994
structure AvailableChain.V2.D.Run 334e4973d0e7f363
ctor AvailableChain.V2.D.Run.mk 79a8b5a590e428df
def AvailableChain.V2.D.Run.honest 0c7144ea2528b7da
def AvailableChain.V2.D.Run.horizon 6ef49daea59a6bda
def AvailableChain.V2.D.Run.events 8c675a79f521a9ed
def AvailableChain.V2.D.Run.seatOf 455edf6096f945ed
def AvailableChain.V2.D.Run.input 5ccc8c02da80bfe7
def AvailableChain.V2.D.Run.ownSeats 6a0b5de4b969977a
def AvailableChain.V2.D.tick 08b3d867be4fbbf7
def AvailableChain.V2.D.World.step a0870cb3e90ff30c
def AvailableChain.V2.D.Run.stateBefore 59ea9481456eed4b
def AvailableChain.V2.D.Run.stateBeforeTime 8a12dc09f5181b70
def AvailableChain.V2.D.Run.readAt e5117228e20bf97b
def AvailableChain.V2.D.Run.final f650e873373a3260
def AvailableChain.V2.D.Run.emitsAt ebee2f7f38989a89
def AvailableChain.V2.D.Run.tickIdx? 1149d050c3cad0aa
def AvailableChain.V2.D.Run.emittedAt 760910343a3f0d32
def AvailableChain.V2.D.Run.emits 77501c97e138a270
def AvailableChain.V2.D.Run.processes b2a749b57f278476
def AvailableChain.V2.D.Run.handlesAt 86414bf8a48e6a67
def AvailableChain.V2.D.Run.acceptsAt f34aa92642d1fe3a
def AvailableChain.V2.D.Run.holder 9981834b855ce4a8
theorem AvailableChain.V2.D.Run.stateBefore_succ 18bb12ac06adec2b
theorem AvailableChain.V2.D.Run.step_tick_eq 24e812b0313d675a
theorem AvailableChain.V2.D.tick_decomp 41e3e174d4c45054
theorem AvailableChain.V2.D.tick_asleep 1dd2eaea3df2ba52
theorem AvailableChain.V2.D.Run.tickIdx?_spec d53522742368aa65
theorem AvailableChain.V2.D.Run.emittedAt_eq_emitsAt 105d84f903758020
theorem AvailableChain.V2.D.Run.mem_emittedAt_iff_emits 3bc4f56865194ebe
```

### `AvailableChainEngineV2.Engine.Duty.Spec`

```text
structure AvailableChain.V2.ProtocolSpecD 0b3fc7d950fa5797
ctor AvailableChain.V2.ProtocolSpecD.mk 12247911796e5abb
def AvailableChain.V2.ProtocolSpecD.State b1f065d22d7c0ffd
def AvailableChain.V2.ProtocolSpecD.Label 7701b3e170ef83f9
def AvailableChain.V2.ProtocolSpecD.Duty 48cc2f91dab5053f
def AvailableChain.V2.ProtocolSpecD.signLabel d72fa72caa7e17a8
def AvailableChain.V2.ProtocolSpecD.seats 249bffb3c1298df4
def AvailableChain.V2.ProtocolSpecD.Payload 630bc02eb07f2c51
def AvailableChain.V2.ProtocolSpecD.Durable ee65ad31d33d849c
def AvailableChain.V2.ProtocolSpecD.init fb4973d56b383cd4
def AvailableChain.V2.ProtocolSpecD.clock 3b83575cc02b1876
def AvailableChain.V2.ProtocolSpecD.actTime 469141c26bd279ab
def AvailableChain.V2.ProtocolSpecD.duties 222bed9d5a086f6c
theorem AvailableChain.V2.ProtocolSpecD.duties_spec e030391cda4a238c
theorem AvailableChain.V2.ProtocolSpecD.duties_nodup 1f56dc6a804ff933
def AvailableChain.V2.ProtocolSpecD.act 2db8feba88710b9f
def AvailableChain.V2.ProtocolSpecD.gossip 5c5fe19e71cf3faa
def AvailableChain.V2.ProtocolSpecD.process 9983a74c2b501a76
def AvailableChain.V2.ProtocolSpecD.selfVisible 2458522c9533290a
def AvailableChain.V2.ProtocolSpecD.recordOwn 7128ac1e268c9ffc
def AvailableChain.V2.ProtocolSpecD.durable 5ce1f7962ba0448d
def AvailableChain.V2.ProtocolSpecD.restore 0b2fb7e7753f40b4
def AvailableChain.V2.ProtocolSpecD.wellFormed 9cb4c05c7ceabf7f
def AvailableChain.V2.ProtocolSpecD.depsPresent 9c174dc2fa4b24d9
def AvailableChain.V2.ProtocolSpecD.processed 7756723aa5d63b8f
def AvailableChain.V2.ProtocolSpecD.excludes 48ff89f62a02c5cd
def AvailableChain.V2.ProtocolSpecD.handles f0972b1f7ca4758e
def AvailableChain.V2.ProtocolSpecD.carries fc476687e62b3f90
def AvailableChain.V2.ProtocolSpecD.Object 4672b3759d46daee
def AvailableChain.V2.ProtocolSpecD.objSelfVisible 3bb2df72707cd207
```

### `AvailableChainEngineV2.Conditions.Duty.Committees`

```text
structure AvailableChain.V2.D.LabelFamilies d5fb11302869f4d1
ctor AvailableChain.V2.D.LabelFamilies.mk 880221d62741ec57
def AvailableChain.V2.D.LabelFamilies.ap 9dbfb7f975a4efb3
def AvailableChain.V2.D.LabelFamilies.fresh 7aa72445110192e2
def AvailableChain.V2.D.LabelFamilies.linked 6150641d5e762aab
def AvailableChain.V2.D.CStar d2614f389b8f0423
def AvailableChain.V2.D.Linked 2d98d27ca2d70a2b
def AvailableChain.V2.D.SingleSeat efee0c7763a01829
theorem AvailableChain.V2.D.Linked.toCStar 896816c5d815faf3
theorem AvailableChain.V2.D.CStar.seats_eq ffc5ffde96979911
```

### `AvailableChainEngineV2.Conditions.Duty.Delivery`

```text
structure AvailableChain.V2.D.PartialSynchrony 562154f06bfd5a81
ctor AvailableChain.V2.D.PartialSynchrony.mk 9c95a605578c9866
theorem AvailableChain.V2.D.PartialSynchrony.broadcast_emitted 69ab8c729152fa93
theorem AvailableChain.V2.D.PartialSynchrony.relay_accepted c8f0be2754928322
structure AvailableChain.V2.D.HealthyPrefixDelivery 34a8e54fc21811db
ctor AvailableChain.V2.D.HealthyPrefixDelivery.mk b7cfa6cb778ed7fe
theorem AvailableChain.V2.D.HealthyPrefixDelivery.broadcast_emitted 717a4a6d13ab4cc2
theorem AvailableChain.V2.D.HealthyPrefixDelivery.relay_accepted 7611ac184656be5a
```

### `AvailableChainEngineV2.Conditions.Duty.Duties`

```text
def AvailableChain.V2.D.DutiesInjectiveAt d1be0598c5bc380b
```

### `AvailableChainEngineV2.Conditions.Duty.Interface`

```text
structure AvailableChain.V2.D.Interface 1d0ba080789483d8
ctor AvailableChain.V2.D.Interface.mk 3311c4b9de153174
def AvailableChain.V2.D.Interface.confirmed 1715fdd410a0d35c
def AvailableChain.V2.D.Interface.stable 93d11a0c80ee7fa1
def AvailableChain.V2.D.Interface.block a0d381a91c7d8e82
def AvailableChain.V2.D.Interface.opening 8ecad9e97676679c
def AvailableChain.V2.D.Interface.propLabel daa2d629e1292639
def AvailableChain.V2.D.Interface.propDuty b74095269e2b25e8
theorem AvailableChain.V2.D.Interface.propDuty_label a2cc26b88c869b53
theorem AvailableChain.V2.D.Interface.propLabel_single 055c18d54333bd27
theorem AvailableChain.V2.D.Interface.propLabel_injective 62a29da2681ac9ac
def AvailableChain.V2.D.proposalTime 0159de25de11d191
def AvailableChain.V2.D.propSeat 2d2a51b028266201
def AvailableChain.V2.D.proposerOf ba9cd4845bf94b83
theorem AvailableChain.V2.D.eq_propSeat b9ef58d99ad76ca6
theorem AvailableChain.V2.D.holder_propLabel a736d9d7890ba8ce
def AvailableChain.V2.D.Output fbb74f15a1c1780f
def AvailableChain.V2.D.outputAt a4c36e19e9aa16a8
def AvailableChain.V2.D.BlockInRun c9f042c525957db3
def AvailableChain.V2.D.RootInjective be817fa0bd8bf6c3
```

### `AvailableChainEngineV2.Conditions.Duty.Lift`

```text
def AvailableChain.V2.LabelFamilies.toD d61522f59a8928a3
def AvailableChain.V2.Interface.toD 7c3a5a5428751ff5
theorem AvailableChain.V2.D.apObject_toD_iff d4851d9aa1e0cc47
def AvailableChain.V2.Isolation.toD e14787ba60639bee
def AvailableChain.V2.D.Isolation.ofD 81d8e2e92bc3eb0c
def AvailableChain.V2.D.Interface.ofD 33bb5f0b2c5a5bac
theorem AvailableChain.V2.D.interface_toD_iff 5822b10e49d60a99
theorem AvailableChain.V2.D.isolation_toD_iff 8614ccea8e686107
theorem AvailableChain.V2.D.cStar_toD_iff be6c3c4e418b694f
theorem AvailableChain.V2.D.linked_toD_iff db74ac280b869711
theorem AvailableChain.V2.D.singleSeat_toD_iff 048b2fb99982f071
theorem AvailableChain.V2.D.noRestart_toD_iff 952c9bb0bd120985
theorem AvailableChain.V2.D.restartFree_toD_iff c5848bbff976cd01
theorem AvailableChain.V2.D.proposalTime_toD 97949804aedbf370
theorem AvailableChain.V2.D.proposerOf_toD b7bf6cf8d89dbc6c
theorem AvailableChain.V2.D.scheduleWellFormed_toD_iff c9815e97e507997c
theorem AvailableChain.V2.D.deliveryWellFormed_toD_iff 3dd7e4e0998303f2
theorem AvailableChain.V2.D.unforgeableSignatures_toD_iff 5cdece89f0969000
theorem AvailableChain.V2.D.partialSynchrony_toD_iff b94466b75a489afb
theorem AvailableChain.V2.D.healthyPrefixDelivery_toD_iff 46c211ff4c9d60d5
theorem AvailableChain.V2.D.emitOk_toD_iff beb27625191d2094
theorem AvailableChain.V2.D.executionValid_toD_iff 8cee386e30664a7a
theorem AvailableChain.V2.D.selfDelivery_toD_iff 1af0a06a3c234f4b
theorem AvailableChain.V2.D.blockInRun_toD_iff 0d5e8796e58bf92c
theorem AvailableChain.V2.D.rootInjective_toD_iff 4172763c5f6008f4
theorem AvailableChain.V2.D.outputAt_toD 5940b8b74a528ea9
theorem AvailableChain.V2.D.holder_of_mem_tick_toD 661dd7a1310e28a7
theorem AvailableChain.V2.D.outputsFactor_toD_iff 24f8ea3f4fe11703
theorem AvailableChain.V2.D.hooksSound_toD_iff 2f478e71da887ff1
```

### `AvailableChainEngineV2.Conditions.Duty.Schedule`

```text
structure AvailableChain.V2.D.ScheduleWellFormed b90d15cb454511f3
ctor AvailableChain.V2.D.ScheduleWellFormed.mk 473d7c7e914c0543
theorem AvailableChain.V2.D.ScheduleWellFormed.horizon_nonneg 5962e520716b7f92
theorem AvailableChain.V2.D.ScheduleWellFormed.sorted 2941e88b3b8e0e83
theorem AvailableChain.V2.D.ScheduleWellFormed.nodup 3a1bad1684871892
theorem AvailableChain.V2.D.ScheduleWellFormed.in_horizon fac776db477b4b06
theorem AvailableChain.V2.D.ScheduleWellFormed.honest_only db8d98c9e1ca3d2b
theorem AvailableChain.V2.D.ScheduleWellFormed.tick_public ab24ba38cdb33c4b
theorem AvailableChain.V2.D.ScheduleWellFormed.tick_total 53d0c34d0eb422df
def AvailableChain.V2.D.NoRestart 61c81d868e8af761
def AvailableChain.V2.D.restartFree 2598def124be1266
structure AvailableChain.V2.D.DeliveryWellFormed 1a816c94344afd36
ctor AvailableChain.V2.D.DeliveryWellFormed.mk 9a8d836d44cff9e6
theorem AvailableChain.V2.D.DeliveryWellFormed.wire 2fb56e9f2ffba607
theorem AvailableChain.V2.D.DeliveryWellFormed.deps dacda2283af44545
theorem AvailableChain.V2.D.DeliveryWellFormed.fresh a3f18ebbd9c6ae0a
structure AvailableChain.V2.D.UnforgeableSignatures 1452c33149072bab
ctor AvailableChain.V2.D.UnforgeableSignatures.mk ac57317d10a79b0d
theorem AvailableChain.V2.D.UnforgeableSignatures.unforgeable 667ad0ba51575fba
theorem AvailableChain.V2.D.UnforgeableSignatures.carried 55928e738ae265d4
structure AvailableChain.V2.D.ExecutionValid 432ec3d6038f2a0f
theorem AvailableChain.V2.D.ExecutionValid.toDeliveryWellFormed 9987ca9419a815b6
theorem AvailableChain.V2.D.ExecutionValid.toScheduleWellFormed 46a8c5120a5df421
theorem AvailableChain.V2.D.ExecutionValid.toUnforgeableSignatures 40163ea5c0215498
ctor AvailableChain.V2.D.ExecutionValid.mk 95292f15315b961c
def AvailableChain.V2.D.SelfDelivery 9a7f85b02c0e60d6
theorem AvailableChain.V2.D.ScheduleWellFormed.mem_emittedAt_iff_emits cceaa82c7bc6a8c3
theorem AvailableChain.V2.D.restartFree_refl dbf7c26d4fdd11ce
theorem AvailableChain.V2.D.not_restartFree_succ_iff c73ac265c06bf2d8
theorem AvailableChain.V2.D.restartFree.mono 54e5488e3550e47c
theorem AvailableChain.V2.D.restartFree.append 1d178b4a1886c2af
theorem AvailableChain.V2.D.NoRestart.restartFree 5934146744b22c47
```

### `AvailableChainEngineV2.Laws.Duty.Hooks`

```text
structure AvailableChain.V2.D.HooksSound 9ae115d2f7a7d4aa
ctor AvailableChain.V2.D.HooksSound.mk 60e54108fd3cec77
theorem AvailableChain.V2.D.HooksSound.excludes_inert 095d325aa652fc22
theorem AvailableChain.V2.D.HooksSound.excludes_stable 5b5af6b2c46b4343
theorem AvailableChain.V2.D.HooksSound.processed_stable 59aaf86fd875ae1b
theorem AvailableChain.V2.D.HooksSound.deps_stable b6027621618ff4d4
theorem AvailableChain.V2.D.HooksSound.handles_carries d1f8500e7f4d9cdd
theorem AvailableChain.V2.D.HooksSound.recordOwn_processed 885399400e924b97
theorem AvailableChain.V2.D.HooksSound.recordOwn_deps 7582b2e8854ce0e0
theorem AvailableChain.V2.D.HooksSound.recordOwn_excludes ef1581acab8c8f9e
theorem AvailableChain.V2.D.HooksSound.foldl_recordOwn_processed f161df2e3ee797b8
theorem AvailableChain.V2.D.HooksSound.foldl_recordOwn_deps a7a1fd171a49f958
theorem AvailableChain.V2.D.HooksSound.foldl_recordOwn_excludes 34fdb819911fc949
theorem AvailableChain.V2.D.HooksSound.processed_tick 0eeb8ce5791d75b4
theorem AvailableChain.V2.D.HooksSound.deps_tick 69ccdaf8daf6316d
theorem AvailableChain.V2.D.HooksSound.excludes_tick 85bf13c93ec9c24b
```

### `AvailableChainEngineV2.Laws.Duty.Isolation`

```text
def AvailableChain.V2.D.LabelFamilies.APObject 952ef7d50926efe9
theorem AvailableChain.V2.D.LabelFamilies.apObject_seat 659924427114cc2f
theorem AvailableChain.V2.D.LabelFamilies.apObject_none 00cbb33cfab5268d
structure AvailableChain.V2.D.Isolation 6adceb8c61fc96da
ctor AvailableChain.V2.D.Isolation.mk 0483b43ba4f95f45
def AvailableChain.V2.D.Isolation.Base 3415084d10f42256
def AvailableChain.V2.D.Isolation.base 0de58c59ae4aea4e
def AvailableChain.V2.D.Isolation.clockB 7db2d0a98e240d9c
theorem AvailableChain.V2.D.Isolation.clock_base f05010cc85ee9daa
def AvailableChain.V2.D.Isolation.processB 392d5183f6806765
theorem AvailableChain.V2.D.Isolation.process_base 2672ba57dbd51102
theorem AvailableChain.V2.D.Isolation.recordOwn_base 1cd5a355ba383974
def AvailableChain.V2.D.Isolation.actB 67ea394a7699935c
theorem AvailableChain.V2.D.Isolation.act_base 15a57c5f6a9d829b
def AvailableChain.V2.D.Isolation.gossipB 202dcba7669de56c
theorem AvailableChain.V2.D.Isolation.gossip_base 4ad5f5e56e9c7885
def AvailableChain.V2.D.Isolation.depsB 48d218cd61d07932
def AvailableChain.V2.D.Isolation.processedB a6a8a29e2aed0d49
def AvailableChain.V2.D.Isolation.excludesB b794dd6f10f750ea
def AvailableChain.V2.D.Isolation.handlesB 19cbd6f58d2fd585
theorem AvailableChain.V2.D.Isolation.hooks_base 78f5326284c1c9e6
theorem AvailableChain.V2.D.Isolation.separation a6fa4415e3d15d1b
theorem AvailableChain.V2.D.Isolation.foldl_recordOwn_base 853ed7735d0272e0
theorem AvailableChain.V2.D.Isolation.base_tick eba936c002be9848
theorem AvailableChain.V2.D.Isolation.hooks_congr 7f968d9ec1ef986a
theorem AvailableChain.V2.D.Isolation.not_ap_of_selfVisible b18b27c4d46acdec
```

### `AvailableChainEngineV2.Laws.Duty.Outputs`

```text
structure AvailableChain.V2.D.OutputsFactor 93a9292a4ed51dea
ctor AvailableChain.V2.D.OutputsFactor.mk 5736019f125565b1
def AvailableChain.V2.D.OutputsFactor.confirmedB e0af6e11a1c3bfa7
theorem AvailableChain.V2.D.OutputsFactor.confirmed_base 92928075575f61b3
def AvailableChain.V2.D.OutputsFactor.stableB 2a0a32b0a1f38413
theorem AvailableChain.V2.D.OutputsFactor.stable_base c70418cf7cf21360
theorem AvailableChain.V2.D.OutputsFactor.confirmed_recordOwn 671ed17b28e70a9f
theorem AvailableChain.V2.D.OutputsFactor.stable_recordOwn e3795ff3791f2c85
theorem AvailableChain.V2.D.OutputsFactor.confirmed_tick 7689870b2a3c20a9
theorem AvailableChain.V2.D.OutputsFactor.stable_tick 97392610a0cd1e45
```

### `AvailableChainEngineV2.Laws.Duty.SelfDelivery`

```text
structure AvailableChain.V2.D.EmitOk 209c188f6b43f12d
ctor AvailableChain.V2.D.EmitOk.mk df36f771195e2d43
theorem AvailableChain.V2.D.EmitOk.wire b99eb4d8e7cc0f18
theorem AvailableChain.V2.D.EmitOk.deps 1ee5cbeddc46f32c
theorem AvailableChain.V2.D.EmitOk.fresh a1d8f3c92f9bec05
theorem AvailableChain.V2.D.EmitOk.noCarried 38968a9639ac2bfa
theorem AvailableChain.V2.D.Run.holder_of_mem_tick 1e90643dcf85d046
theorem AvailableChain.V2.D.World.step_apply_of_node_ne 3acab309912053e1
theorem AvailableChain.V2.D.Run.stateBefore_eq_of_node_ne 58584a7d1c3512b0
theorem AvailableChain.V2.D.selfDelivery_admissible 58cad2a4fe63181e
theorem AvailableChain.V2.D.Run.getElem?_snoc_of_lt bc6002271aa3904c
theorem AvailableChain.V2.D.Run.tick_snoc 1f05deaae77d0e5f
theorem AvailableChain.V2.D.Run.stateBefore_snoc_of_le 9be8fe8a3512d3d9
theorem AvailableChain.V2.D.Run.emitsAt_snoc_of_lt 5dd8cf215b1e4926
theorem AvailableChain.V2.D.Run.emits_snoc a3e51cdb084443b4
theorem AvailableChain.V2.D.EmitOk.snoc 1e499dffc35015a0
theorem AvailableChain.V2.D.ExecutionValid.snoc_selfDelivery 520eb73c990da2c5
```

### `AvailableChainKitV2.DutyEmission`

```text
theorem AvailableChain.V2.D.Engine.mem_tick_seat_iff 895b4eda7c1f7cdb
theorem AvailableChain.V2.D.Engine.mem_tick_duty_iff fbf5706ba4f001c6
theorem AvailableChain.V2.D.Engine.mem_tick_of_duty 66c630dc358188d8
theorem AvailableChain.V2.D.Engine.ownSeats_bijSeat ff8cce9b7c60dc44
theorem AvailableChain.V2.D.Engine.emits_bijSeat 8e11251ebc3968b1
theorem AvailableChain.V2.D.Engine.mem_tick_seat_toD_iff 19757f871d80f96d
```

### `AvailableChainKitV2.DutyLinked`

```text
theorem AvailableChain.V2.D.Engine.linked_singleton_iff 1bc1d4ed1f506ad8
theorem AvailableChain.V2.D.Engine.seat_family_iff_representative_toD 41133f928dbe4a58
theorem AvailableChain.V2.D.Engine.seat_equation_toD_of_family 71fd7e817a3975a0
```

### `AvailableChainKitV2.DutyClockLaws`

```text
structure AvailableChain.V2.D.Engine.ClockLaws da7625d0531294f9
ctor AvailableChain.V2.D.Engine.ClockLaws.mk a59ce200e3441c55
def AvailableChain.V2.D.Engine.ClockLaws.now 8e2344910c52841e
theorem AvailableChain.V2.D.Engine.ClockLaws.init 2c2088fee6c5a366
theorem AvailableChain.V2.D.Engine.ClockLaws.clock 6b91b32c96dd0e82
theorem AvailableChain.V2.D.Engine.ClockLaws.process 5e798afc5f517de5
theorem AvailableChain.V2.D.Engine.ClockLaws.recordOwn_now ca4ffdb214ba7fc0
theorem AvailableChain.V2.D.Engine.ClockLaws.now_foldl_recordOwn 4d5387560b0522ec
theorem AvailableChain.V2.D.Engine.ClockLaws.now_tick e7a56d81a0698f79
```

### `AvailableChainKitV2.DutyEngineClock`

```text
theorem AvailableChain.V2.D.Engine.stateBefore_now_source c556b3f9270ce80b
theorem AvailableChain.V2.D.Engine.stateBefore_now_source_noRestart 8188969742b87617
theorem AvailableChain.V2.D.Engine.stateBefore_now_le_event 757c29148b6d8dfd
theorem AvailableChain.V2.D.Engine.stateBefore_now_le_event_noRestart 21ee6c9c426ec1c6
theorem AvailableChain.V2.D.Engine.stateBefore_now_mono d96c8dbcb0ab144f
theorem AvailableChain.V2.D.Engine.stateBefore_now_mono_noRestart 222cb09d8eda0171
theorem AvailableChain.V2.D.Engine.delivery_now_ge_public 3895dc5ba9e2acd8
theorem AvailableChain.V2.D.Engine.stateBefore_invariant 49347bd5e864b50c
theorem AvailableChain.V2.D.Engine.stateBefore_invariant_noRestart e14bbf6f3ae27ac4
theorem AvailableChain.V2.D.Engine.stateBefore_stable_clock a0b180e2ecb15b44
theorem AvailableChain.V2.D.Engine.stateBefore_stable_clock_restore 04533de1d30dc850
theorem AvailableChain.V2.D.Engine.stateBefore_stable_clock_noRestart 254a33070ace0644
theorem AvailableChain.V2.D.Engine.clock_field_origin 0cabaf9537c0dfa6
theorem AvailableChain.V2.D.Engine.clock_field_origin_noRestart f1e8577e8ded84c5
theorem AvailableChain.V2.D.Engine.clock_field_origin_of_subset 637db826493dbec0
theorem AvailableChain.V2.D.Engine.stateBefore_field_prefix 23183fffebc81698
theorem AvailableChain.V2.D.Engine.stateBefore_field_prefix_restore aded7526377edc5e
```

### `AvailableChainKitV2.DutyExecution`

```text
theorem AvailableChain.V2.D.Engine.eventIndex_lt_of_time_lt 69f02cb9b89ad8c3
theorem AvailableChain.V2.D.Engine.time_le_of_key_le fe723cf18e365497
theorem AvailableChain.V2.D.Engine.filter_eq_take e57398f104757534
theorem AvailableChain.V2.D.Engine.filter_false_of_index_ge 5645bac824454bad
theorem AvailableChain.V2.D.Engine.index_lt_read_length_iff 71ee49562801ab10
theorem AvailableChain.V2.D.Engine.read_length_mono 437a4ac054322858
theorem AvailableChain.V2.D.Engine.tick_index_lt_delivery 01b9e8e5bf9d1a70
theorem AvailableChain.V2.D.Engine.readAt_eq_stateBefore cc225b2ecbbd7d32
theorem AvailableChain.V2.D.Engine.stateBefore_other_node 695952512d88999d
theorem AvailableChain.V2.D.Engine.stateBefore_tick_eq_stateBeforeTime e6356bea44258b6e
```

### `AvailableChainKitV2.DutyRecord`

```text
def AvailableChain.V2.D.Engine.ownReleasedAt 5d93fcd9116932a1
def AvailableChain.V2.D.Engine.ownReleased 8e95a495b218f7df
theorem AvailableChain.V2.D.Engine.ownReleasedAt_def 446ea4db917debf9
theorem AvailableChain.V2.D.Engine.ownReleased_def c3a755ca388d2266
theorem AvailableChain.V2.D.Engine.ownReleased_self fc8f525878bdcd3e
theorem AvailableChain.V2.D.Engine.ownReleased_succ dbb5de8b607d64fb
theorem AvailableChain.V2.D.Engine.ownRecord_fold_interval bdedbac7de227b1b
theorem AvailableChain.V2.D.Engine.ownRecord_fold 4c18d9267d374c45
theorem AvailableChain.V2.D.Engine.ownRecord_fold_interval_restart ebb485d92d680fcd
theorem AvailableChain.V2.D.Engine.ownRecord_fold_restore 9b736ddd6b040914
```

### `AvailableChainKitV2.DutyStable`

```text
theorem AvailableChain.V2.D.Engine.foldl_recordOwn_preserve 3dd40ab089116b78
theorem AvailableChain.V2.D.Engine.tick_preserve 79780cb52f307185
theorem AvailableChain.V2.D.Engine.recordOwn_preserve_of_base 8b0c114ce5e936a6
theorem AvailableChain.V2.D.Engine.stateBefore_step_induction 0f5f32435b17620c
theorem AvailableChain.V2.D.Engine.stateBefore_stable 74359fd20ef2eec6
```
