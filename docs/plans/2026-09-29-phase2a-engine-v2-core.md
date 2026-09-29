# Phase 2a: engine v2 core — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A frozen engine v2 core (design §2 E1, E2, E5, with the E4 hooks and the reserved E6 and input interfaces) and a Kit v2 port, so that FG-SA T7.0–T7.9 can start on v2.

**Architecture:** Everything goes into the library `AvailableChainEngineV2` (engine, conditions, laws; namespace `AvailableChain.V2`) and a new library `AvailableChainKitV2` (engine lemmas). Nothing goes into `AvailableChainFramework` except one anchor declaration at the gate, which adds lock lines only. `ProtocolSpec` takes the run-chosen input type as a parameter. One atomic `tick` function gives both the post-tick state and the released objects. Restart, `durable`, `restore` and the input are reserved now, so that 2b and 2c add declarations but never change a 2a type. Stages 2b (the lift, v2 claims) and 2c (E6, the toy protocol, I1) get their own plans after 2a is frozen.

**Tech Stack:** Lean 4 v4.30.0-rc2, Mathlib (no `lake update`), Lake libraries of this repository.

**Spec:** `docs/FRAMEWORK-DESIGN.md` §2 (E1–E6, Lift), §1, §8 ("Order after plan 1b"), §9. Order check: `docs/audit/phase2-order-check-report.md` (conditions O1–O4; §6 self-delivery). Survey: `claude-files/p2/survey.md`. FG-SA T7 plan: branch `fgsa-composition-plan` (a0f08c6), `docs/plans/2026-09-29-fgsa-composition-t7-t1.md`. I9 plan: `docs/plans/2026-09-29-i9-derived-roots.md`.

## Decisions

```text
┌────┬─────────────────────────────────────────────────┬──────────────────────────────┐
│ D  │ Decision                                        │ By                           │
├────┼─────────────────────────────────────────────────┼──────────────────────────────┤
│ D1 │ Phase 2 in stages; 2a unblocks T7.0–T7.9; 2b    │ user (Phase 2 asap, both     │
│    │ lift; 2c E6, toy, I1                            │ parts); DC-simplify; Astra   │
│ D2 │ Reserve NoRestart, durable, restore and the     │ Astra O2; DC-simplify        │
│    │ input in 2a; later stages only ADD              │                              │
│ D3 │ The input is a TYPE PARAMETER                   │ controller (survey R1): a    │
│    │ `ProtocolSpec (In : Type)`, per validator and   │ field would let a protocol   │
│    │ time (`Run.input : V → Time → In`); the claim   │ set `In := Unit` and pass    │
│    │ domain fixes `In` (2c)                          │ any binding floor. For audit │
│ D4 │ Self-delivery at the emission time through      │ DC-simplify (i-a); Astra §6  │
│    │ `process` is allowed, not required; 2a proves   │                              │
│    │ it admissible; an optional `SelfDelivery`       │                              │
│    │ condition exists; FG-SA regimes do not require  │                              │
│    │ it                                              │                              │
│ D5 │ No P2P forwarding rule beyond the v1 receipt    │ user; DC-simplify            │
│    │ premises; DC's receipt relay stays              │                              │
│ D6 │ 2a code outside the Framework; an anchor under  │ controller (survey §5, R4)   │
│    │ a new locked prefix `AvailableChainFramework.V2`│                              │
│    │ at the gate (ADDED lines only)                  │                              │
│ D7 │ The E4 hooks stay run-level (deviation (i)),    │ design §8 row 0; T7 plan     │
│    │ with stability on restart-free intervals        │ T7.7                         │
│ D8 │ Tasks 0–4 need no `Block` and may run before    │ controller (survey R5);      │
│    │ the I9 merge; Tasks 5–7 run after it            │ Astra A08                    │
└────┴─────────────────────────────────────────────────┴──────────────────────────────┘
```

Answered by DC-simplify (2026-09-29; survey R6): FG-SA HEAD labels (the SA base, AP duties) are in the `fresh` (CStar) family; FG labels (`.fg r`) are in the `linked` family (one FG identity across rounds, needed for client safety). FG-SA regimes do not require `SelfDelivery`; every FG-SA result holds for both self-delivery timings. `selfDelivery_admissible` shows that one such delivery is admissible; that complete regime runs with the DC timing exist is an inhabitation question (plan 1c). Claim ids for v2 (survey R7) are a 2b question for the user.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- No `sorry`, `admit`, `native_decide` or new axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The Mac `lean` is a 3-slot throttle wrapper. Run `pgrep -fl lean` first. Use `lake env lean --run <file>` for scripts; never a `lean_exe`. When the I9 branch builds at the same time, one build at a time per worktree.
- **Worktree.** Work in `~/worktrees/available-chain-v2` on branch `v2-2a` from main. Before Task 5, merge (or rebase onto) the I9 result on main. Clone `.lake/packages` from the main checkout with `cp -c -R` (APFS clone) when the worktree is created, so that Mathlib is not rebuilt.
- **No v1 edits.** Do not edit `AvailableChainModel/**`, `AvailableChainStatements/**`, `AvailableChainFramework/**` (except Task 7's anchor), the v1 Kit, or any protocol library. v2 copies v1 text; it does not import-and-modify v1 definitions.
- **Imports.** `AvailableChainEngineV2` imports only Mathlib, `AvailableChainModel` (objects: `Block`, `BlockId`, `Slot`, `Time`, `Env`) and its own modules. `AvailableChainKitV2` imports only Mathlib, `AvailableChainModel` and `AvailableChainEngineV2`.
- **Freeze rule.** After the gate (Task 7), a 2a structure never gains a field, a 2a inductive never gains a constructor, a 2a definition never gains a parameter. 2b and 2c add declarations or separate structures.
- Commit by explicit path. Commit messages end with the `Claude-Session:` line. Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md`, `docs/audit/*.log`.
- Prose in ASD-STE100; tables in Unicode box drawing inside fenced `text` blocks. No time estimates.

## Review Focus

1. **Emission equals the actual tick** (Astra A01). `emits` and `emittedAt` are defined from the state before the tick EVENT (its index), so a restart at the same time is included. Test: Task 1 `step_tick_eq`, and a restart-then-tick test in Task 1 Step 6.
2. **An asleep node emits nothing and records nothing.** Test: Task 1 `tick_asleep`.
3. **Separation.** AP labels and the designated fresh family `F.fresh` are never self-visible; `Linked` labels may be. Test: Task 3 negative example.
4. **Self-delivery admissibility is real** (Astra A02). The hypotheses hold in a complete finite run. Test: Task 6, a finite `ExecutionValid` witness with a self-delivery at the emission time.
5. **The input cannot be trivialized by the protocol.** `In` is a parameter. Test: Task 1 Step 6.
6. **Kit stability covers `recordOwn`** (Astra A03). Every stability or invariant lemma has a `recordOwn` premise or a "factors through `base`" premise. Test: Task 4 counterexample check (a predicate preserved by clock and process but not by `recordOwn` does not satisfy the lemma's premises).

## Tasks

### Task 0: Libraries and layout

**Files:**
- Modify: `lakefile.toml` (new library `AvailableChainKitV2`; globs for `AvailableChainEngineV2` `Engine/*`, `Conditions/*`, `Laws/*`, `Tests/*`).
- Modify: `AvailableChainEngineV2.lean` (imports as the tasks add modules), `scripts/CheckFrameworkAxioms.lean` (scan `AvailableChainEngineV2` and `AvailableChainKitV2`, Astra A10).

- [ ] **Step 1:** Library entries. `Sketch.lean` stays; I9 Task 2 edits its block folds. New 2a modules must not import `Sketch.lean` or `Block` (Tasks 0–4).
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainEngineV2 AvailableChainKitV2`; the axiom check covers both. Commit `EngineV2, KitV2: library layout for 2a`.

### Task 1: Objects, spec, events, tick, runs

**Files:**
- Create: `AvailableChainEngineV2/Engine/Objects.lean`, `Engine/Spec.lean`, `Engine/Run.lean`, `Tests/Engine.lean`.

**Interfaces:**
- Produces: `Auth (L) (seats : L → Nat)` with `seat (ℓ) (i : Fin (seats ℓ)) | none`; `Signed L seats Payload`; `ProtocolSpec (In : Type)` with fields `State Label seats Payload Durable init clock actTime duties duties_spec duties_nodup act gossip process selfVisible recordOwn durable restore wellFormed depsPresent processed excludes handles carries` (`act : State → Label → In → Option Payload`); `P.Object`; `objSelfVisible`; `Event V Object` with `restart | tick | deliver`, phases 0, 1, 2; `World`; `Run V P` with `honest horizon events seatOf input`; `holder`; `tick E rho st v t : P.State × List P.Object`; `World.step`; `stateBefore E rho i`, `stateBeforeTime`, `readAt`, `final`, `emitsAt E rho i` (objects of the tick event at index `i`), `emittedAt`, `emits`, `processes`, `handlesAt`, `acceptsAt`.

- [ ] **Step 1: Objects.** `Auth` and `Signed`. `DecidableEq` by `deriving` if it works on the dependent `Fin`; otherwise a manual instance.
- [ ] **Step 2: Spec.** `ProtocolSpec (In : Type)`. `objSelfVisible o := match o.auth with | .seat ℓ _ => selfVisible ℓ | .none => false`.
- [ ] **Step 3: Tick.** Clock; if awake, the payloads of every duty `ℓ ∈ duties t` for every seat `i` with `seatOf ℓ i = v`, from the post-clock state and `rho.input v t`, in label order then seat order, then gossip; `recordOwn` folded over the self-visible released objects; release. `World.step`: `restart` ↦ `restore (durable _)`, `tick` ↦ `(tick …).1`, `deliver` ↦ `process`.
- [ ] **Step 4: Run functions** (Astra A01). As v1 (`AvailableChainModel/Generic/Run.lean`), each taking `E`. Emission is indexed by the event: `emitsAt E rho i := match rho.events[i]? with | some (.tick v t) => (tick E rho (stateBefore E rho i v) v t).2 | _ => []`. `emittedAt E rho v t` is `emitsAt` at the index of the tick event of `v` at `t` (empty if none); `emits` quantifies over tick indices. `stateBefore E rho i` is the world before event `i`, so a restart at the same time (phase 0) is included.
- [ ] **Step 5: Laws.** `step_tick_eq` (the world after the tick event at `i` is `(tick … (stateBefore E rho i v) v t).1` at `v`, and its released objects are `emitsAt E rho i`); `tick_decomp` (post-tick state = `recordOwn` fold over the released self-visible objects, from the post-clock state); `tick_asleep`.
- [ ] **Step 6: Tests.** (a) A two-label spec with one seat each, three events; `decide` or `rfl` checks of `emitsAt`, `stateBefore`. (b) Restart-then-tick at the same time: state 1 before `t`, restart restores 0, clock keeps the state, `act` emits the state: `emittedAt` reports 0. (c) A spec that ignores its input, typed at `In := Nat` and `In := Unit`; a `#check` that `ProtocolSpec` has no input field.
- [ ] **Step 7: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: objects, spec, tick, runs`.

### Task 2: Conditions without blocks

**Files:**
- Create: `AvailableChainEngineV2/Conditions/Schedule.lean`, `Conditions/Committees.lean`.

**Interfaces:**
- Produces: `PublicTime`, `ScheduleWellFormed`, `DeliveryWellFormed`, `UnforgeableSignatures`, `ExecutionValid` (v1 text over v2 runs; `holder` through `seatOf`; emission through `emitsAt`); `NoRestart`; `restartFree rho v i j` (no restart of `v` at an index `k` with `i ≤ k < j`; restarts of other nodes do not count); `LabelFamilies P` (`ap fresh linked : P.Label → Prop`); `CStar F rho`, `Linked F rho` (one bijection `Fin N ≃ V` for all labels in `F`, `seats ℓ = N`, `Fin.cast`), `SingleSeat F`; `SelfDelivery rho`.

- [ ] **Step 1:** Copy the v1 texts from `AvailableChainStatements/Generic/Conditions.lean`; adapt to v2 runs; record each adaptation in the report.
- [ ] **Step 2:** `Linked F → CStar F` (lemma). `restartFree` endpoint lemmas: `restartFree rho v i i`; `restartFree rho v i (i+1)` fails exactly when event `i` is a restart of `v`.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: schedule, committee and restart conditions`.

### Task 3: Laws without blocks

**Files:**
- Create: `AvailableChainEngineV2/Laws/Isolation.lean`, `Laws/Hooks.lean`, `Laws/SelfDelivery.lean`.

**Interfaces:**
- Produces: `Isolation P F` (`Base`, `base`, `clockB`, `clock_base`, `processB`, `process_base`, `recordOwn_base`, `actB` with the input argument, `act_base` on `F.ap`, `gossipB`, `gossip_base`, `hooks_base` (the hooks restricted to AP objects factor through `base`; for `handles`, both object arguments are AP objects), `separation : ∀ ℓ, F.ap ℓ ∨ F.fresh ℓ → P.selfVisible ℓ = false`); `base_tick : base (tick …).1 = clockB (base st) t`; `HooksSound P` (v1 fields over v2 runs; stability on `restartFree` intervals; `recordOwn_processed` (equality), `recordOwn_deps` (equality), `recordOwn_excludes` (true stays true)); `EmitOk`; `selfDelivery_admissible`.

- [ ] **Step 1: Isolation.** Port the law shapes of `Sketch.lean` (`Isolated`, `foldl_recordOwn_base`) to the new spec. Prove `base_tick` in the stronger form above (Astra: released AP payloads are not an extra dependency). The 2c restore law will reserve both directions, `restore_base` and `durable_base` (note in the docstring).
- [ ] **Step 2: HooksSound.** Stated over v2 runs with `ScheduleWellFormed`; the stability fields take `restartFree rho v i j`.
- [ ] **Step 3: Self-delivery** (Astra A02). `EmitOk` fields: `P.wellFormed o`; `P.depsPresent` in the post-tick state; NOT `P.processed` in the POST-CLOCK state (the `recordOwn_processed` field carries it through the fold); `∀ o', P.carries o o' → False` for the object class of the lemma (or a carried-signature premise; choose one and state it). Conclusion, at the delivery prefix: if the events between the tick event and the delivery do not change `v`'s state, then the delivery passes the wire, dependency and freshness checks of `DeliveryWellFormed`, and the outer signature has provenance for `UnforgeableSignatures`. The lemma does not claim acceptance by the handler, and it does not claim that the rest of the run stays valid.
- [ ] **Step 4: Negative test.** A spec where an AP label is self-visible has no `Isolation` value for the obvious `LabelFamilies`.
- [ ] **Step 5: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: isolation, hooks, self-delivery`.

### Task 4: Kit v2

**Files:**
- Create: `AvailableChainKitV2.lean`, `AvailableChainKitV2/{ClockLaws,Execution,EngineClock,Stable}.lean`.

**Interfaces:**
- Produces: `ClockLaws` (v1 fields plus `recordOwn_now`); the v2 forms of the lemmas that the T7 plan names (`eventIndex_lt_of_time_lt`, `readAt_eq_stateBefore`, `stateBefore_tick_eq_stateBeforeTime`, `tick_index_lt_delivery`, `delivery_now_ge_public`, `stateBefore_now_mono`, `stateBefore_now_le_event`, `stateBefore_stable`, `stateBefore_stable_clock`, `stateBefore_invariant`) with their `Execution` dependencies.

- [ ] **Step 1:** Port each lemma from `AvailableChainKit/Engine/{EngineClock,Execution,Stable}.lean`; names kept; namespace `AvailableChain.V2.Engine`; imports narrowed to the v2 engine.
- [ ] **Step 2** (Astra A03). Every stability, invariant, field-origin and field-prefix lemma gets a premise that `recordOwn` preserves its predicate (`∀ st o, Q st → Q (recordOwn st o)`), or the alternative premise "Q factors through `iso.base`". Each lemma that crosses a restart takes `NoRestart` (or `restartFree` on its interval). List them in the report; 2c ADDS restart-aware lemmas and keeps these.
- [ ] **Step 3: Counterexample check.** A predicate on a private flag that clock and process preserve and `recordOwn` changes: show that `stateBefore_stable`'s premises fail for it (a short `example`).
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainKitV2`; axiom check. Commit `KitV2: engine lemmas`.

### Task 5: Conditions with blocks; interface; outputs (after the I9 merge)

**Files:**
- Create: `AvailableChainEngineV2/Conditions/Delivery.lean`, `Conditions/Interface.lean`, `Laws/Outputs.lean`.

**Interfaces:**
- Produces: `PartialSynchrony`, `HealthyPrefixDelivery` (v1 text with the exclusion exemption and DC's receipt relay); `Interface P` (`confirmed`, `stable`, `block`, `opening`, `propLabel : Slot → P.Label`, `propLabel_single : P.seats (propLabel s) = 1`); `proposalTime`, `proposerOf`; `readAt` for outputs; `BlockInRun`, `RootInjective` (post-I9) and `rootInjective_all`; `OutputsFactor I iso` (every output getter factors through `base`).

- [ ] **Step 1:** Merge or rebase onto main after the I9 merge. Copy from the post-I9 text.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: delivery conditions, interface, outputs`.

### Task 6: Toy run and self-delivery witness (after the I9 merge)

**Files:**
- Create: `AvailableChainEngineV2/Tests/Toy.lean`.

- [ ] **Step 1:** A toy spec on the new engine: receipts in `base`, the own record outside `base`, a state-preserving clock, one Linked self-visible label that emits a previously unseen row and carries nothing, one AP label with one seat. Give its `Isolation`, `OutputsFactor` and `HooksSound` values.
- [ ] **Step 2:** A complete finite run with a tick, a self-delivery at the emission time, and a delivery to another node. Prove `ExecutionValid` for the whole run (Review Focus 4), and check that `selfDelivery_admissible`'s hypotheses hold at the self-delivery.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainEngineV2`; axiom check. Commit `EngineV2: toy run with a self-delivery`.

### Task 7: Gate — manifest, anchor, lock, merge

**Files:**
- Create: `docs/V2-API.md` (the frozen API manifest: every 2a declaration that T7 and 2b may use), `AvailableChainFramework/V2/Anchor.lean`.
- Modify: `scripts/CatalogLock.lean` (`lockedModulePrefixes` gains `AvailableChainFramework.V2`), `AvailableChainFramework.lean` (import), `lakefile.toml` if needed.

- [ ] **Step 1: Anchor** (Astra A07). `AvailableChainFramework` may import `AvailableChainEngineV2` (design §1: L2–L3 may depend on L0–L1). The anchor is one `def` whose VALUE references every declaration of `docs/V2-API.md` from `AvailableChainEngineV2` (for example a tuple of `@name` terms), so its closure contains each one. Do not import `AvailableChainKitV2` into the Framework (L5); list the Kit v2 lemmas in the manifest as "not locked".
- [ ] **Step 2: Coverage check.** A small script (or `CatalogLock` option) that reads `docs/V2-API.md` and checks that each listed engine declaration is in the anchor's closure; exit 1 otherwise.
- [ ] **Step 3: Lock.** `CatalogLock --check`: ADDED lines only (under `AvailableChainFramework.V2`), against the post-I9 lock. `--write` (no `--allow-changes`). `--check` prints nothing.
- [ ] **Step 4: Full build.** `pgrep -fl lean`; `lake build --wfail` (every default target, `AvailableChainKitV2` included); `CheckFrameworkAxioms` (EngineV2 and KitV2 scanned); `Registry --check`; `check-fg.sh`; `check-fgsa.sh`; the grep for `sorry|admit|native_decide|^axiom` over the new files.
- [ ] **Step 5: Docs.** `docs/MAP.md` rows; a dated design §2 note "As implemented in Phase 2a"; `docs/PHASE2A-REPORT.md` (controller).
- [ ] **Step 6: Merge.** Merge `v2-2a` into main (`--ff-only` if possible, else `--no-ff` after `merge-tree` and a full build). Tell DC-simplify: the manifest and the report. fgsa-impl then writes the v2 revision of the T7 plan against the manifest (survey R10).

## After 2a (outlines; each gets its own plan and audit)

**2b — lift and v2 claims.**
- Generic parts in `AvailableChainFramework/V2` and `Catalog/V2` (ADDED lock lines only): v2 properties and regimes (each with `NoRestart` and `CStar` on the fresh family); the v2 `Instance` (binds `LabelFamilies`, `Isolation`, `OutputsFactor`, `HooksSound`, `Interface`); `ClaimDomain.v2 In`; the 14 claims and 3 profiles under new ids (the user decides the scheme); v2 `StrongInstance`; `Simulation`, `ClaimSim`, `ClaimSim.holds`.
- Concrete parts in L4 (Registry or protocol libraries), not in the Framework (Astra A09): the lifted instances, the transported `grid_holds`, `sa_holds`, `sapc_holds_*`, Counter certificates and Sanity refutations, and the finite checked traces of lifted Grid CO, SA and SA-PC.
- Input in the context correspondence (Astra A04): legacy v2 contexts ≃ v1 contexts × (V → Time → In), or an embedding that is a section of the projection for a chosen input stream; certificate transport needs an input value (no transport at `In = Empty`); refutation transport needs the reverse conclusion implication on embedded contexts.
- Hooks for lifted instances (Astra A05): v2 `HooksSound` quantifies over runs with restarts and over non-bijective seat maps. A v1 hook proof does not give it. Either prove the five facts per protocol on v2, or choose the legacy restart behaviour and prove that restarted states are covered; do not weaken the v2 hook interface.
- `n` versus `Fintype.card V` (Astra A06): prove the relation from `CStar` for protocols with a non-empty legacy label family; handle protocols with no old labels (for example `clockChain`) separately.
- Registry: v2 instance and strong-instance types; the new floor's certificate form; old ids, certificates and the I1 `KNOWN-GAP` history kept.

**2c — restart, toy protocol, I1.** The E6 restore law (`RestoreLaw` with `restore_base` and `durable_base`), epochs, rejoin conditions, `catchUp`, restart regimes; restart-aware Kit lemmas ADDED beside the frozen `NoRestart` ones; the toy Linked, self-visible, restart protocol (a non-trivial restart, receipt loss outside the durable state, a later delivery that is fresh in the new epoch); the I1 fix: an input facet with a specified decoding relation (not a protocol-supplied `binds := True`), a versioned floor claim with the binding in the conclusion and no premise that assumes the binding, `clockChain` lifted at a non-trivial `In` and refuted, `Candidate` kept as the legacy floor (order check O1). Check the lift and the finite traces again against the final 2c engine.

## Risks

```text
┌────┬────────────────────────────────────────┬──────────────────────────────────────────┐
│ R  │ Risk                                   │ Response                                 │
├────┼────────────────────────────────────────┼──────────────────────────────────────────┤
│ R1 │ `DecidableEq` on dependent `Auth`      │ Manual instance (Task 1 Step 1)          │
│ R2 │ Every run function takes `E`; Kit      │ Accepted (survey R9); the port records   │
│    │ lemma statements change                │ each changed statement                   │
│ R3 │ A 2a type must change after T7 starts  │ Freeze rule, manifest and anchor; a      │
│    │                                        │ change is a declared lock break with     │
│    │                                        │ DC-simplify's review                     │
│ R4 │ T7 needs restart-aware hook facts      │ T7.7 proves them on its own spec, or     │
│    │ (Astra 6: T7.5, T7.7, T7.9)            │ states `NoRestart`; recorded in the T7   │
│    │                                        │ v2 revision                              │
│ R5 │ I9 changes a copied v1 text            │ Tasks 5–7 wait for the I9 merge (D8)     │
│ R6 │ Two worktrees build at once on 3 Lean  │ One build per worktree at a time; the    │
│    │ slots                                  │ controller orders builds                 │
└────┴────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Audit disposition

Astra audit (`docs/audit/phase2a-plan-audit-report.md`): REVISE, 1 blocking, 8 major, 1 minor. All applied in this revision: A01 (emission from the tick event, Task 1 Steps 4–6), A02 (`EmitOk`, Task 3 Step 3), A03 (Kit `recordOwn` premises, Task 4 Steps 2–3), A04–A06 and A09 (2b outline), A07 (manifest, anchor value, coverage check, Task 7), A08 (task split: Tasks 0–4 before I9, 5–7 after), A10 (KitV2 in the build and axiom check, Task 0). Also from the report: separation names the designated fresh family; `actB` keeps the input; `base_tick` in the stronger form; 2c restore law reserves both directions; 2c adds restart-aware Kit lemmas and keeps the frozen ones; the I1 floor needs a specified decoding relation. DC-simplify review: pending.
