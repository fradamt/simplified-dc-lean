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
│ D8 │ Block-dependent parts (Task 3) start after the  │ controller (survey R5)       │
│    │ I9 merge; Tasks 0–2 and 4–5 may run before it   │                              │
└────┴─────────────────────────────────────────────────┴──────────────────────────────┘
```

Answered by DC-simplify (2026-09-29; survey R6): FG-SA HEAD labels (the SA base, AP duties) are in the `fresh` (CStar) family; FG labels (`.fg r`) are in the `linked` family (one FG identity across rounds, needed for client safety). FG-SA regimes do not require `SelfDelivery`; every FG-SA result holds for both self-delivery timings. `selfDelivery_admissible` shows that one such delivery is admissible; that complete regime runs with the DC timing exist is an inhabitation question (plan 1c). Claim ids for v2 (survey R7) are a 2b question for the user.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- No `sorry`, `admit`, `native_decide` or new axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The Mac `lean` is a 3-slot throttle wrapper. Run `pgrep -fl lean` first. Use `lake env lean --run <file>` for scripts; never a `lean_exe`. When the I9 branch builds at the same time, one build at a time per worktree.
- **Worktree.** Work in `~/worktrees/available-chain-v2` on branch `v2-2a` from main. Before Task 3, merge (or rebase onto) the I9 result on main. Copy `.lake/packages` from the main checkout when the worktree is created, so that Mathlib is not rebuilt.
- **No v1 edits.** Do not edit `AvailableChainModel/**`, `AvailableChainStatements/**`, `AvailableChainFramework/**` (except Task 6's anchor), the v1 Kit, or any protocol library. v2 copies v1 text; it does not import-and-modify v1 definitions.
- **Imports.** `AvailableChainEngineV2` imports only Mathlib, `AvailableChainModel` (objects: `Block`, `BlockId`, `Slot`, `Time`, `Env`) and its own modules. `AvailableChainKitV2` imports only Mathlib, `AvailableChainModel` and `AvailableChainEngineV2`.
- **Freeze rule.** After the gate (Task 6), a 2a structure never gains a field, a 2a inductive never gains a constructor, a 2a definition never gains a parameter. 2b and 2c add declarations or separate structures.
- Commit by explicit path. Commit messages end with the `Claude-Session:` line. Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md`, `docs/audit/*.log`.
- Prose in ASD-STE100; tables in Unicode box drawing inside fenced `text` blocks. No time estimates.

## Review Focus

1. **The tick and the emission cannot drift.** `World.step` and `emittedAt` use the same `tick`. Test: Task 1 `tick_decomp` and `emittedAt_eq_tick`.
2. **An asleep node emits nothing and records nothing.** `recordOwn` folds only over released objects. Test: Task 1 Step 5.
3. **Separation.** AP labels and the fresh (CStar) family are never self-visible. Test: Task 4 negative example (a spec that violates separation has no `Isolation` value).
4. **Self-delivery admissibility is real.** The lemma's hypotheses are satisfiable for a concrete protocol. Test: Task 5 toy run where a self-visible object is delivered to its sender at the emission time and passes every check.
5. **The input cannot be trivialized by the protocol.** `In` is a parameter, not a field. Test: Task 1 Step 6, a `#check` that `ProtocolSpec` has no input field, and a protocol that ignores its input still has type `ProtocolSpec In` for any `In`.

## Tasks

### Task 0: Libraries and layout

**Files:**
- Modify: `lakefile.toml` (new library `AvailableChainKitV2`; `AvailableChainEngineV2` globs for `Engine/*`, `Conditions/*`, `Laws/*`).
- Modify: `AvailableChainEngineV2.lean` (imports as the tasks add modules).

- [ ] **Step 1:** Library entries. The existing `Sketch.lean` stays as it is (namespace `AvailableChain.Framework.V2Sketch`); it is a law study, and Task 5 ports its toy.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: library layout for 2a`.

### Task 1: Objects, spec, events, tick, runs

**Files:**
- Create: `AvailableChainEngineV2/Engine/Objects.lean`, `Engine/Spec.lean`, `Engine/Run.lean`.

**Interfaces:**
- Produces: `Auth (L) (seats : L → Nat)` with `seat (ℓ) (i : Fin (seats ℓ)) | none`; `Signed L seats Payload`; `ProtocolSpec (In : Type)` with fields `State Label seats Payload Durable init clock actTime duties duties_spec duties_nodup act gossip process selfVisible recordOwn durable restore wellFormed depsPresent processed excludes handles carries` (survey §2.1; `act : State → Label → In → Option Payload`); `P.Object := Signed P.Label P.seats P.Payload`; `Event V Object` with `restart | tick | deliver` and phases 0, 1, 2; `World`; `Run V P` with `honest horizon events seatOf input`; `holder`; `tick E rho st v t : P.State × List P.Object`; `World.step`; `stateBefore E rho i`, `stateBeforeTime`, `readAt`, `final`, `emittedAt`, `emits`, `processes`, `handlesAt`, `acceptsAt`.

- [ ] **Step 1: Objects.** `Auth` and `Signed`. Give `DecidableEq` by `deriving` if it works on the dependent `Fin`; otherwise a manual instance. `Repr` if cheap.
- [ ] **Step 2: Spec.** `ProtocolSpec (In : Type)` as the survey §2.1 states it, with `selfVisible : Label → Bool` (labels, not objects; an unsigned object is never self-visible: `objSelfVisible o := match o.auth with | .seat ℓ _ => selfVisible ℓ | .none => false`).
- [ ] **Step 3: Tick.** `tick` as survey §2.1: clock; if awake, the payloads of every duty `ℓ ∈ duties t` for every seat `i` with `seatOf ℓ i = v`, from the post-clock state and `rho.input v t`, in label order then seat order, then gossip; `recordOwn` folded over the self-visible released objects; release. `World.step`: `restart` ↦ `restore (durable _)`, `tick` ↦ `(tick …).1`, `deliver` ↦ `process`.
- [ ] **Step 4: Run functions.** As v1 (`AvailableChainModel/Generic/Run.lean`), each taking `E`. `emittedAt E rho v t := (tick E rho (stateBeforeTime E rho v t) v t).2` (the state before the tick at `t`). `holder (.seat ℓ i) := some (rho.seatOf ℓ i)`, `holder .none := none`.
- [ ] **Step 5: Laws.** `tick_decomp` (the post-tick state is the `recordOwn` fold over the released self-visible objects, from the post-clock state); `emittedAt_eq_tick`; `tick_asleep` (asleep: no objects, state = post-clock state).
- [ ] **Step 6: Tests.** A two-label spec with one seat each, a run of three events; `decide` or `rfl` checks of `emittedAt`, `stateBefore`; a spec that ignores its input, typed at `In := Nat` and at `In := Unit`.
- [ ] **Step 7: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: objects, spec, tick, runs`.

### Task 2: Conditions without blocks

**Files:**
- Create: `AvailableChainEngineV2/Conditions/Schedule.lean`, `Conditions/Committees.lean`.

**Interfaces:**
- Produces: `PublicTime`, `ScheduleWellFormed`, `DeliveryWellFormed`, `UnforgeableSignatures`, `ExecutionValid` (v1 text over v2 runs; `holder` through `seatOf`); `NoRestart`, `restartFree rho v i j`; `LabelFamilies P` (`ap fresh linked : P.Label → Prop`); `CStar F rho` (each label in `F` has a bijective seat map), `Linked F rho` (one bijection `Fin N ≃ V` shared by all labels in `F`, with `seats ℓ = N` and `Fin.cast`), `SingleSeat F`; `SelfDelivery rho` (every self-visible released object is delivered to its sender at the emission time).

- [ ] **Step 1:** Copy the v1 texts from the post-plan-1b `AvailableChainStatements/Generic/Conditions.lean` and adapt them to v2 runs. Record each adaptation in the report.
- [ ] **Step 2:** The committee and restart conditions. `Linked` implies `CStar` on its family (lemma).
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: schedule, committee and restart conditions`.

### Task 3: Conditions with blocks; interface (after the I9 merge)

**Files:**
- Create: `AvailableChainEngineV2/Conditions/Delivery.lean`, `Conditions/Interface.lean`.

**Interfaces:**
- Produces: `PartialSynchrony`, `HealthyPrefixDelivery` (v1 text, with the exclusion exemption and DC's receipt relay); `Interface P` (`confirmed`, `stable`, `block`, `opening`, `propLabel : Slot → P.Label`, `propLabel_single : P.seats (propLabel s) = 1`); `proposalTime I s := P.actTime (I.propLabel s)`; `proposerOf rho I s := rho.seatOf (I.propLabel s) ⟨0, _⟩`; `readAt E rho I v t`; `BlockInRun`, `RootInjective` (post-I9 text) and `rootInjective_all` (from `Block.root_injective`).

- [ ] **Step 1:** Rebase or merge the branch onto main after the I9 merge. Copy from the post-I9 text.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: delivery conditions and interface`.

### Task 4: Laws

**Files:**
- Create: `AvailableChainEngineV2/Laws/Isolation.lean`, `Laws/Hooks.lean`, `Laws/SelfDelivery.lean`.

**Interfaces:**
- Produces: `Isolation P F` (survey §2.2: `Base`, `base`, `clockB`, `clock_base`, `processB`, `process_base`, `recordOwn_base` (`base (recordOwn st o) = base st`), `actB`, `act_base` on `F.ap`, `gossipB`, `gossip_base`, `hooks_base` (the five hooks on AP objects factor through `base`), `separation : ∀ ℓ, F.ap ℓ ∨ F.fresh ℓ → P.selfVisible ℓ = false`); `OutputsFactor I iso`; `HooksSound P` (v1 fields over v2 runs, stability on `restartFree` intervals, plus `recordOwn_processed`, `recordOwn_deps`, `recordOwn_excludes`); `selfDelivery_admissible`.

- [ ] **Step 1: Isolation.** Port the law shapes of `Sketch.lean` (`Isolated`, `foldl_recordOwn_base`, `output_tick`) to the new spec; prove `base_tick` (the base after a tick depends only on the base before, the time and the released AP payloads).
- [ ] **Step 2: HooksSound.** Stated over v2 runs with `ScheduleWellFormed`, stability fields with `restartFree rho v i j`.
- [ ] **Step 3: Self-delivery.** `selfDelivery_admissible`: for an honest, awake `v` and a self-visible object `o` released at `t`, a delivery of `o` to `v` at `t`, placed after the tick phase, satisfies `DeliveryWellFormed` (wire, provenance, freshness) under explicit hypotheses: `P.wellFormed o`, `P.depsPresent` after the tick, and `¬ P.processed` after `recordOwn` (the `recordOwn_processed` field gives the last from "not processed before the tick"). State the hypotheses as a structure `EmitOk P` so that plan 1c can reuse it.
- [ ] **Step 4: Negative test.** A two-label spec where an AP label is self-visible: prove that it has no `Isolation` value for the obvious `LabelFamilies`.
- [ ] **Step 5: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: isolation, hooks, self-delivery`.

### Task 5: Kit v2 and the toy

**Files:**
- Create: `AvailableChainKitV2.lean`, `AvailableChainKitV2/{ClockLaws,Execution,EngineClock,Stable}.lean`, `AvailableChainEngineV2/Tests/Toy.lean`.

**Interfaces:**
- Produces: `ClockLaws` (v1 fields plus `recordOwn_now`); the v2 forms of the lemmas that the T7 plan names at T7.0 and T7.6 (`eventIndex_lt_of_time_lt`, `readAt_eq_stateBefore`, `stateBefore_tick_eq_stateBeforeTime`, `tick_index_lt_delivery`, `delivery_now_ge_public`, `stateBefore_now_mono`, `stateBefore_now_le_event`, `stateBefore_stable`, `stateBefore_stable_clock`) with their `Execution` dependencies; each lemma that crosses a restart takes `NoRestart`.

- [ ] **Step 1:** Port each lemma from `AvailableChainKit/Engine/{EngineClock,Execution,Stable}.lean`. Keep names; namespace `AvailableChain.V2.Engine`. List in the report each lemma that needed `NoRestart` (2c must generalize them).
- [ ] **Step 2: Toy.** Port `toyV2` from `Sketch.lean` to the v2 spec: a Linked family with one self-visible label, one AP label, a run with a tick, a self-delivery at the emission time and a delivery to another node. Check `selfDelivery_admissible`'s hypotheses on it (Review Focus 4). This is a test, not the Phase 2c toy protocol.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainEngineV2 AvailableChainKitV2`. Commit `KitV2: engine lemmas; EngineV2: toy`.

### Task 6: Gate — anchor and freeze

**Files:**
- Modify: `scripts/CatalogLock.lean` (add `AvailableChainFramework.V2` to `lockedModulePrefixes`).
- Create: `AvailableChainFramework/V2/Anchor.lean` (one `def` whose type mentions `ProtocolSpec`, `Run`, `tick`, `Interface`, `LabelFamilies`, `Isolation`, `HooksSound`, `EmitOk` and the conditions of Tasks 2–3).
- Modify: `AvailableChainFramework.lean` (import), `lakefile.toml` only if the Framework library needs the dependency listed.

- [ ] **Step 1:** Check that `AvailableChainFramework` may import `AvailableChainEngineV2` (the layer rule in design §1: the Framework is L2–L3, the engine is L0–L1). If the layer rule forbids it, put the anchor in a new small locked library instead, and report.
- [ ] **Step 2:** `CatalogLock --check`: ADDED lines only, all under `AvailableChainFramework.V2` or the closure of the anchor. `--write` (no `--allow-changes`). `--check` prints nothing.
- [ ] **Step 3: Full build.** `pgrep -fl lean`; `lake build --wfail` (every default target); `CheckFrameworkAxioms`; `Registry --check`; `check-fg.sh`; `check-fgsa.sh`; grep for `sorry|admit|native_decide|^axiom` over the new files.
- [ ] **Step 4: Docs.** `docs/MAP.md` rows; a dated design §2 note "As implemented in Phase 2a"; `docs/PHASE2A-REPORT.md` (controller) with the frozen API list for the T7 v2 revision.
- [ ] **Step 5: Merge.** Merge `v2-2a` into main (`--ff-only` if possible, else `--no-ff` after `merge-tree` and a full build). Tell DC-simplify: the frozen API list and the report path.

## After 2a (outlines; each gets its own plan and audit)

**2b — lift and v2 claims.** v2 properties and regimes (each with `NoRestart` and `CStar` on the fresh family; `FastOutageRegime` with `Fintype.card V`); the v2 `Instance` (binds `LabelFamilies`, `Isolation`, `HooksSound`, `Interface`); `ClaimDomain.v2 In`; the 14 claims and 3 profiles under new ids (the user decides the id scheme); `StrongInstance` v2; `Simulation`, `ClaimSim`, `ClaimSim.holds` (survey §4.3); the lift of a v1 `ProtocolSpec` (label sum `P₁.Label ⊕ Slot`, `enc`/`dec`, seat maps from `CStar`); the subtype equivalence of legacy contexts, so the lift also transports `inhabited`, certificates and refutations; the transport of `grid_holds`, `sa_holds`, `sapc_holds_*`, the Counter certificates and the Sanity refutations; `HooksSound` for lifted instances (survey R3: a node-projection lemma, or per-protocol v2 proofs); finite checked v2 traces of lifted Grid CO, SA and SA-PC (order check, acceptance item); Registry support for v2 instance types. All in `AvailableChainFramework/V2` and `Catalog/V2`: ADDED lock lines only.

**2c — restart, toy protocol, I1.** The E6 restore law (`RestoreLaw`), epochs, rejoin conditions, `catchUp`, restart regimes; the generalization of the Kit v2 lemmas that took `NoRestart`; the toy Linked, self-visible, restart protocol of the Phase 2 acceptance; the I1 fix: an input facet, a versioned floor claim with the input binding in the conclusion, `clockChain` lifted at a non-trivial `In` and refuted, `Candidate` kept as the legacy floor (order check O1).

## Risks

```text
┌────┬────────────────────────────────────────┬──────────────────────────────────────────┐
│ R  │ Risk                                   │ Response                                 │
├────┼────────────────────────────────────────┼──────────────────────────────────────────┤
│ R1 │ `DecidableEq` on dependent `Auth`      │ Manual instance (Task 1 Step 1)          │
│ R2 │ Every run function takes `E`; Kit      │ Accepted (survey R9); the port records   │
│    │ lemma statements change                │ each changed statement                   │
│ R3 │ A 2a type must change after T7 starts  │ Freeze rule + anchor; a change is a      │
│    │                                        │ declared lock break with DC-simplify's   │
│    │                                        │ review                                   │
│ R4 │ The Framework cannot import the engine │ Task 6 Step 1 fallback: a small locked   │
│    │ by the layer rule                      │ library                                  │
│ R5 │ I9 changes a copied v1 text            │ Task 3 waits for the I9 merge (D8)       │
│ R6 │ Two worktrees build at once on 3 Lean  │ One build per worktree at a time; the    │
│    │ slots                                  │ controller orders builds                 │
└────┴────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Audit disposition

(Filled after the Astra audit and the DC-simplify review.)
