# I9: derived block roots (store-only) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A block has no supplied root. `Block.root` is computed from the parent's root, the slot and a body by one injective function, so root injectivity is a theorem for every block, with no run premise.

**Architecture:** `Block.node parent slot body` replaces `Block.node parent slot root`. A new model module gives a linear-size, self-delimiting pairing on `Nat` and its injectivity. `Block.root` applies it recursively. The store-only variant keeps every payload type, `Interface.block` and every contract statement: the store check stays "the parent is stored" (`blockKnown st b.parent`), and a lemma shows that this is the same as "the store has a block with root `b.parent.root`". There is no wire-validity root check, and `excludes` gains no clause. For FG-SA, the FG block gets a body, and the signed row list is encoded into the base body, so `ContentAgree` becomes a theorem. The five regime root fields stay, filled by the universal lemma; their removal is a later, separate API change. The work runs on a branch in a worktree, because the type change breaks every downstream library until the last task. Main moves only when the branch is green.

**Tech Stack:** Lean 4 v4.30.0-rc2, Mathlib (no `lake update`), Lake libraries of this repository.

**Spec:** `docs/FRAMEWORK-DESIGN.md` §12 (I9, with the user's decisions of 2026-09-29) and §2 E4. Design study: `../../research/async-resilient-committees/tip-stability/codex/derived-root.md` (r203), with `codex/scratch/r203-followups.md`. Survey of the merged tree: `claude-files/i9/survey.md` (copied from the session scratchpad). Plan 1b report: `docs/PHASE1B-REPORT.md`.

## Decisions that this plan implements

```text
┌────┬───────────────────────────────────────────────┬──────────────────────────────┐
│ D  │ Decision                                      │ By                           │
├────┼───────────────────────────────────────────────┼──────────────────────────────┤
│ D1 │ The root is a function of content; a block    │ user, 2026-09-29             │
│    │ does not carry its own root; it carries its   │                              │
│    │ parent's root                                 │                              │
│ D2 │ The parent-root check is the store dependency │ user, 2026-09-29             │
│    │ lookup only; an unknown parent root is a      │                              │
│    │ temporary missing dependency; no wire root    │                              │
│    │ check; wire forwarding waits for a P2P spec   │                              │
│ D3 │ Store-only variant: payloads keep resolved    │ controller; DC-simplify      │
│    │ blocks (the parent's root is `b.parent.root`);│ agreed; the user was asked   │
│    │ no Msg, Interface or contract change          │                              │
│ D4 │ Linear-size self-delimiting codec, not        │ controller (survey: Nat.pair │
│    │ `Nat.pair` (see Finding 1); Task 0 checks it  │ roots of FG fixtures reach   │
│    │ before any other task                         │ ~10^13 bits at depth 3)      │
│ D5 │ Honest proposers use body 0; FG-SA's base     │ r203 §1, §3                  │
│    │ body packs (application body, signed rows)    │                              │
│ D6 │ Regime root fields stay, filled by            │ r203 §4, §9 step 5           │
│    │ `rootInjective_all`; removal is a later plan  │                              │
│ D7 │ One joint change on the merged tree, FG-SA    │ r203 §9; DC-simplify         │
│    │ included                                      │                              │
│ D8 │ Order: I9 before Phase 2 and plan 1c          │ user, 2026-09-29             │
└────┴───────────────────────────────────────────────┴──────────────────────────────┘
```

## Findings that shape the plan (survey of d0d913a)

1. **`Nat.pair` roots cannot be evaluated for the FG fixtures.** `Nat.pair` about doubles the bit length at each nesting level. FG rows name earlier roots, and a row encoder nests those roots about 15 levels deep. With r203's encoders the G02 chain gives about 10^4 bits (B1), 3·10^8 bits (B2) and 10^13 bits (B3). The chain is reused by `SimplexFG/{Store,Frame,Client}`, `KitFG/TwoChanges` (`K3`) and `FGSA/Tests/Smoke` (`stA`). A codec whose length adds (`|E(a,b)| ≤ |a| + 2|b| + 2`) grows about `(k+1)×` per FG level for `k` rows, and it stays small at the fixture depths. Its operations (shifts, `Nat.log2`, `+`, `*`, `%`, `/`) have kernel GMP acceleration, so `decide` can evaluate them.
2. **The unchanged FG-SA payload has no application-body field.** r203 §3 checks `b.body = pack appBody rows`. Under store-only, admission decodes `b.body` and checks only its rows component against the carried rows; the application component stays free (honest value 0).
3. **Parent-content reads.** Every handler reads the carried parent only after the store membership check. The only reads without a store check are the state-free `wellFormed` parent-slot tests: `GridCO/Model/Protocol.lean:337`, `SAPC/Model/Handlers.lean:65`, `LStar/Model/Protocol.lean:300`, `FGSA/Model/Handlers.lean:96`.
4. **Lock.** `docs/catalog.lock` has 250 lines, the same file that r203 analysed. `scratch/r203/lock-impact.tsv` predicts 101 CHANGED and 149 unchanged lines. The FG-SA merge added no lock line.
5. **Drift.** Since r203's snapshots, only three main Lean files changed (`GridCO/Model/Protocol` docstring, `GridCO/Proofs/Handling` +1, `GridCO/Proofs/Hooks` −6). All 21 FG-SA files are byte-identical to r203's FG-SA snapshot. Use `main-audit.json` for shared files and `fgsa-audit.json` only for `AvailableChainFGSA/*`.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- No `sorry`, `admit`, `native_decide` or new axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The Mac `lean` is a 3-slot throttle wrapper. Run `pgrep -fl lean` before a build. Use `lake env lean --run <file>` for scripts; never a `lean_exe`.
- **Worktree.** All work is in `~/worktrees/available-chain-i9` on branch `i9-derived-roots`, created from main at the plan's approval commit. Main does not change until Task 11. Every commit ends with the `Claude-Session:` line. Commit by explicit path (`git add <paths>`, then `git commit -m` with no pathspec).
- **Build states.** After Task N, every library that Task N or an earlier task owns builds with `--wfail`. Downstream libraries may fail until their task. A task never weakens a downstream file to make it build.
- **Statements.** A theorem statement may change only where it names the old root field, the old root formula, or a numeric root value. Each such change is listed in the task report with the old and new text. The statements of `gridContract_from_engine`, `saContract_from_engine`, `sapcContract_from_engine`, `sapcStrong_from_engine`, and every theorem that a `Tests/Axioms.lean` file prints, do not change as text.
- **No wire root check.** Do not add a root or parent-root conjunct to any `wellFormed` or to any handler. Do not add a clause to any `excludes`. `blockKnown` keeps its definition.
- **Payloads.** No `Msg`, `Wire`, `Payload` or `Interface` type changes. `fgBlock` and `blockAccepted` in FG-SA change their bodies only as Task 9 states.
- **Fixtures keep their intent.** A test that shows a fork, a counterexample, a refusal or a tie keeps showing it. A fixture that asserted a root collision becomes a positive injectivity or duplicate-refusal test (r203 §8). Record the old and new intent of each changed test in the task report.
- **Lock.** Tasks 0–10 do not run `CatalogLock --write`. Task 11 runs `--check` and compares every CHANGED line with `lock-impact.tsv`. The write needs `--allow-changes`. This is a declared lock break (see "Lock break").
- Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md` or `docs/audit/*.log`.
- Prose in ASD-STE100 Simplified Technical English; tables in Unicode box drawing inside fenced `text` blocks. No time estimates.

## Review Focus

1. **A handler path that skips the parent lookup.** Every insertion of a block into a store must follow `blockKnown st b.parent` (or FG-SA's `parentFG`). A path that inserts first, or reads stored-parent facts from the carried parent before the check, breaks the store-only reading of D2. Test: Task 1's `blockKnown_iff_root` and Task 3/5/6/9 admission lemmas; the audit reads every insertion site.
2. **FG and base content disagree.** `eraseFG (fgBlock P b rows) = b` must hold for every accepted proposal, and the FG root must equal the base root. Test: Task 8's `eraseFG_root` and Task 9's `fgBlock_erase`.
3. **Signed-row rounds are lost.** Two row lists with the same decoded rows and different rounds must give different bodies and roots. Test: Task 9 Step 5.
4. **Tie outcomes change silently.** `ghostStep`, `liveRoot`, `deepest`, `lexKey`, `lexMax` and `bestEligible` order roots numerically. New roots change the order. Every fixture with an order outcome states its expected winner again, computed from the new roots. Test: each task's fixture step.
5. **Parent reads before the store check.** The four `wellFormed` parent-slot tests read the carried parent without the store. Task 1 Step 4 gives the three-case lemma; Tasks 3, 5, 6 and 9 instantiate it.

## Lock break

The change of `Block`'s third constructor argument (from `root : BlockId` to `body : Nat`) changes the closure of every lock line that reaches `Block`. r203 predicts 101 CHANGED lines (lines `6; 13–14; 21; 28–32; 34–106; 122–124; 155–156; 163–169; 195–201`). This plan declares that break. No declaration in `AvailableChainFramework` changes its text; the lines change because their closure changes. Task 11 stops if a line outside the predicted set changes, if a line is REMOVED, or if an ADDED line appears in `AvailableChainFramework`.

## Tasks

### Task 0: Codec

**Files:**
- Create: `AvailableChainModel/Objects/Codec.lean`
- Modify: `AvailableChainModel.lean` (import)
- Scratch: a fixture-size check outside the repository

**Interfaces:**
- Produces: `bitLen : Nat → Nat`, `lpair : Nat → Nat → Nat`, `lfst`, `lsnd`, `lpair_inj`, `lfst_lpair`, `lsnd_lpair`, `bitLen_lpair_le`; `encList`, `encOption`, `encBool` with injectivity lemmas.

- [ ] **Step 1: Definitions.** `bitLen n := if n = 0 then 0 else Nat.log2 n + 1`. `lpair a b := ((((a <<< bitLen b) ||| b) <<< (bitLen b + 1)) ||| (2 ^ bitLen b - 1))`: the low `bitLen b` bits are ones, then one zero bit, then `b`, then `a`. `lfst`, `lsnd` decode by counting the trailing ones. Use only `Nat` operations with kernel acceleration (`<<<`, `>>>`, `|||`, `&&&`, `+`, `-`, `*`, `/`, `%`, `^`, `Nat.log2`). If an equivalent arithmetic form (`a * 2^k + b`) gives simpler proofs, use it and state the equivalence.
- [ ] **Step 2: Laws.** `lfst (lpair a b) = a`, `lsnd (lpair a b) = b`, hence `lpair_inj`. `bitLen (lpair a b) ≤ bitLen a + 2 * bitLen b + 1`. `encList enc (xs)` with `encList_inj` for an injective `enc`; `encOption`, `encBool` likewise. The list code preserves order and duplicates.
- [ ] **Step 3: Size spike.** In a scratch file, build the G02 FG chain shape (three blocks, each with the rows of `SimplexFG/Store.lean:163–212`, rows naming earlier roots) with the new codec and the r203 row encoders (§3), and evaluate the roots with `decide` or `#eval`. Record the bit lengths. **Stop rule:** if B3's root has more than 10^6 bits, or if `decide` on a root comparison does not finish, stop and report; do not continue with Task 1.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainModel`; `#print axioms` for the laws. Commit `Model: linear self-delimiting codec`.

### Task 1: Block with a body; universal root injectivity

**Files:**
- Modify: `AvailableChainModel/Objects/Blocks.lean`
- Modify: `AvailableChainStatements/Generic/Conditions.lean` (docstring of `RootInjective`; new theorem `rootInjective_all`)

**Interfaces:**
- Consumes: Task 0's `lpair`, `lpair_inj`.
- Produces: `Block.node (parent : Block) (slot : Slot) (body : Nat)`; `nodeRoot`; `Block.root`, `Block.body`; `Block.root_injective : Function.Injective Block.root`; `Block.root_ne_genesis_of_node`; `mem_iff_root_mem` (for a list store); `rootInjective_all`.

- [ ] **Step 1: Type.** Change the third argument of `Block.node` to `body : Nat`. `nodeRoot (pr : BlockId) (s : Slot) (x : Nat) : BlockId := ⟨lpair pr.value (lpair s x) + 1⟩`. `Block.root .genesis = genesisRoot`; `Block.root (.node p s x) = nodeRoot p.root s x`. Keep `slot`, `parent?`, `parent`, `depth`, `preceq` and the `Ancestry` section unchanged in shape.
- [ ] **Step 2: Injectivity.** Prove `Block.root_injective` by induction on the first block (r203 §4, with `lpair_inj` for `Nat.pair_eq_pair`). Prove `nodeRoot` never equals `genesisRoot`.
- [ ] **Step 3: Store lookup.** For a list store: `b.parent ∈ blocks ↔ ∃ p ∈ blocks, p.root = b.parent.root`. Add a docstring that states the correspondence with a root-only wire (DC-simplify): every root in the range of `nodeRoot` names exactly one block; a root outside the range never resolves, so its block waits; a root-only adapter later needs only this lemma and a decoder.
- [ ] **Step 4: Three-case lemma for state-free parent reads** (Finding 3; DC-simplify). State it generically: for a state-free predicate `q` on the carried parent, and a store that grows, the outcome of "check `q b.parent` early, then wait for `blockKnown`" equals "wait for `blockKnown`, then check `q` on the stored parent": the lookup succeeds (the stored parent equals the carried parent by injectivity), never succeeds (the block waits or is outside `ExecutionValid`; no delivery obligation either way), or succeeds later (the parent's content is fixed). Put the generic lemma in `AvailableChainModel` (or `AvailableChainStatements/Generic` if it needs the run types) and name it so Tasks 3, 5, 6, 9 can instantiate it.
- [ ] **Step 5: Statements.** `rootInjective_all (E) (I) (rho) : RootInjective E I rho` from `Block.root_injective`. Update the `RootInjective` docstring: it is now a theorem for every run.
- [ ] **Step 6: Checkpoint.** `lake build --wfail AvailableChainModel AvailableChainStatements`. Commit `Model: derived block roots; universal root injectivity`.

### Task 2: Kit, engine v2 sketch, Framework

**Files:**
- Modify: `AvailableChainKit/Engine/HealthyPrefix.lean` (`healthyPrefix_rootInjective` may become `rootInjective_all`; keep the name as a wrapper), `AvailableChainKit/Engine/HealthyInterior.lean`, `AvailableChainKit/Core.lean` (`block_preceq_trans` binder names), `AvailableChainEngineV2/Sketch.lean` (the two folds at :95, :104: body `k`, not root `⟨k+1⟩`), `AvailableChainFramework/Catalog/Mono.lean` (only if it breaks).

- [ ] **Step 1:** Repair constructor binders (a binder that named a root now names a body; do not reuse a `BlockId` term as a body). Keep every statement.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainKit AvailableChainEngineV2 AvailableChainFramework`. `CatalogLock --check` is expected to report CHANGED lines; save its output as the first lock snapshot; do not write. Commit `Kit, EngineV2, Framework: derived roots`.

### Task 3: Grid CO and SA

**Files:**
- Modify: `AvailableChainGridCO/Model/Protocol.lean` (`propose` :287–293: `Block.node parent s 0`), `AvailableChainGridCO/Proofs/Proposals.lean` (:65, :223 statements name the old formula: change to the body-0 node), `AvailableChainGridCO/Proofs/Roots.lean` (`RootInjectiveBelow` and the six scope lemmas: prove from `Block.root_injective`, keep names and statements), the other `AvailableChainGridCO/Proofs/*` files of the survey's list that fail, `AvailableChainGridCO/Tests/Smoke.lean`, `AvailableChainSA/Proofs/{Outage,FastOutage}.lean`, `AvailableChainSA/Tests/Smoke.lean`.

- [ ] **Step 1:** Change `propose`. Rebuild; repair each failing proof. Use named projections, not positional ones, where a conjunction changed.
- [ ] **Step 2:** Instantiate Task 1 Step 4 for `wellFormed` at :337 (`b.parent?.isSome && b.parent.slot < s`).
- [ ] **Step 3: Fixtures.** Smoke `:56, 61, 62, 108`: bodies instead of literal roots; `badChild` keeps "same slot as its parent". SA Smoke `:10–12`: `X` stays a sibling of `B` at slot 1 with a different body. State each order outcome again (Review Focus 4).
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainGridCO AvailableChainSA`; the SA `Tests/Axioms.lean` output is unchanged except for the three standard axioms; plan 1b's WindowMargin and hook facts still build unchanged in statement. Commit `GridCO, SA: derived roots`.

### Task 4: SA-PC

**Files:**
- Modify: `AvailableChainSAPC/Model/Choice.lean` (`propose` :86–87, body 0), `AvailableChainSAPC/Proofs/Proposals.lean` (:55, :106), the SA-PC proof files of the survey's list that fail, `AvailableChainSAPC/Tests/Smoke.lean`, `AvailableChainSAPC/Tests/CleanInvariantCounterexample.lean`.

- [ ] **Step 1:** As Task 3 Step 1. `excludes` stays `fun _ _ => false`, and `receipt_acceptedRelay` keeps its `rfl`.
- [ ] **Step 2:** Instantiate Task 1 Step 4 for `wellFormed` at `Handlers.lean:65`.
- [ ] **Step 3: Fixtures.** `CleanInvariantCounterexample:27–28`: `x` and `y` keep the same parent and slot with different bodies; the docstring at :9 says "its root is larger": choose bodies so that `x.root > y.root` still holds, and prove it by `decide`. The `roots` field at :247 uses `rootInjective_all`. Smoke `:9–12, 97, 151`: bodies.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainSAPC`; `Tests/Axioms.lean` output unchanged except for the standard axioms. Commit `SAPC: derived roots`.

### Task 5: L*

**Files:**
- Modify: `AvailableChainLStar/Model/Protocol.lean` (`propose` :253–259, body 0), `AvailableChainLStar/Proofs/Hooks.lean`, `AvailableChainLStar/Tests/Smoke.lean`.

- [ ] **Step 1:** As Task 3 Step 1. Re-prove `excludes_stable`, `excludes_proposal_iff` and the stored-block clause facts (r203-followups item 1); their statements do not change.
- [ ] **Step 2:** Instantiate Task 1 Step 4 for `wellFormed` at :300.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainLStar`. Commit `LStar: derived roots`.

### Task 6: Registry and witnesses

**Files:**
- Modify: `AvailableChainRegistry/Counter.lean` (:13–15 chain: body `k`), `AvailableChainRegistry/CounterRun.lean` (`chain_root` :287 is false after the change: replace it with an index lemma `chain_injective` or use `Block.root_injective`; `counter_rootInjective` :325–330 becomes `rootInjective_all`), `AvailableChainRegistry/Gaps/NoInput.lean` (`clockBlock` :38–40, `clockBlock_root` :191, `clock_rootInjective` :231–238, the same way; the I1 witness keeps its `KNOWN-GAP` status), `AvailableChainWitnesses/{Sanity,Regimes,Accumulation}.lean`, `AvailableChainRegistry/Instances/*` (re-elaborate only).

- [ ] **Step 1:** Recode the chains. Keep every certificate, refutation and gap row. `Accumulation`: `visible` and `hidden` keep the same parent and slot 1 with different bodies.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainRegistry AvailableChainWitnesses`. `lake env lean --run scripts/Registry.lean` then `--check` exit 0; every row keeps its status (the REGISTRY.md diff may change only hashes or text that names roots). The self-test compare exits 0. Commit `Registry, Witnesses: derived roots`.

### Task 7: SimplexFG

**Files:**
- Modify: `AvailableChainSimplexFG/Objects.lean` (`FGBlock` :43–46: `node (parent) (slot) (body : Nat) (rows : List (Row V))`; `FGBlock.root` derived), `ChainState.lean`, `Frame.lean`, `Store.lean`, `Client.lean` (root reads and inline fixtures).

**Interfaces:**
- Produces: `RowCodec V` (an injective `encodeSigner : V → Nat`); `encRow`, `encFGBody C body rows` (injective in the pair); `FGBlock.root C`; `FGBlock.root_injective`.

- [ ] **Step 1:** Row encoders as r203 §3 lists them, built on Task 0's `lpair` and `encList` (not `Nat.pair`). Every root-valued row field is in the code (`NamedHeightPair`, `FinalityPair`, `Evidence` fields, `Client.Record` fields that the rows carry; r203 §6 SimplexFG).
- [ ] **Step 2:** `FGBlock.root C (.node p s x rows) = nodeRoot (p.root C) s (encFGBody C x rows)`. Thread `C` through the root readers (`process_row`, `derive`, `ViewRootInj`, `lexKey`, `lexMax`, `HeadFields.ofBlock`, `record_row`, `createRow`, `update_finality`). Prove `FGBlock.root_injective`.
- [ ] **Step 3: Fixtures.** Recode B1, BX, B1b, childA, childB, B1c, childC, Y, X, B2, B3, B1', Bs, clientB1alt. The same-root example at `Frame.lean:176–200` (B1a/B1c collision) is impossible now: replace it with a proof that distinct content gives distinct roots, and keep the frame counterexample that it served with a fixture that is still possible. State each order outcome again.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainSimplexFG`. Commit `SimplexFG: FG blocks with a body; derived roots`.

### Task 8: KitFG

**Files:**
- Modify: the ten KitFG files of the survey (`Accountable`, `Ancestry`, `Certificates`, `ClientSafety`, `Correspondence`, `CrossingNoFinal`, `InBandLock`, `Pins`, `Provenance`, `TwoChanges`).

- [ ] **Step 1:** Repair constructor binders and codec arguments. Prove `RootInjectiveOn` and `ViewRootInj` globally from `FGBlock.root_injective`, and keep their public signatures (r203 §6 KitFG).
- [ ] **Step 2:** `Pins.lean`: update the annotations that call root injectivity a run idealization; keep the archived source pins. `bash scripts/check-fg.sh` exits 0. Do not edit `docs/FG-COMPOSITION.md` (DC-simplify owns it); list the entries that need a note in the report.
- [ ] **Step 3: Fixtures.** `TwoChanges:757–767` (`K3`): recode; keep the frame counterexample.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainKitFG`; `check-fg.sh` exit 0. Commit `KitFG: derived roots`.

### Task 9: FG-SA

**Files:**
- Modify: `AvailableChainFGSA/Model/{Objects,Frame,Handlers}.lean`, `AvailableChainFGSA/Statements/Invariants.lean`, `AvailableChainFGSA/Proofs/{Admission,Carrier,CrossNode,StoreInv,Metadata,ActView,BlockAncestry}.lean`, `AvailableChainFGSA/Tests/{Smoke,RootCollision,Axioms}.lean`, `scripts/CheckFGSAAxioms.lean` (names only, if names change).

**Interfaces:**
- Consumes: Task 7's `encFGBody`, `FGBlock.root`; Task 0's `lpair`, `lfst`, `lsnd`, `encList`.
- Produces: `packBody (app : Nat) (rw : List (RowWire n)) : Nat`; `rowsOk b rw : Bool` (the rows component of `b.body` equals the code of `rw`); `eraseFG` with the erasure law `(eraseFG C B).root = B.root C`; `fgBlock` built from checked content; `contentAgree` as a theorem for stores with the strengthened `MetaInv.wireTree`.

- [ ] **Step 1: Content packing** (Finding 2). `packBody app rw := encFGBody finCodec (lpair app (encList encRowWire rw)) (rw.filterMap RowWire.toRow?)`, so the base body binds the ordered signed rows, rounds included (r203 §3). `rowsOk b rw` decodes `b.body` and compares its rows component with `encList encRowWire rw`; the application component is free. Honest `propose` (`Frame.lean:149`) selects the rows first, then builds `Block.node parent s (packBody 0 rw)`.
- [ ] **Step 2: Admission.** `blockAccepted` adds `rowsOk b rows` after `parentFG` succeeds; `wellFormed` (:96) adds `rowsOk b rows` too (a state-free content check, not a root check: it binds content to identity; Global Constraint "no wire root check" is about roots). `fgBlock P b rows` builds the FG node from `b.body`'s decoded application component and the decoded rows, so that `eraseFG (fgBlock P b rows) = b` holds when `rowsOk` and `eraseFG P = b.parent`.
- [ ] **Step 3: Invariants.** `CStoreInv.rootInj` and the second conjunct of `Inv0` are filled by `FGBlock.root_injective` (fields stay). Strengthen `MetaInv.wireTree` with `rowsOk` and prove its preservation by admission. Prove `ContentAgree st st'` for any two stores that satisfy `CStoreInv` and `MetaInv` (r203 §4); `contentAgree_self` becomes a corollary.
- [ ] **Step 4: Proofs.** Redo the r203 §6 FG-SA list: `eraseFG_fgBlock`, `fgBlock_root` (now a theorem from the erasure law, not `rfl`), `fgBlock_rows`, `fgBlock_notMem`, `blockAccepted_of_wellFormed`, `rootTest_iff_blockTest`, `blockAccepted_facts`, `accepted_base_facts`, `fg_on_block_accepts`, `admitProposal_of_accept`, `base_admitProposal_accepts`, then `admitBlock_accepted_eq`, `admitProposal_base_view`, `actView_admitBlock_sameF`, `actView_admitBlock_movedF`, `admitBlock_sufficient`, `admitBlock_sufficient_absent`, and the `Carrier` and `CrossNode` lemmas. Instantiate Task 1 Step 4 for `wellFormed` at :96.
- [ ] **Step 5: Tests.** `RootCollision.lean` (r203 §8): keep `ba`, `c1`, `bb`; prove `ba.root ≠ bb.root`; replace `not_contentAgree` with a positive `ContentAgree stX stY`; show a reader holding `ba` accepts `c1` then `bb`; a repeated `bb` is refused as a duplicate. `Smoke.lean`: packed signed content; the DQ2 case at :208–210 becomes a duplicate test; recompute the order ties at :374–375, :500–501, :571–573 and the expected roots at :432–447, :590–607. New checks (r203 §8): genesis versus a slot-0 node; same parent and slot with different bodies; a wrong rows component is refused and both stores stay unchanged; two row lists with the same decoded rows and different rounds give different roots.
- [ ] **Step 6: Checkpoint.** `lake build --wfail AvailableChainFGSA`; `bash scripts/check-fgsa.sh` exit 0 (all controls still rejected); `Tests/Axioms.lean` standard axioms only. Commit `FGSA: signed content in block identity; ContentAgree proved`.

### Task 10: Documents

**Files:**
- Modify: `docs/FRAMEWORK-DESIGN.md` (§12 I9: "As implemented" note; §2 E4 note that I9 added no exclusion), `docs/CONTRACT.md` (the `RootInjective` premise is now a theorem), `docs/MAP.md`, `docs/GRIDCO-STATUS.md`, `docs/FGSA-STORE-REPORT.md` (DQ2/DQ10/I9 status), `docs/PHASE0-REPORT.md` (Roots row closed).

- [ ] **Step 1:** Dated notes only; the approved text stays. Remove no history. State: roots are derived; the store check is the dependency lookup; the regime root fields are kept and filled by `rootInjective_all`; their removal is a later plan.
- [ ] **Step 2: Checkpoint.** Commit `docs: I9 derived roots`.

### Task 11: Full build, lock, merge

- [ ] **Step 1:** `pgrep -fl lean`; `lake build --wfail` (every default target); `CheckFrameworkAxioms`; `check-fg.sh`; `check-fgsa.sh`; `Registry --check`; the self-test compare; the grep `sorry|admit|native_decide|^axiom` over every changed Lean file (outside `scripts/registry-selftest/`).
- [ ] **Step 2: Lock.** `CatalogLock --check > i9-lock.out`. Compare each CHANGED name with `lock-impact.tsv`. Stop if a name outside the predicted set changed, if any name is REMOVED, or if an ADDED name is in `AvailableChainFramework`. Otherwise `--write --allow-changes`, then `--check` prints nothing. Add a design §8 lock-log entry with the count and the reason (closure through `Block`), and the list of names.
- [ ] **Step 3: Merge.** Merge `i9-derived-roots` into main with `--ff-only` if main has not moved, else a `--no-ff` merge after a trial `git merge-tree` and a full `--wfail` build of the merged tree. Tell DC-simplify before the merge (FG-SA T7 and the FG-COMPOSITION entries depend on it). Remove the worktree after the merge.
- [ ] **Step 4:** The controller writes `docs/I9-REPORT.md`: tasks and commits, checks, the lock break with its names, every statement change, every fixture whose intent changed, and decisions taken without the user.

## Risks

```text
┌────┬────────────────────────────────────────┬──────────────────────────────────────────┐
│ R  │ Risk                                   │ Response                                 │
├────┼────────────────────────────────────────┼──────────────────────────────────────────┤
│ R1 │ The codec's injectivity proof is hard  │ Task 0 first, with a stop rule; the      │
│    │ (bit reasoning)                        │ arithmetic form `a * 2^k + b` is allowed │
│ R2 │ FG roots still too large for decide    │ Task 0 Step 3 measures the worst chain   │
│    │                                        │ before any dependent work                │
│ R3 │ A proof depended on a numeric root     │ Replace with injectivity or an index     │
│    │ (root = height)                        │ lemma; list it in the report             │
│ R4 │ Order outcomes change and a test keeps │ Review Focus 4: restate each winner      │
│    │ passing for a different reason         │                                          │
│ R5 │ FG-SA `fgBlock_root` stops being `rfl` │ Task 9 Step 2 builds `fgBlock` from      │
│    │ and many proofs used that              │ decoded content; the erasure law is the  │
│    │                                        │ replacement                              │
│ R6 │ Main moves during the work (Phase 2    │ Phase 2 plan work is documents only on   │
│    │ plan, T7)                              │ main; T7 waits for Phase 2a, after I9    │
│ R7 │ A lock line outside the predicted set  │ Task 11 stop rule                        │
│    │ changes                                │                                          │
└────┴────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Not in this plan

- Removal of the five regime root fields, `CStoreInv.rootInj` and the `Inv0` conjunct (a later API plan; r203 §9 step 5).
- A root-only wire and its adapter (waits for the P2P spec; Task 1 Step 3 prepares its resolution law).
- An honest external input for the body (Phase 2c, I1).
- Plan 1c items ("deps never present" classification, inhabitation, certificates).

## Audit disposition

(Filled after the Astra audit and the DC-simplify review.)
