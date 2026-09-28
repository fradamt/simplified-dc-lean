# FG-SA Model and Store Facts (Composition T3–T6) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task by task. Steps use checkbox (`- [ ]`) syntax for tracking. Do not start Task 1 before the Astra plan audit (Task 0) is closed.

**Goal:** Build the composite FG-SA node model as pure Lean definitions, and prove its store facts. The model is the plain SA base (GridCO/SA state functions) plus the DC-fj FG store of the FG module, with the filtered base (`act(Σ)`), `reconcile_with_finality`, the `F ⋠ B` refusal, the cumulative tree `Σ.T`, `fastWrite` and the FG source `C_fg`. The proofs are the carrier bridge K5, the store facts K1–K4, and the store form of output nesting (`comp.outputNesting.v2`, K2). This plan covers tasks T3, T4, T5 and T6 of the composition plan. It has no run layer and no engine binding.

**Architecture:** One new Lake library, `AvailableChainFGSA`, with the SA layout:
- `Model/` (LM): definitions and nothing else. `Objects`, `Store`, `Handlers`, `Clock`, `Frame`.
- `Statements/`: the invariants and the public statements (`Prop` values).
- `Proofs/`: the theorems. `BlockAncestry`, `Carrier`, `Fields`, `ActView`, `Nesting`, `Reconcile`, `Admission`, `StoreInv`.
- `Tests/`: `Smoke` (`decide` examples) and `Axioms` (`#print axioms`).

The composite state keeps the SA base as a `GridCO.State n` value (field `base`) and the FG part as a `SimplexFG.Store (Fin n)` value (field `fg`), as SA-PC keeps `base` (`AvailableChainSAPC/Model/Objects.lean:58`). Every SA read and write runs unchanged on `actView st`, the base with its block list filtered to `act(Σ)`. The stored block list stays cumulative. The FG part changes only through `SimplexFG.on_block`. `reconcile` writes only SA fields.

**Tech Stack:** Lean 4 v4.30.0-rc2 and Mathlib v4.30.0-rc2 (`lean-toolchain`). Lake, the module system (`module`, `public import`, `@[expose] public section`).

**Worktree and branch:** `/Users/francesco/worktrees/available-chain-fgsa`, branch `fgsa-composition` (base `d415a7c`). Do not touch `/Users/francesco/ethereum/lean/available-chain`: another session works there on framework plan 1a.

## Sources

`R/` means `/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/`. `AC/` means this worktree.

```text
┌────────────┬──────────────────────────────────────────────┬──────────────────────────────┐
│ Key        │ File                                         │ Version                      │
├────────────┼──────────────────────────────────────────────┼──────────────────────────────┤
│ spec       │ R/spec/fgsa-protocol.tex (AUTHORITY, frozen) │ sha256 2e884811…dc5599adb9787│
│            │ = R/spec/archive/fgsa-protocol-2e884811.tex  │ (see note 1)                 │
│ comp       │ R/codex/lean-composition-plan.md             │ sha256 228dbe98…             │
│ bp00       │ R/blueprint/00-outline.md                    │ sha256 6057f9b5…             │
│ bp01       │ R/blueprint/01-foundations.md                │ sha256 989289cc…             │
│ FG plan    │ AC/docs/plans/2026-09-28-fg-module.md        │ branch base d415a7c          │
│ SA, GridCO │ AC/AvailableChainSA, AC/AvailableChainGridCO │ branch base d415a7c          │
│ FG module  │ AC/AvailableChainSimplexFG,                  │ branch base d415a7c          │
│            │ AC/AvailableChainKitFG                       │                              │
└────────────┴──────────────────────────────────────────────┴──────────────────────────────┘
```

Notes:
1. The spec sha256 is `2e88481117ba3e663c559f95218ce545aba5639f201063c1942dc5599adb9787`. Its archive copy is identical. In this plan, "spec N" is a line number of that file. A revision is in draft (`R/spec/drafts/fgsa-protocol-next.tex`, identical to the frozen file on 2026-09-28). It changes the recovery premises and adds a leak section. It does not change the store or the state machine. If a new frozen version appears before execution, diff it against `2e884811`. Report each changed line in a rule that this plan models. Do not resolve a difference yourself.
2. The FG module pins `alfs4` (`bd942ca0`). The diff from `bd942ca0` to `2e884811` has 56 lines. It changes no FG store rule. It changes three things that this plan models: (a) no rule deletes a block of `Σ.T` (spec 372–377; the FG module and this plan keep the cumulative tree); (b) the signatures of an admitted proposal count in the HEAD merge through the proposal, also when the proposal leaves the active view (spec 190–193); (c) the carried-support arm of the HEAD merge tests `H' ∈ Σ.T`, not `act(Σ)` (spec 423–429).
3. The composition plan cites `bd942ca0` line numbers. This plan cites `2e884811` line numbers.

Spec lines that this plan models:

```text
┌──────────────────────────────────────────┬────────────────┐
│ Rule                                     │ spec lines     │
├──────────────────────────────────────────┼────────────────┤
│ relay, receiver exclusion                │ 169–193        │
│ schedule, a_r = d_{rR}, rows, blocks     │ 197–263        │
│ parameters                               │ 265–335        │
│ store tuple, Trees, act(Σ)               │ 339–379        │
│ block states, FG caches                  │ 381–412        │
│ pools (vote, row), resolution            │ 414–439        │
│ SA fields, fastWrite                     │ 441–461        │
│ reconciliation (prose)                   │ 474–484        │
│ initialization                           │ 486–503        │
│ input validation, acceptance, inclusion  │ 505–556        │
│ outputs, F ⪯ S                           │ 558–575        │
│ HEAD view, frame, walk start, FG action  │ 598–681        │
│ tick order                               │ 683–694        │
│ on_tick, expire, release                 │ 709–752        │
│ update_confirmation, advance, outputs    │ 754–802        │
│ on_block, on_goldfish_vote,              │ 804–857        │
│ on_attestation                           │                │
│ update_finality, reconcile               │ 859–894        │
│ resolution_time … get_head               │ 973–1114       │
│ SA gate helpers                          │ 1118–1206      │
│ duties (voter tree … get_fg_vote)        │ 1210–1338      │
│ client                                   │ 1342–1414      │
└──────────────────────────────────────────┴────────────────┘
```

## Scope and user decisions

This plan does the composition-plan tasks below (comp §7.1, lines 496–549). The composition plan is the design; the blueprint gives the statements and paper proofs (bp00 §3.1, bp01 §§2, 4–7).

```text
┌──────┬──────────────────────────────────────────┬──────────────────────────────┐
│ comp │ Content                                  │ Tasks of this plan           │
├──────┼──────────────────────────────────────────┼──────────────────────────────┤
│ T3   │ Model (LM), comp §4.2–4.6, smoke tests   │ 1, 3, 4, 5, 6                │
│ T4   │ Carrier bridge K5                        │ 2                            │
│ T5   │ Store facts K1–K4; base = Σ.T erased;    │ 7, 9, 10, 11                 │
│      │ actView laws; F monotone                 │                              │
│ T6   │ Output nesting, store form (K2)          │ 8                            │
└──────┴──────────────────────────────────────────┴──────────────────────────────┘
```

User decisions that this plan uses:

```text
┌────┬────────────────────────────────────────┬────────────────────────────────────┐
│ Q  │ Status                                 │ Effect on this plan                │
├────┼────────────────────────────────────────┼────────────────────────────────────┤
│ Q1 │ OPEN (engine v1 or v2)                 │ No dependency. No ProtocolSpec, no │
│    │                                        │ Run, no hooks binding, no Λ field, │
│    │                                        │ no pendingRow. See "Q1 boundary".  │
│ Q2 │ Clean first                            │ No effect on T3–T6. K1 and the SA  │
│    │                                        │ compatibility invariant feed (b1). │
│ Q3 │ ANSWERED: FG module re-pinned on the   │ K4 is short: the FG part IS a      │
│    │ filtered base (fj.frame.v3, one tree)  │ SimplexFG.Store value, changed     │
│    │                                        │ only by on_block. No raw-tree      │
│    │                                        │ correspondence.                    │
│ Q4 │ DONE (blueprint)                       │ Statements follow bp00 §3.1 and    │
│    │                                        │ bp01 §§2, 4–7.                     │
│ Q5 │ OPEN (additive companion)              │ No dependency. No Interface, no    │
│    │                                        │ Claims, no contract bundle.        │
└────┴────────────────────────────────────────┴────────────────────────────────────┘
```

### Q1 boundary

These items depend on the engine version. This plan does not define them. Composition task T7 binds them after Q1.

```text
┌──────────────────────────────────────┬─────────────────────────────────────────┐
│ Deferred item                        │ What this plan gives instead            │
├──────────────────────────────────────┼─────────────────────────────────────────┤
│ ProtocolSpec fgsa, duties, act       │ pure duty functions headVote, propose,  │
│                                      │ attest (Task 6)                         │
│ where Λ lives; when Λ is recorded    │ attest takes Λ and returns (row, Λ′);   │
│ (v1: at the clock tick; v2: E5)      │ State has no Λ field (DQ4)              │
│ own row processed at once (spec 681) │ admitRow is a plain handler (Task 4)    │
│ signer identity of a row (LinkedFG   │ the row signer is the seat index of the │
│ premise on v1; E2 on v2)             │ fg-label signature (Objects, Task 1)    │
│ hooks excludes, handles, depsPresent,│ the store predicate blockExcluded and   │
│ processed, carries                   │ its stability lemma (Tasks 3, 7);       │
│                                      │ wellFormed as a pure input check        │
│ run form of nesting, all run facts   │ Reachable closure of the local steps    │
└──────────────────────────────────────┴─────────────────────────────────────────┘
```

## Review status

DRAFT, 2026-09-29. Not audited. Task 0 runs the Astra plan audit. Record its report and each applied fix here before Task 1.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- Committed proofs use no `sorry`, no `admit`, no project axioms and no `native_decide` (also no `decide +native`, no `ofReduceBool`). A `sorry` body is allowed only between the statement step and the CHECKPOINT of one task. `lake build --wfail` fails on `sorry`. `scripts/CheckFGSAAxioms.lean` (Task 2) rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound`. `scripts/check-fgsa.sh` (Task 1) scans for native evaluation outside comments.
- Kernel checks use `decide`, `decide +kernel`, `decide_cbv` or `rfl`. If `decide` is slow on a smoke test, first make the test a `Bool` value (`def t : Bool := …` and `example : t = true := by decide`, as `AvailableChainSA/Tests/Smoke.lean`), then try `decide +kernel`. Report each fallback.
- New code goes only in the new library `AvailableChainFGSA`, in new scripts `scripts/check-fgsa.sh` and `scripts/CheckFGSAAxioms.lean`, in one appended `[[lean_lib]]` block of `lakefile.toml`, and (Task 12) in `defaultTargets` and one new section of `docs/MAP.md`. Do not edit any file of another library. Do not edit `docs/FG-COMPOSITION.md`, `docs/FRAMEWORK-DESIGN.md`, the FG scripts, or `decoupled-consensus/`.
- Do not import `AvailableChainFramework`, `AvailableChainRegistry`, `AvailableChainStatements`, `AvailableChainWitnesses` or `AvailableChainSAPC`. Plan 1a changes the first two. The allowed imports are: `AvailableChainModel.*`, `AvailableChainGridCO.Model.Protocol`, `AvailableChainGridCO.Proofs.*` (in `Proofs/` only), `AvailableChainSA.Model.Protocol`, `AvailableChainSimplexFG`, `AvailableChainKitFG.*` (in `Statements/` and `Proofs/` only), and Mathlib. Import the smallest module that has the declaration.
- Model files (`Model/`) hold definitions only. No theorem with a proof goes in `Model/`. Examples go in `Tests/Smoke.lean`. `Statements/` holds invariant definitions and `Prop` statements. `Proofs/` holds the theorems (lean/AGENTS.md: keep executable definitions, public statements and proofs apart).
- Namespace `AvailableChain.FGSA` for `Model`, `Statements` and `Proofs`; `AvailableChain.FGSA.Tests` for `Tests`.
- Every new `.lean` file starts with `module`, the `public import` lines, a blank line, `@[expose] public section`, a blank line, `namespace …`. It ends with `end …` then `end`.
- Root imports. Each task that creates a `.lean` file adds `public import <module>` to `AvailableChainFGSA.lean` in the same commit. At each CHECKPOINT this must print nothing:
  `comm -23 <(find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) <(grep -o 'import [A-Za-z.]*' AvailableChainFGSA.lean | sed 's/import //' | sort)`
- Builds. The Mac `lean` has 3 machine-wide slots (`LEAN_SLOTS=3`). Before each build run `pgrep -fl lean`; if 3 compiles run, wait (use `ps -o etime,%cpu -p <pids>` to tell a slow build from a blocked one). During a step, build one module: `lake build --wfail AvailableChainFGSA.Model.Store` (module targets build only that module and its imports). At each CHECKPOINT: `lake build --wfail AvailableChainFGSA`. At Task 12 only: the full project target `lake build --wfail`. Do not add a `lean_exe` target. Run scripts with `lake env lean --run <file>.lean`.
- Faithfulness. The spec is the authority. Each model definition has a docstring that names its spec lines, for example ``[spec 804–829]``. A proof docstring names its blueprint id and K id, for example ``[bp bp.reconcile.v1; K3]``, or ``[helper]``. Do not change a statement to make a proof pass. A difference from the spec, the blueprint or the composition plan is a finding: report it in the task report and do not resolve it.
- Leak-ledger readiness. A later revision adds a leak ledger as a DERIVED function of the chain (`R/codex/round-leak.md`: "All snapshots and charges are derived from the chain"; the ledger "does not change weights"). So: the model stores no derived value that the spec does not store; `σ[B]` stays `SimplexFG.derive E cfg B` (never a cached field); each FG block keeps its full ordered row list; the stored proposals keep the full signed rows with their rounds; the electorate stays a parameter. Then `leakLedger : FGBlock (Fin n) → …` can be added in a new file without a change to `State` or to a handler.
- Q1/Q5 independence. No file of this plan mentions `ProtocolSpec`, `Run`, `World`, `Env`, `Interface`, `Claims`, `pendingRow` or an engine field. `grep -rnE 'ProtocolSpec|Generic\.Run|World|pendingRow' AvailableChainFGSA` must print nothing at each CHECKPOINT.
- Each task ends at a CHECKPOINT:
  - the library build is green;
  - `bash scripts/check-fgsa.sh` exits 0 (from Task 1; from Task 2 it also runs the axiom check);
  - the root-import check and the Q1/Q5 grep print nothing;
  - the independent review gate of the task is passed (see "Review gates");
  - the task is committed on `fgsa-composition` with the message `FGSA model: <task title>`, and only the task's files are staged. Each commit message ends with the attribution line of the executing session.
- Prose in comments and docs: ASD-STE100 Simplified Technical English. Tables: Unicode box drawing in fenced `text` blocks.

## Design decisions of this plan

These decisions refine comp §4. Each one names what it changes in comp §4, if anything.

```text
┌─────┬───────────────────────────────────┬────────────────────────────────────────────┐
│ ID  │ Decision                          │ Reason                                     │
├─────┼───────────────────────────────────┼────────────────────────────────────────────┤
│ M1  │ base : GridCO.State n (cumulative │ comp D2, D3. GridCO proofs need a growing  │
│     │ erased Σ.T); fg : SimplexFG.Store │ block list (ReceiptPrefix). K4 is then the │
│     │ (Fin n) (the FG caches and Σ.T)   │ FG module's own StoreInv (Q3 answered).    │
│ M2  │ actView st = base with blocks     │ comp §4.2 last item; spec 363–366.         │
│     │ filtered to compatibility with    │ resolvedBefore, confirmation, gate,        │
│     │ eraseFG F; onView f runs a GridCO │ release, prefix support then read act(Σ)   │
│     │ step on actView and restores the  │ with no change to SA code.                 │
│     │ cumulative block list             │                                            │
│ M3  │ The proposal wire carries the     │ comp §4.2 Msg. The FG block is built at    │
│     │ erased Block b, the vote lists    │ admission from the stored parent (spec     │
│     │ and its own signed rows; the FG   │ 519–522: "the parent is the block that the │
│     │ block is .node P b.slot b.root    │ store holds under the root B.parent").     │
│     │ rows′ with P the stored parent    │ See DQ1.                                   │
│ M4  │ A row wire is Signed Label n      │ spec 230–237: a = (valindex, round, …).    │
│     │ RowBody with auth .seat (.fg r) i:│ The round is the label; the identity is    │
│     │ round r, identity i : Fin n       │ the seat index (comp D5). How i binds to a │
│     │                                   │ validator is a run premise (Q1).           │
│ M5  │ The duplicate test of on_block    │ spec 167, 521: roots are distinct. With    │
│     │ refuses a block whose ROOT is     │ this test Σ.T is root-injective by         │
│     │ already in Σ.T                    │ construction; ViewRootInj Σ.T follows with │
│     │                                   │ no hypothesis. See DQ2.                    │
│ M6  │ reconcile runs inside the         │ comp D7; spec 867–871. It writes only SA   │
│     │ accepted branch of admitBlock,    │ fields and S.                              │
│     │ right after on_block, when F      │                                            │
│     │ changed; the row handlers run     │                                            │
│     │ after it                          │                                            │
│ M7  │ The composite gate: evaluate once │ spec 756–781 (the "s ∉ dom genuine" test   │
│     │ (skip if the label is saved);     │ and the final S rule). SA.gate itself has  │
│     │ SA.gate on actView; fastWrite[s]  │ no once-guard. See DQ5.                    │
│     │ from the fast test, also empty;   │                                            │
│     │ then S := F if F ⋠ S              │                                            │
│ M8  │ The clock follows GridCO.clock    │ SA-PC precedent (AvailableChainSAPC/Model/ │
│     │ step by step: expire on base;     │ Protocol.lean:48). Freeze and early caches │
│     │ freeze, early, release on         │ keep the SA base shape for later reuse;    │
│     │ actView; then the composite gate  │ no duty reads a cached resolved flag.      │
│ M9  │ Duties are pure functions of the  │ comp §4.5; spec 1210–1338. The HEAD reads  │
│     │ state; they read the live frame   │ resolution at read time (spec 429–430).    │
│     │ storeControls and derive every    │                                            │
│     │ pool from stamps at read time     │                                            │
│ M10 │ No Λ field and no pendingRow      │ spec 352–353 (Λ is not part of the store); │
│     │                                   │ Q1. See DQ4.                               │
└─────┴───────────────────────────────────┴────────────────────────────────────────────┘
```

## Open design questions

Each question has a recommended answer. The plan follows the recommendation. The Astra audit (Task 0) and the user can change it before Task 1.

- **DQ1. Block wire form.** (a) Flat: the wire carries the erased `Block b` and its own rows; the FG block is built from the stored parent (M3; comp §4.2). (b) Recursive: a new inductive `FullBlock n` with full rows at every ancestor, and two projections `fg` and `erase` (bp01 §2.1). **Recommendation: (a).** The HEAD walk and the proposer work on erased blocks (`GridCO.ghost`), so the proposer's parent is an erased block in both forms, and (b) needs a lookup anyway. (a) keeps one erasure (`eraseFG`), and K5 is about `eraseFG` only. The rows of stored blocks stay available with their rounds in `st.proposals`. The blueprint's `eraseFG (fg B) = erase B` becomes `eraseFG (fgBlock P b rows) = b` (Task 11).
- **DQ2. Duplicate test.** (a) By root: refuse if some `Y ∈ Σ.T` has `Y.root = b.root` (M5). (b) By erased block: refuse if `b` is in the base list, and carry `ViewRootInj Σ.T` as a hypothesis of every store lemma. **Recommendation: (a).** Under the spec's root idealization (spec 167, 521) the two tests agree. (a) makes `Σ.T` root-injective by construction, so `KitFG.storeInv_on_block` gets its `ViewRootInj` premise from the invariant, and no store fact needs a collision hypothesis. The price: a faulty block with a reused root is refused even if its content is new. That is outside the spec's model. At run level, the AC condition `RootInjective` (distinct roots in a run) makes the extra refusal never fire for an honest block.
- **DQ3. Content-bound roots (comp D4).** (a) A model check `b.root = code(parent root, slot, rows)`. (b) No model check; a content-root premise at run level. **Recommendation: (b), deferred to T7.** The store facts of this plan need no content premise (DQ2). The cross-node question (two nodes admit two different row lists under one root) is a run question. A code check needs an injective `Nat` encoding of rows and makes every smoke-test root a computed code. Composition task T1 already asks the registry for the content-root idealization.
- **DQ4. Where Λ lives.** (a) Not in `State`; `attest` takes `Λ` and returns `(row, Λ′)`; T7 defines the node state (for example `structure NodeState extends State n where record : Record`). (b) A `record` field in `State`. **Recommendation: (a).** Spec 352–353 says Λ is not part of the store. `SimplexFG.Record` holds functions, so a `State` with it has no `Repr`. The choice of the write point (v1 clock tick or v2 `recordOwn`) is Q1.
- **DQ5. Evaluate-once guard at the gate.** (a) The composite gate skips the SA gate when `savedGenuine st.base s` is `some _` (spec 756). (b) Call `SA.gate` always, as SA does. **Recommendation: (a).** It is the spec text. It also makes `fastWrite[s]` "created once" (spec 458–460). On a run with one tick per public time the two agree. Task 7 proves the bridge `clock_eq_saClock` with the premise "the label is not saved".
- **DQ6. HEAD block view.** (a) Compute the spec's `voter_processed_block_tree` from `Σ.T` and the base block stamps at read time. (b) Read GridCO's `frozen` block cache. **Recommendation: (a).** It is the spec form (spec 1219–1226). The freeze cache holds only active blocks at `z_{s−1}`; (a) and (b) give the same filtered tree because F only grows and the filter requires `F ⪯ B`, but that is a lemma that no task needs.
- **DQ7. Output-nesting reading for T6.** The task text says "F ⪯ S ⪯ available". **Recommendation:** read it as `comp.outputNesting.v2` (bp00 §3.1): at every reachable state `F ⪯ S`, and both available accessors (`confirmed`, `stable`) equal S. The spec has no third output (spec 558–569). Task 8 also proves the accessor form `comp.outputNesting.v1`.
- **DQ8. The SA record G (`goldfishRecord`).** The spec has no G. SA keeps it. **Recommendation:** keep the field (the SA gate writes it through `onView`); `reconcile` does not touch it; no FG-SA output reads it. Report this as a declared model field, not a spec rule.
- **DQ9. Hooks.** **Recommendation:** define no engine hook in this plan. Give the store predicate `blockExcluded` (DC `NamedReceipt.excludes`: a proposal block incompatible with F) and prove its stability (Task 7). Give the spec input check as the pure function `wellFormed` (Task 4). T7 binds both.
- **DQ10. Honest proposal root.** **Recommendation:** use the GridCO formula `⟨s * (parent.root.value + 1)⟩` (`GridCO.propose`). Distinct roots are a run premise (DQ3). Report it as an idealization.
- **DQ11. Pin tags.** The blueprint ids (`bp.*`, `comp.outputNesting.v2`) are not yet in `docs/FG-COMPOSITION.md` (composition task T1). **Recommendation:** use docstring tags ``[bp <id>; K<k>]`` and ``[spec <lines>]`` now. Build a pin table and a checker in composition task T15, after T1.
- **DQ12. A carried row with a wrong signature form.** **Recommendation:** `admitBlock` refuses a block that carries a row whose auth is not `.seat (.fg r) i` (it folds that part of the input check into the refusal). Under the spec's input check (spec 505–518) this never fires. Then `fgBlock` never drops a row.

## Tree-read inventory (Review Focus 1)

Every consumer must read the right block set. This is bp00 §2.4 with the Lean name of each read.

```text
┌───────────────────────────┬──────────────────────────────────┬─────────────────────────────────┐
│ Consumer                  │ Spec read                        │ Lean (this plan)                │
├───────────────────────────┼──────────────────────────────────┼─────────────────────────────────┤
│ Confirmation / gate       │ act(Σ), walk from genesis, no FJ │ SA.gate via onView (actView)    │
│                           │ band                             │                                 │
│ Release / resolution      │ active heads, original stamps    │ SA.release via onView;          │
│                           │                                  │ GridCO.resolvedBefore (actView) │
│ Late count / equivocation │ signed votes, no active test     │ base.votes (actView keeps them) │
│ H / contest / frame       │ cumulative Σ.T and live caches   │ storeControls p.E p.cfg st.fg   │
│ V_s block view            │ pre-z_{s−1} blocks ∪ current     │ voterBlocks (st.fg.TF, base     │
│                           │ proposal paths                   │ block stamps)                   │
│ HEAD raw merge            │ frozen votes + every current     │ headVotes (st.proposals, no act │
│                           │ proposal in Σ.T                  │ filter; spec 190–193)           │
│ Frozen support            │ active resolution before z_{s−1},│ headSupport, frozen arm, on     │
│                           │ tested at read time              │ actView                         │
│ Carried support           │ original declaration; head in    │ headSupport, carried arm,       │
│                           │ Σ.T, valid slot                  │ blockKnown st.base              │
│ Proposal / finality head  │ full filtered tree D_Σ(Σ.T);     │ getHead with fullTree;          │
│                           │ active resolved support          │ support on actView              │
│ live_root                 │ deepest live lease in D_Σ(Σ.T),  │ liveRoot                        │
│                           │ else Z                           │                                 │
│ C_fg at a_r               │ deepest live fastWrite[rR]       │ fgSource                        │
│                           │ member in D_Σ(Σ.T)               │                                 │
│ Row inclusion             │ row pool + original rows of      │ proposalRows (rowPool,          │
│                           │ blocks in Σ.T                    │ st.proposals)                   │
└───────────────────────────┴──────────────────────────────────┴─────────────────────────────────┘
```

## Review Focus

1. **The tree-read inventory above.** A reviewer checks each row against the Lean definition.
2. **Refusal before any write** (spec 530–536, 806–817). A refused block changes nothing: no base block, no stamp, no carried vote, no row, no FG change. Test: Task 4, a conflicting block that carries a raw vote.
3. **reconcile writes only SA fields and S** (spec 474–484, 874–894; K3). It keeps the evaluated label of an emptied result; it never moves a lease or writes `F` into a saved result. Test: Task 4 (through a block delivery) and Task 3 (direct).
4. **S := F after every gate and every F advance** (spec 563–568, 778–781, 890–892). Also after an empty or vetoed gate. Test: Task 5.
5. **fastWrite[rR] is created at the gate, also empty; there is no older-set fallback** (spec 458–460, 669–677). Test: Task 6, the `C_fg` empty case.
6. **The live frame comes from the full store** (spec 616–646). The HEAD applies it to its own block view; it does not recompute controls from the view. Test: Task 6, a HEAD that takes a child by band eligibility.
7. **Resolution at read time** (spec 429–430). The HEAD's frozen support tests the CURRENT `act(Σ)`, not the one at the freeze. Test: Task 6.
8. **The root-based duplicate test** (DQ2). Test: Task 4, a new block with a stored root and a different parent is refused.

## File structure

```text
┌──────────────────────────────────────────────┬──────────────────────────────────────────┐
│ File                                         │ Responsibility                           │
├──────────────────────────────────────────────┼──────────────────────────────────────────┤
│ lakefile.toml                                │ one appended lean_lib block; default     │
│                                              │ target at Task 12                        │
│ AvailableChainFGSA.lean                      │ library root (imports every file)        │
│ AvailableChainFGSA/Model/Objects.lean        │ Params, Label, RowBody, wires, Msg,      │
│                                              │ eraseFG, base conversions, rounds        │
│ AvailableChainFGSA/Model/Store.lean          │ State, initial, outputs, actView,        │
│                                              │ onView, normalizeS, reconcile, lease and │
│                                              │ fastWrite reads, blockExcluded           │
│ AvailableChainFGSA/Model/Handlers.lean       │ admitHead, admitRow, parentFG, fgBlock,  │
│                                              │ blockAccepted, admitBlock, process,      │
│                                              │ wellFormed                               │
│ AvailableChainFGSA/Model/Clock.lean          │ fastSet, gateStep, clock                 │
│ AvailableChainFGSA/Model/Frame.lean          │ controls, fullTree, liveRoot, eligible,  │
│                                              │ headInTree, voterBlocks, headVotes,      │
│                                              │ headSupport, headVote, getHead,          │
│                                              │ proposalRows, propose, fgHead, fgSource, │
│                                              │ fgInputs, attest                         │
│ AvailableChainFGSA/Statements/Invariants.lean│ Reachable, NestOK, SACompat, CStoreInv   │
│ AvailableChainFGSA/Statements/Store.lean     │ OutputNestingStored, StoreInvariant,     │
│                                              │ FMonotone (Prop statements)              │
│ AvailableChainFGSA/Proofs/BlockAncestry.lean │ public Block ancestry lemmas             │
│ AvailableChainFGSA/Proofs/Carrier.lean       │ K5                                       │
│ AvailableChainFGSA/Proofs/Fields.lean        │ write sets of every step; SA bridge      │
│ AvailableChainFGSA/Proofs/ActView.lean       │ actView laws, bp.activeView.v1           │
│ AvailableChainFGSA/Proofs/Nesting.lean       │ K2, comp.outputNesting.v1/v2             │
│ AvailableChainFGSA/Proofs/Reconcile.lean     │ K1, K3, exact effects, idempotence       │
│ AvailableChainFGSA/Proofs/Admission.lean     │ refusal and accept-branch agreement      │
│ AvailableChainFGSA/Proofs/StoreInv.lean      │ K4, base = Σ.T erased, F monotone,       │
│                                              │ SACompat                                 │
│ AvailableChainFGSA/Tests/Smoke.lean          │ decide examples (grown by Tasks 1–6)     │
│ AvailableChainFGSA/Tests/Axioms.lean         │ #print axioms of every public theorem    │
│ scripts/check-fgsa.sh                        │ build, root imports, native scan, Q1     │
│                                              │ grep, axiom check                        │
│ scripts/CheckFGSAAxioms.lean                 │ axioms of every compiled FGSA constant   │
└──────────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Task list

```text
┌─────┬──────────────────────────────────┬──────┬──────────┬──────────┬────────────────┐
│ #   │ Task                             │ comp │ Size     │ Depends  │ Parallel with  │
├─────┼──────────────────────────────────┼──────┼──────────┼──────────┼────────────────┤
│ 0   │ Preconditions; Astra plan audit  │ —    │ —        │ —        │ —              │
│ 1   │ Library skeleton and objects     │ T3   │ S 0.15k  │ 0        │ —              │
│ 2   │ Block ancestry and carrier K5    │ T4   │ S–M      │ 1        │ 3–6            │
│     │                                  │      │ 0.3–0.5k │          │                │
│ 3   │ Store: state, act(Σ), reconcile, │ T3   │ S 0.2k   │ 1        │ 2              │
│     │ outputs                          │      │          │          │                │
│ 4   │ Handlers: votes, rows, blocks    │ T3   │ M 0.3k   │ 3        │ 2              │
│ 5   │ Clock and composite gate         │ T3   │ S 0.2k   │ 3        │ 2, 4           │
│ 6   │ Frame reads and duties; Astra    │ T3   │ M        │ 4, 5     │ 2              │
│     │ model check                      │      │ 0.4–0.5k │          │                │
│ 7   │ Write sets, actView laws, SA     │ T5   │ M        │ 2, 6     │ —              │
│     │ bridge                           │      │ 0.4–0.6k │          │                │
│ 8   │ Output nesting (K2), store form  │ T6   │ S 0.2k   │ 7        │ 9              │
│ 9   │ Reconcile facts (K1, K3)         │ T5   │ M        │ 7        │ 8              │
│     │                                  │      │ 0.3–0.4k │          │                │
│ 10  │ Admission agreement              │ T5   │ M        │ 2, 7     │ 8, 9           │
│     │                                  │      │ 0.3–0.4k │          │                │
│ 11  │ Composite store invariant (K4),  │ T5   │ M–L      │ 8, 9, 10 │ —              │
│     │ F monotone, SA compatibility     │      │ 0.5–0.8k │          │                │
│ 12  │ Axiom audit, full build, MAP,    │ —    │ S        │ 11       │ —              │
│     │ handoff                          │      │          │          │                │
└─────┴──────────────────────────────────┴──────┴──────────┴──────────┴────────────────┘
```

Sizes are Lean lines, with tests. Total: about 3.3–4.3k lines (model 1.1–1.3k, proofs 2.0–2.8k, tests 0.3k). The composition plan estimated 0.8–1.2k (T3), 0.3–0.6k (T4), 0.8–1.5k (T5) and S (T6); the model is at the top of its range because the duties (Task 6) are complete. Critical path: 0 → 1 → 3 → 4 → 6 → 7 → 10 → 11 → 12.

---

### Task 0: Preconditions and the Astra plan audit

**Files:** none in Lean. The audit report goes to `docs/audit/fgsa-model-store-plan-audit.md` (written by the Astra job).

- [ ] **Step 1: Check the base.** In the worktree: `git status` is clean; the branch is `fgsa-composition`; `git log -1` contains this plan's commit. `shasum -a 256 R/spec/fgsa-protocol.tex` gives `2e884811…`. If not, stop and report (Sources, note 1).
- [ ] **Step 2: Check the FG module state.** `grep -n 'structure Store' -A8 AvailableChainSimplexFG/Store.lean` shows one tree `TF` and no raw tree (Q3). `grep -n 'theorem storeInv_on_block\|theorem storeControls_eq_fjControls\|theorem update_finality_F_mono\|def pickPair\|theorem pickPair_eq_of_unique\|theorem ancestor_closed_of_parent_closed' AvailableChainKitFG/Correspondence.lean AvailableChainSimplexFG/Frame.lean` finds each name. If a name moved, update this plan before Task 1.
- [ ] **Step 3: Astra plan audit (review gate G0).** Start a Codex job with the astra model (memory: "use astra freely when beneficial"; see the `codex-teammate` skill). The job reads this plan, the spec (`2e884811`), comp §4 and §5 (lines 209–466), bp00 §2 and §3.1, bp01 §§2, 4–7 and the Lean sources that the plan names. It checks: (a) each model definition against its spec lines, with the tree-read inventory; (b) each statement against its blueprint statement; (c) that no step depends on Q1 or Q5; (d) the recommended answers of DQ1–DQ12; (e) that each cited Lean name exists with the stated signature. Output: a report with findings graded blocking, major, minor, and a verdict ADOPT, ADOPT WITH FIXES or REVISE.
- [ ] **Step 4: Apply the audit.** Fix every blocking and major finding in this plan. Record the report, the fixes and the open minor findings under "Review status". A REVISE verdict needs a second audit of the changed sections. Commit the plan change: `FGSA plan: Astra audit fixes`.

---

### Task 1: Library skeleton and objects

**Files:**
- Modify: `lakefile.toml` (append the block below; do NOT add it to `defaultTargets` until Task 12)
- Create: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Model/Objects.lean`, `AvailableChainFGSA/Tests/Smoke.lean`, `scripts/check-fgsa.sh`

**Interfaces:**
- Consumes: `SA.Params`, `SA.gateTime`, `SA.voteTime`, `GridCO.HeadWire`, `GridCO.Wire`, `GridCO.fromHead`, `SimplexFG.{NamedHeightPair, FinalityPair, Row, FGBlock, Electorate, FGConfig}`, `AvailableChain.{Block, Signed, Auth}`.
- Produces: `Params` (with `E`, `cfg`, `round`, `actionTime`, `slotOf`), `Label` (with `actTime`), `RowBody`, `HeadWire`, `RowWire` (with `round?`, `toRow?`), `RowBody.ofRow`, `Msg`, `Wire`, `eraseFG`, `baseAuth`, `baseHead`, `baseVote`, `liftHead?`, `baseProposal`.

- [ ] **Step 1: Add the library.** Append to `lakefile.toml`:

```toml
# FG-SA composite model (LM), store statements and store proofs
# (docs/plans/2026-09-29-fgsa-model-store.md). No engine binding.
[[lean_lib]]
name = "AvailableChainFGSA"
```

- [ ] **Step 2: Write the failing tests.** Create `AvailableChainFGSA.lean` with `public import AvailableChainFGSA.Model.Objects` and `public import AvailableChainFGSA.Tests.Smoke`. Create `AvailableChainFGSA/Tests/Smoke.lean` (imports `AvailableChainFGSA.Model.Objects`; namespace `AvailableChain.FGSA.Tests`; `open AvailableChain.SimplexFG`) with the fixture and the object tests:

```lean
/-- The test parameters: Δ = 1, n = 4, k = 2, R = 2, w_F = 1, δ_t = 1.
`pT.cfg` is the FG module's `cfg1` and `pT.E` is its `E4`, so the FG test
blocks `B1`, `B2`, `B3`, `B1'` of `AvailableChainSimplexFG` apply. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, wF := 1, δt := 1, RLarge := by decide, wFPos := by decide }

/-- A signed FG row of round `r` by identity `i`. -/
def rw (r : Nat) (i : Fin 4) (a : Row (Fin 4)) : RowWire 4 :=
  ⟨.seat (.fg r) i, RowBody.ofRow a⟩

example : eraseFG B1 = Block.node .genesis 1 ⟨1⟩ := by decide
example : (rw 0 2 (rowT 2)).toRow? = some (rowT 2) := by decide
example : (rw 0 2 (rowT 2)).round? = some 0 := by decide
/-- `a_r = d_{rR}` (spec 217–220): with R = 2, `a_1 = d_2 = 4·2 + 6 = 14`. -/
example : pT.actionTime 1 = 14 := by decide
example : (Label.fg 1).actTime pT = 14 ∧ (Label.head 3).actTime pT = 13 := by decide
/-- At `a_1 = 14` the store slot is `rR + 1 = 3`, still round 1 (spec 1306, 1317). -/
example : pT.slotOf 14 = 3 ∧ pT.round 3 = 1 := by decide
example : baseAuth (n := 4) (.seat (.head 3) 1) = .seat 3 1 ∧
    baseAuth (n := 4) (.seat (.fg 3) 1) = .none := by decide
```

Run: `lake build AvailableChainFGSA.Tests.Smoke`. Expected: FAIL (unknown identifiers).

- [ ] **Step 3: Write `Model/Objects.lean`.** Imports: `AvailableChainSA.Model.Protocol`, `AvailableChainSimplexFG.Store`, `AvailableChainSimplexFG.Client`. Namespace `AvailableChain.FGSA`; `open AvailableChain.Generic AvailableChain.SimplexFG`.

```lean
/-- [spec 265–335] FG-SA parameters: the SA parameters (`Δ`, `n`, `k`, `η`), the
round length `R ≥ 2`, the row window `w_F ≥ 1` and the timeout delay `δ_t ≥ 0`
(`δ_t = 0` is allowed; no statement may need `δ_t > 0`). -/
structure Params extends SA.Params where
  R : Nat
  wF : Nat
  δt : Nat
  RLarge : 2 ≤ R
  wFPos : 1 ≤ wF

namespace Params
/-- [spec 154–158] Unit weights on the fixed identities `V = Fin n`. -/
def E (p : Params) : Electorate (Fin p.n) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
/-- [spec 283] The FG configuration: the timeout delay `δ_t`. -/
def cfg (p : Params) : FGConfig := ⟨p.δt⟩
/-- [spec 209] `round(s) = ⌊s / R⌋`. -/
def round (p : Params) (s : Slot) : Nat := s / p.R
/-- [spec 217–220] `a_r = T_r + 6Δ = d_{rR}`. -/
def actionTime (p : Params) (r : Nat) : Time := SA.gateTime p.toParams (r * p.R)
/-- [spec 711] `Σ.s = ⌊t / 4Δ⌋`, as `GridCO.admitProposal` computes it. -/
def slotOf (p : Params) (t : Time) : Slot := (t / (4 * p.Δ)).toNat
end Params

/-- [comp §4.2] Duty labels: the HEAD of slot `s` and the FG action of round `r`. -/
inductive Label where
  | head (s : Slot)
  | fg (r : Nat)
  deriving DecidableEq, Repr

/-- [spec 197–220] The act time of a label: `v_s` for a HEAD, `a_r` for an FG
action. The two families never share a time. -/
def Label.actTime (p : Params) : Label → Time
  | .head s => SA.voteTime p.toParams s
  | .fg r => p.actionTime r

/-- [spec 230–237] An FG row without its identity and round: the height pair and
the finality pair. The identity is the seat index and the round is the label of
the row's signature (M4). -/
structure RowBody where
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

def RowBody.ofRow {V : Type} (a : Row V) : RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [spec 225–228] A signed Goldfish vote, as a block carries it. -/
abbrev HeadWire (n : Nat) := Signed Label n Block
/-- [spec 230–237] A signed FG row. Its auth is `.seat (.fg r) i`. -/
abbrev RowWire (n : Nat) := Signed Label n RowBody

namespace RowWire
variable {n : Nat}
/-- The round of a row: the label of its signature. -/
def round? (a : RowWire n) : Option Nat :=
  match a.auth with
  | .seat (.fg r) _ => some r
  | _ => none
/-- The FG row: the signer is the seat index of the fg-label signature. -/
def toRow? (a : RowWire n) : Option (Row (Fin n)) :=
  match a.auth with
  | .seat (.fg _) i => some ⟨i, a.payload.height_pair, a.payload.finality_pair⟩
  | _ => none
end RowWire

/-- [spec 225–263; comp §4.2] The payloads. A proposal carries the erased block,
the previous-slot votes, the declared support subset and its own signed rows
(M3). -/
inductive Msg (n : Nat) where
  | head (target : Block)
  | proposal (b : Block) (view supportView : List (HeadWire n)) (rows : List (RowWire n))
  | row (body : RowBody)
  deriving DecidableEq, Repr

abbrev Wire (n : Nat) := Signed Label n (Msg n)

/-- [bp bp.carrier.v1] The geometric erasure of an FG block (bp01 §2.1 `eraseFG`). -/
def eraseFG {V : Type} : FGBlock V → Block
  | .genesis => .genesis
  | .node p s r _ => .node (eraseFG p) s r

/-- [helper] The base auth: a HEAD seat of slot `s` is a seat of base label `s`;
a proposer key is unchanged; an FG seat is not a base signature. -/
def baseAuth {n : Nat} : Auth Label n → Auth Slot n
  | .seat (.head s) i => .seat s i
  | .seat (.fg _) _ => .none
  | .proposer s => .proposer s
  | .none => .none

def baseHead {n : Nat} (o : HeadWire n) : GridCO.HeadWire n := ⟨baseAuth o.auth, o.payload⟩
def baseVote {n : Nat} (o : HeadWire n) : GridCO.Wire n := GridCO.fromHead (baseHead o)
/-- [helper] A base vote as a composite carried vote (for the proposer's lists). -/
def liftHead? {n : Nat} (o : GridCO.Wire n) : Option (HeadWire n) :=
  match o.auth, o.payload with
  | .seat s i, .head b => some ⟨.seat (.head s) i, b⟩
  | _, _ => none
/-- [helper] The base proposal of a composite proposal wire (as SA-PC `baseProposal`). -/
def baseProposal {n : Nat} (o : Wire n) (b : Block) (raw support : List (HeadWire n)) :
    GridCO.Wire n :=
  ⟨baseAuth o.auth, .proposal b (raw.map baseHead) (support.map baseHead)⟩
```

  If `structure Params extends SA.Params` does not give `p.Δ`, `p.n` and `p.toParams`, report it and use an explicit field `sa : SA.Params` with the same names in the rest of the plan.

- [ ] **Step 4: Write `scripts/check-fgsa.sh`.**

```bash
#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the Q1/Q5 boundary grep, and (once present) the axiom check.
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== lake build --wfail AvailableChainFGSA"
lake build --wfail AvailableChainFGSA
echo "== root imports"
missing=$(comm -23 \
  <(find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) \
  <(grep -o 'import [A-Za-z.]*' AvailableChainFGSA.lean | sed 's/import //' | sort))
[ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; exit 2; }
echo "== native evaluation"
status=0
for f in $(find AvailableChainFGSA -name '*.lean') AvailableChainFGSA.lean; do
  if perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== Q1/Q5 boundary"
if grep -rnE 'ProtocolSpec|Generic\.Run|World|pendingRow|AvailableChainFramework|AvailableChainRegistry' AvailableChainFGSA AvailableChainFGSA.lean; then
  echo "ENGINE OR FRAMEWORK REFERENCE"; exit 1
fi
if [ -f scripts/CheckFGSAAxioms.lean ]; then
  echo "== axioms"
  lake env lean --run scripts/CheckFGSAAxioms.lean
fi
echo "all FGSA checks pass"
```

  Negative test (once, then remove it): add `example : 1 = 1 := by native_decide` to `Tests/Smoke.lean`; the script must exit 1. A comment `-- native_decide` must not make it fail.
- [ ] **Step 5: Run it; it passes.** `lake build --wfail AvailableChainFGSA.Tests.Smoke`, then `bash scripts/check-fgsa.sh`. Expected: PASS, exit 0.
- [ ] **Step 6: Review gate G1 and CHECKPOINT.** Commit `FGSA model: library skeleton and objects`.

---

### Task 2: Block ancestry and the carrier bridge (K5)

**Files:**
- Create: `AvailableChainFGSA/Proofs/BlockAncestry.lean`, `AvailableChainFGSA/Proofs/Carrier.lean`, `scripts/CheckFGSAAxioms.lean`
- Modify: `AvailableChainFGSA.lean` (two imports)

**Interfaces:**
- Consumes: Task 1 (`eraseFG`); `SimplexFG.{FGBlock.preceq, ViewRootInj}`; `KitFG.{preceq_refl, preceq_trans, preceq_total_of_common, ancestor_closed_of_parent_closed, RootInjectiveOn}`.
- Produces: `block_preceq_refl`, `block_preceq_trans`, `block_preceq_antisymm`, `block_preceq_total_of_common`, `block_compatible_comm`, `block_compatible_of_common`, `block_incompatible_of_preceq`, `block_genesis_preceq`; `eraseFG_slot`, `eraseFG_root`, `eraseFG_parent`, `eraseFG_eq_genesis`, `eraseFG_preceq`, `eraseFG_compatible`, `eraseFG_injOn`, `preceq_of_eraseFG_preceq`, `compatible_iff_eraseFG`, `viewRootInj_of_rootInj`, `rootInjectiveOn_of_viewRootInj`, `erase_rootInjective`.

**Blueprint:** `bp.carrier.v1` (bp00 §3.1; bp01 §2.2 steps 1–6). With DQ1 there is one erasure. Step 3 of bp01 ("full-content root injectivity gives X = Y") becomes the root injectivity of a view (`ViewRootInj`), which Task 11 gets by construction (DQ2).

- [ ] **Step 1: Write the Block ancestry statements** in `Proofs/BlockAncestry.lean` (imports `AvailableChainModel.Objects.Blocks`, `Mathlib.Tactic`). The GridCO copies of these lemmas are `private` (`GridCO/Proofs/Map.lean:25`, `Goldfish.lean:81`); do not import them.

```lean
theorem block_preceq_refl (B : Block) : Block.Preceq B B
theorem block_preceq_trans {A B C : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B C) :
    Block.Preceq A C
theorem block_preceq_antisymm {A B : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B A) :
    A = B
theorem block_genesis_preceq (B : Block) : Block.Preceq .genesis B
/-- Two ancestors of one block are comparable. -/
theorem block_preceq_total_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Preceq A B ∨ Block.Preceq B A
theorem block_compatible_comm (A B : Block) : Block.compatible A B = Block.compatible B A
/-- A block below a block compatible with `X`, or two blocks below one block, are compatible. -/
theorem block_compatible_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Compatible A B
/-- bp01 §5 item 5: a block that conflicts with `X` conflicts with every descendant of `X`. -/
theorem block_incompatible_of_preceq {b X Y : Block} (hbX : ¬ Block.Compatible b X)
    (hXY : Block.Preceq X Y) : ¬ Block.Compatible b Y
/-- If `A ⪯ C` and `C` is compatible with `F`, then `A` is compatible with `F`. -/
theorem block_compatible_of_preceq_compatible {A C F : Block} (hAC : Block.Preceq A C)
    (hCF : Block.Compatible C F) : Block.Compatible A F
```

  (The last one: if `C ⪯ F` then `A ⪯ F`; if `F ⪯ C` then `A` and `F` are ancestors of `C`.)
- [ ] **Step 2: Write the carrier statements** in `Proofs/Carrier.lean` (imports `AvailableChainFGSA.Model.Objects`, `AvailableChainFGSA.Proofs.BlockAncestry`, `AvailableChainKitFG.Correspondence`). `variable {V : Type} [DecidableEq V]`.

```lean
/-- [bp bp.carrier.v1; K5] (step 1) -/
theorem eraseFG_slot (B : FGBlock V) : (eraseFG B).slot = B.slot
theorem eraseFG_root (B : FGBlock V) : (eraseFG B).root = B.root
theorem eraseFG_parent (B : FGBlock V) : (eraseFG B).parent = eraseFG B.parent
theorem eraseFG_eq_genesis {B : FGBlock V} : eraseFG B = .genesis ↔ B = .genesis
/-- [bp bp.carrier.v1; K5] (step 2; DC `NamedWire.erase_preceq`) Forward ancestry. -/
theorem eraseFG_preceq {A B : FGBlock V} (h : FGBlock.Preceq A B) :
    Block.Preceq (eraseFG A) (eraseFG B)
theorem eraseFG_compatible {A B : FGBlock V} (h : FGBlock.compatible A B = true) :
    Block.Compatible (eraseFG A) (eraseFG B)
/-- [bp bp.carrier.v1; K5] (step 3) Erasure is injective on the ancestors of a
root-injective view. -/
theorem eraseFG_injOn {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W)
    (h : eraseFG A = eraseFG B) : A = B
/-- [bp bp.carrier.v1; K5] (step 4) Erasure reflects ancestry on such a view. -/
theorem preceq_of_eraseFG_preceq {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W)
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B
/-- [bp bp.carrier.v1; K5] (step 5) -/
theorem compatible_iff_eraseFG {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W) :
    FGBlock.compatible A B = Block.compatible (eraseFG A) (eraseFG B)
/-- [bp bp.carrier.v1; K5] (step 6) A parent-closed, root-injective block set
satisfies `ViewRootInj`. -/
theorem viewRootInj_of_rootInj {T : Finset (FGBlock V)} (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T
/-- [bp bp.carrier.v1; K5] (step 6, two chains) The `KitFG.accountable` premise. -/
theorem rootInjectiveOn_of_viewRootInj {T : Finset (FGBlock V)} (hinj : ViewRootInj T)
    {B₁ B₂ : FGBlock V} (h₁ : B₁ ∈ T) (h₂ : B₂ ∈ T) : KitFG.RootInjectiveOn B₁ B₂
/-- [bp bp.carrier.v1; K5] The erased blocks of a root-injective view have
distinct roots (the AC `RootInjective` shape, for T7). -/
theorem erase_rootInjective {T : Finset (FGBlock V)} (hinj : ViewRootInj T) :
    ∀ b ∈ T.image eraseFG, ∀ c ∈ T.image eraseFG, b.root = c.root → b = c
```

  Run: `lake build AvailableChainFGSA.Proofs.Carrier`. Expected: builds with `sorry` warnings only.
- [ ] **Step 3: Prove them.** Step-1 lemmas: `cases B <;> rfl`. `eraseFG_preceq`: induction on `B`, as DC `NamedWire.erase_preceq` (DC `DecoupledConsensusProofs/Execution/Wire.lean`). `eraseFG_injOn`: `eraseFG_root` gives equal roots; `hinj` gives `A = B`. `preceq_of_eraseFG_preceq`: induction on `B`; in the node case either `eraseFG A = eraseFG B` (then `eraseFG_injOn`) or `Block.Preceq (eraseFG A) (eraseFG B.parent)` (then the induction hypothesis with the ancestor witness of `B.parent`). `viewRootInj_of_rootInj`: `KitFG.ancestor_closed_of_parent_closed` puts every ancestor of a member in `T`.
- [ ] **Step 4: Write `scripts/CheckFGSAAxioms.lean`.** Copy `scripts/CheckFGAxioms.lean`. Change only: the imported module (`AvailableChainFGSA`), the module-prefix test (`` (`AvailableChainFGSA).isPrefixOf m ``) and the docstring. Keep the exit codes (0 clean; 1 a bad axiom; 2 nothing found or an expected name missing).
- [ ] **Step 5: Run it; it passes.** `lake build --wfail AvailableChainFGSA`, `bash scripts/check-fgsa.sh`. Expected: exit 0; the axiom step prints `checked <c> constants, <t> theorems`.
- [ ] **Step 6: Review gate G2 and CHECKPOINT.** Commit `FGSA model: block ancestry and carrier bridge (K5)`.

---

### Task 3: Store: state, active view, reconcile, outputs

**Files:**
- Create: `AvailableChainFGSA/Model/Store.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Task 1.
- Produces: `State`, `initial`, `State.slot`, `finalized`, `stable`, `confirmed`, `activeCompatible`, `actView`, `onView`, `normalizeS`, `reconcile`, `leaseOf`, `fastWriteAt`, `blockExcluded`.

- [ ] **Step 1: Write the failing tests** (append to `Tests/Smoke.lean`). The state `stR0` is set by hand, as `AvailableChainSA/Tests/Smoke.lean` does. It is not a reachable state; Task 4 has the reachable form.

```lean
def b1 : Block := eraseFG B1
def b1' : Block := eraseFG B1'
/-- F = B1 (the FG store of the FG module's G02 test), with a lease, a saved
result and a fast write on the conflicting `b1'`, and S = b1'. -/
def stR0 : State 4 :=
  { fg := stF, base := { GridCO.initial 4 with
      blocks := [.genesis, b1, eraseFG B2, eraseFG B3, b1'],
      genuine := [(1, some b1'), (2, some .genesis)],
      obligations := [(b1', 2, 100)], stableRecord := b1' },
    fastWrite := [(1, [b1'])] }

/-- Reconcile deletes the lease, empties the conflicting result but keeps its
label, keeps the compatible result, filters fastWrite, and sets S := F (spec 874–894). -/
example : (reconcile stR0).base.obligations = [] ∧
    (reconcile stR0).base.genuine = [(1, none), (2, some .genesis)] ∧
    (reconcile stR0).fastWrite = [(1, [])] ∧
    (reconcile stR0).base.stableRecord = b1 ∧
    (reconcile stR0).base.blocks = stR0.base.blocks := by decide
/-- act(Σ) keeps the cumulative list but drops `b1'` (spec 360–361). -/
example : b1' ∈ stR0.base.blocks ∧ b1' ∉ (actView stR0).blocks ∧
    b1 ∈ (actView stR0).blocks := by decide
/-- A compatible S ahead of F stays (spec 565). -/
example : (normalizeS { stR0 with base := { stR0.base with stableRecord := eraseFG B3 } }).base.stableRecord
    = eraseFG B3 := by decide
example : blockExcluded stR0 b1' = true ∧ blockExcluded stR0 .genesis = false := by decide
```

  Run: `lake build AvailableChainFGSA.Tests.Smoke`. Expected: FAIL.
- [ ] **Step 2: Write `Model/Store.lean`.** Imports: `AvailableChainFGSA.Model.Objects`.

```lean
/-- [spec 339–353, 486–503; M1] The composite node store. `base` holds the SA
fields and the erased cumulative tree (`Σ.T`, stamps, vote pool, frozen and
early caches, saved results `Σ.genuine`, leases `Σ.lease` as `obligations`,
`S` as `stableRecord`). `fg` holds `Σ.T` with rows and the FG caches
`F, J, h_j, hmax`. `proposals` holds the admitted proposal wires with their
signed rows (for the HEAD merge and row inclusion). `rowPool` is
`Σ.attestations`. `fastWrite` is `Σ.fastWrite`. `σ[B]` is `derive p.E p.cfg B`,
not a field. Λ is not a field (DQ4). -/
structure State (n : Nat) where
  base : GridCO.State n := GridCO.initial n
  fg : Store (Fin n) := Store.init
  proposals : List (Wire n) := []
  rowPool : List (RowWire n) := []
  fastWrite : List (Slot × List Block) := []

variable {n : Nat}

def initial (n : Nat) : State n := {}

/-- [spec 711] The store slot `Σ.s`. -/
def State.slot (p : Params) (st : State n) : Slot := p.slotOf st.base.now

/-- [spec 558–561, 789–802] The outputs. -/
def finalized (st : State n) : FGBlock (Fin n) := st.fg.F
def confirmed (st : State n) : Block := st.base.stableRecord
def stable (st : State n) : Block := confirmed st

/-- [spec 360–361] Membership in `act(Σ)` of an erased block: compatibility with F. -/
def activeCompatible (st : State n) (b : Block) : Bool :=
  Block.compatible b (eraseFG st.fg.F)

/-- [spec 363–366; M2] The SA base as the SA code reads it: the stored state with
its block list filtered to `act(Σ)`. Every other field is the stored one. -/
def actView (st : State n) : GridCO.State n :=
  { st.base with blocks := st.base.blocks.filter (activeCompatible st) }

/-- [M2] Run a GridCO step on the active view, then keep the cumulative block
list. Used only with steps that do not change `blocks` (Task 7 proves it). -/
def onView (f : GridCO.State n → GridCO.State n) (st : State n) : State n :=
  { st with base := { f (actView st) with blocks := st.base.blocks } }

/-- [spec 565–566, 778–781, 890–892] `S := F` when `F ⋠ S`. -/
def normalizeS (st : State n) : State n :=
  if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st
  else { st with base := { st.base with stableRecord := eraseFG st.fg.F } }

/-- [spec 474–484, 874–894; K1, K3] `reconcile_with_finality`: delete the leases
whose target conflicts with F; filter every fastWrite set; empty each
conflicting saved result and keep its label; then `S := F` if `F ⋠ S`. It
writes no other field: not `fg`, not the blocks, stamps, pools or proposals,
not `goldfishRecord` (DQ8). -/
def reconcile (st : State n) : State n :=
  let ok := activeCompatible st
  normalizeS { st with
    base := { st.base with
      obligations := st.base.obligations.filter (fun row => ok row.1)
      genuine := st.base.genuine.map (fun row => (row.1, row.2.filter ok)) }
    fastWrite := st.fastWrite.map (fun row => (row.1, row.2.filter ok)) }

/-- [spec 293–294] `Σ.lease[B]`: the deadline of the first lease row on `b`. SA
writes one level only, so there is at most one row per target. -/
def leaseOf (st : State n) (b : Block) : Option Time :=
  (st.base.obligations.find? (fun row => row.1 == b)).map (fun row => row.2.2)

/-- [spec 297–298, 457–461] `Σ.fastWrite[r]`, or `none` if the gate at `d_r` did
not run. -/
def fastWriteAt (st : State n) (r : Slot) : Option (List Block) :=
  (st.fastWrite.find? (fun row => row.1 == r)).map Prod.snd

/-- [spec 178–182; DQ9] DC `NamedReceipt.excludes` as a store predicate: a block
that conflicts with F. A stored finalized ancestor is not excluded. -/
def blockExcluded (st : State n) (b : Block) : Bool := !activeCompatible st b
```

- [ ] **Step 3: Run it; it passes.** `lake build --wfail AvailableChainFGSA.Tests.Smoke`. If a test value differs from the expected value, compute it by hand from the spec. A real difference is a finding: report it and do not change the expectation to match the code.
- [ ] **Step 4: Review gate G3 and CHECKPOINT.** Commit `FGSA model: store, active view, reconcile`.

---

### Task 4: Handlers: votes, rows, blocks

**Files:**
- Create: `AvailableChainFGSA/Model/Handlers.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Task 3; `GridCO.admitVote`, `GridCO.admitProposal`, `SimplexFG.on_block`, `SimplexFG.pickPair`.
- Produces: `admitHead`, `admitRow`, `parentFG`, `fgBlock`, `blockAccepted`, `admitBlock`, `process`, `wellFormed`.

- [ ] **Step 1: Write the failing tests.** The proposal wires carry the rows of the FG test blocks. Row rounds: `B1` (slot 1) has round-0 rows; `B2`, `B3` (slots 2, 3) have round-1 rows (`pT.round 2 = pT.round 3 = 1`).

```lean
def rowsOf (r : Nat) (B : FGBlock (Fin 4)) : List (RowWire 4) := B.rows.map (fun a => ⟨.seat (.fg r) a.signer, RowBody.ofRow a⟩)
def wProp (B : FGBlock (Fin 4)) (r : Nat) (raw : List (HeadWire 4) := []) : Wire 4 :=
  ⟨.proposer B.slot, .proposal (eraseFG B) raw [] (rowsOf r B)⟩
/-- Now = 12: slot 3, round 1. -/
def st0 : State 4 := { base := { GridCO.initial 4 with now := 12 } }
def stA : State 4 := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) st0

/-- The FG part is the FG module's store after the same blocks (K4). -/
example : stA.fg.TF = stF.TF ∧ stA.fg.F = B1 ∧ stA.fg.J = stF.J ∧
    stA.fg.h_j = stF.h_j ∧ stA.fg.h_max = stF.h_max := by decide
/-- The base holds the erased tree (spec 355–358). -/
example : stA.base.blocks = [.genesis, b1, eraseFG B2, eraseFG B3] := by decide
/-- F moved to B1: S := F (spec 890–892). -/
example : stA.base.stableRecord = b1 := by decide

/-- A vote carried by the conflicting block. -/
def v0 : HeadWire 4 := ⟨.seat (.head 1) 0, .genesis⟩
/-- Refusal of `F ⋠ B` before unpacking (spec 808, 535–536): no block, no stamp,
no carried vote, no row, no FG change. -/
example : (process pT stA (wProp B1' 0 [v0])).base.blocks = stA.base.blocks ∧
    (process pT stA (wProp B1' 0 [v0])).base.votes = stA.base.votes ∧
    (process pT stA (wProp B1' 0 [v0])).base.blockStamp = stA.base.blockStamp ∧
    (process pT stA (wProp B1' 0 [v0])).rowPool = stA.rowPool ∧
    (process pT stA (wProp B1' 0 [v0])).fg.TF = stA.fg.TF ∧
    (process pT stA (wProp B1' 0 [v0])).proposals = stA.proposals := by decide

/-- The reachable form of Task 3's test: `B1'` enters while F = genesis; a
lease, a saved result and a fast write on it are set by hand; then `B1`, `B2`,
`B3` move F to `B1`, and reconcile runs inside the handler. -/
def stR1 : State 4 :=
  let st := process pT st0 (wProp B1' 0)
  { st with base := { st.base with genuine := [(1, some b1')],
      obligations := [(b1', 2, 100)], stableRecord := b1' },
    fastWrite := [(1, [b1'])] }
def stR2 : State 4 := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) stR1
example : stR2.fg.F = B1 ∧ stR2.base.obligations = [] ∧
    GridCO.savedGenuine stR2.base 1 = some none ∧ stR2.fastWrite = [(1, [])] ∧
    stR2.base.stableRecord = b1 ∧ b1' ∈ stR2.base.blocks ∧
    b1' ∉ (actView stR2).blocks := by decide

/-- DQ2: a new block whose root is already stored is refused. -/
example : (process pT stA ⟨.proposer 3, .proposal (.node b1 3 B2.root) [] [] []⟩).fg.TF
    = stA.fg.TF := by decide
/-- The row pool admits at most two distinct rows per identity and round
(spec 433–439, 852–855), and only rows in the window (spec 848–851). -/
def rA (h : Nat) : RowWire 4 := ⟨.seat (.fg 1) 0, ⟨.vote h genesisRoot false, none⟩⟩
example : ([rA 1, rA 2, rA 3].foldl (admitRow pT) st0).rowPool = [rA 1, rA 2] := by decide
example : (admitRow pT st0 ⟨.seat (.fg 2) 0, ⟨.empty, none⟩⟩).rowPool = [] := by decide
```

  Run the build. Expected: FAIL.
- [ ] **Step 2: Write `Model/Handlers.lean`.** Imports: `AvailableChainFGSA.Model.Store`.

```lean
variable {n : Nat}

/-- [spec 831–842] `on_goldfish_vote`: SA's vote pool, unchanged. -/
def admitHead (p : Params) (st : State n) (o : Wire n) (b : Block) : State n :=
  { st with base := GridCO.admitVote p.toParams.engine st.base ⟨baseAuth o.auth, .head b⟩ }

/-- [spec 433–439, 844–857] `on_attestation`: a row of round `r` enters the pool
if `r` is in the window `[max 0 (r_now − w_F), r_now]`, it is not already
there, and its identity has fewer than two rows of round `r`. -/
def admitRow (p : Params) (st : State n) (a : RowWire n) : State n :=
  match a.auth with
  | .seat (.fg r) i =>
      let now := p.round (st.slot p)
      let mine := st.rowPool.filter (fun b => b.auth == .seat (.fg r) i)
      if r + p.wF < now || now < r || decide (a ∈ mine) || 2 ≤ mine.length then st
      else { st with rowPool := st.rowPool ++ [a] }
  | _ => st

/-- [spec 519–522; M3] The stored FG parent of an erased block. `pickPair`
returns `none` on two candidates; Task 10 shows there is at most one. -/
def parentFG (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun P => decide (eraseFG P = b.parent))

/-- [M3] The FG block of an admitted proposal: the stored parent, the slot and
root of the wire block, and its rows. -/
def fgBlock (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) : FGBlock (Fin n) :=
  .node P b.slot b.root (rows.filterMap RowWire.toRow?)

/-- [spec 530–536, 806–817; M5, DQ2, DQ12] The acceptance tests of `on_block`,
all before any write: not genesis; `b.slot ≤ Σ.s`; no stored block has the
root of `b`; `F ⪯ B`; `b.parent.slot < b.slot`; the slot-`b.slot` proposer
signs it; every row is a row wire with round `≤ round(b.slot)`. The parent test
is `parentFG st b = some P`. -/
def blockAccepted (p : Params) (st : State n) (o : Wire n) (b : Block)
    (P : FGBlock (Fin n)) (rows : List (RowWire n)) : Bool :=
  b != .genesis && decide (b.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = b.root) &&
    FGBlock.preceq st.fg.F (fgBlock P b rows) &&
    decide (b.parent.slot < b.slot) && decide (o.auth = .proposer b.slot) &&
    rows.all (fun a => match a.round? with
      | some r => decide (r ≤ p.round b.slot)
      | none => false)

/-- [spec 804–829; M6] `on_block`. On refusal the state does not change. On
acceptance: the SA block admission and the carried votes (SA code on the
cumulative base, with the erased block); the FG admission (`on_block` of the FG
module: insert, then `update_finality`); the proposal wire is stored; if F
moved, `reconcile`; then the carried rows pass `admitRow`. -/
def admitBlock (p : Params) (st : State n) (o : Wire n) (b : Block)
    (raw support : List (HeadWire n)) (rows : List (RowWire n)) : State n :=
  match parentFG st b with
  | none => st
  | some P =>
      if blockAccepted p st o b P rows then
        let st1 : State n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal o b raw support) b (raw.map baseHead)
          fg := on_block p.E p.cfg st.fg (fgBlock P b rows)
          proposals := st.proposals ++ [o] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        rows.foldl (admitRow p) st2
      else st

/-- [spec 804–857] The delivery handler. -/
def process (p : Params) (st : State n) (o : Wire n) : State n :=
  match o.auth, o.payload with
  | .seat (.head _) _, .head b => admitHead p st o b
  | .seat (.fg _) _, .row body => admitRow p st ⟨o.auth, body⟩
  | .proposer _, .proposal b raw support rows => admitBlock p st o b raw support rows
  | _, _ => st

/-- [spec 505–528; DQ9] The input check, as a pure function (T7 binds it). A
vote: a HEAD seat. A row: an FG seat, and a height pair with `h ≥ 1`. A block:
not genesis, the proposer key of its slot, every carried vote of slot
`b.slot − 1`, support ⊆ votes, every carried row a row wire. The parent-slot
test needs the parent and is in `blockAccepted`. -/
def wellFormed (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat (.head _) _, .head _ => true
  | .seat (.fg _) _, .row body =>
      match body.height_pair with
      | .empty => true
      | .vote h _ _ => decide (1 ≤ h)
  | .proposer s, .proposal b raw support rows =>
      b != .genesis && s == b.slot &&
        raw.all (fun v => match v.auth with
          | .seat (.head r) _ => r + 1 == b.slot
          | _ => false) &&
        support.all (fun v => decide (v ∈ raw)) &&
        rows.all (fun a => a.round?.isSome)
  | _, _ => false
```

- [ ] **Step 3: Run it; it passes.** As in Task 3, Step 3.
- [ ] **Step 4: Review gate G4 and CHECKPOINT.** Commit `FGSA model: handlers`.

---

### Task 5: Clock and the composite gate

**Files:**
- Create: `AvailableChainFGSA/Model/Clock.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Task 3; `SA.{confirmation, gate, release, prefixSupport, releaseThreshold, freezeTime, earlyTime, releaseTime, gateTime}`, `GridCO.{expire, freeze, earlyVotes, savedGenuine}`.
- Produces: `fastSet`, `gateStep`, `clock`.

- [ ] **Step 1: Write the failing tests.**

```lean
/-- An empty gate at d_2 = 14 (no votes): the result is saved as empty, the fast
set of label 2 is created empty, and S := F runs after the gate (spec 756–781). -/
def stG : State 4 :=
  { stA with base := { stA.base with now := 14, stableRecord := .genesis } }
example : GridCO.savedGenuine (gateStep pT stG 2).base 2 = some none ∧
    fastWriteAt (gateStep pT stG 2) 2 = some [] ∧
    (gateStep pT stG 2).base.stableRecord = b1 := by decide
/-- Evaluate once: a second gate of label 2 writes nothing new (spec 756). -/
example : (gateStep pT (gateStep pT stG 2) 2).fastWrite = (gateStep pT stG 2).fastWrite := by decide
/-- The clock at 14 runs the gate of slot 2 and keeps the FG part (spec 718–720). -/
example : fastWriteAt (clock pT stA 14) 2 = some [] ∧ (clock pT stA 14).fg.F = stA.fg.F := by decide
```

  Add one successful fast gate. The blocks of `stA` have stamp 12, which is after `e_2 = 10`, so use a new fixture: admit `B1` and `B2` at now = 8 (stamps 8), then admit two label-2 HEAD votes for `eraseFG B2` at now = 9 (seats 0 and 1; stamps 9 < `e_2`), then run `gateStep` at now = 14. Expected: the saved result is `some (eraseFG B2)`; `fastWriteAt … 2 = some [b1, eraseFG B2]` (the non-genesis active prefixes with `p ≥ τ = 2`); a lease on each with deadline `d_2 + L = 14 + 7 = 21`. If `decide` is too slow, keep the test as a `#eval` and say so in the report.
- [ ] **Step 2: Write `Model/Clock.lean`.** Imports: `AvailableChainFGSA.Model.Store`.

```lean
variable {n : Nat}

/-- [spec 761–775, 457–461] The fast-write set of gate `s`, computed on the
active view before the gate: empty if the result is empty or vetoed; else the
non-genesis active prefixes of the result that pass the fast test `p(s,B) ≥ τ`.
A renewal counts also when the deadline does not change. -/
def fastSet (p : Params) (v : GridCO.State n) (s : Slot) : List Block :=
  match SA.confirmation p.toParams v s with
  | none => []
  | some h =>
      if v.obligations.any (fun row => !Block.compatible row.1 h) then [] else
        v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
          decide (SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams v s b))

/-- [spec 754–782; M7, DQ5] `update_confirmation`: if label `s` is not saved,
run the SA gate on the active view and record `fastWrite[s]`; then `S := F`
if `F ⋠ S`, also after an empty or vetoed gate. -/
def gateStep (p : Params) (st : State n) (s : Slot) : State n :=
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    { onView (fun v => SA.gate p.toParams v s) st with
      fastWrite := st.fastWrite ++ [(s, fastSet p (actView st) s)] }
  normalizeS st

/-- [spec 683–694, 709–752; M8] The tick: set the time and expire leases; the
freeze and early caches (on the active view; M8); the release at `q_{s−1}` (on
the active view); the gate at `d_{s−1}`. The duties are not here (Q1). The
step order and the time tests are those of `GridCO.clock`
(`AvailableChainGridCO/Model/Protocol.lean:485`). -/
def clock (p : Params) (st : State n) (t : Time) : State n :=
  let q := p.toParams
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
    onView (fun v => GridCO.freeze q.engine v fSlot) st else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
    onView (fun v => { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] }) st
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot then
    onView (fun v => SA.release q v qSlot) st else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == SA.gateTime q dSlot then gateStep p st dSlot else st
```

- [ ] **Step 3: Run it; it passes.** As in Task 3, Step 3.
- [ ] **Step 4: Review gate G5 and CHECKPOINT.** Commit `FGSA model: clock and composite gate`.

---

### Task 6: Frame reads and duties; Astra model check

**Files:**
- Create: `AvailableChainFGSA/Model/Frame.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Tasks 4–5; `SimplexFG.{storeControls, storeFrame, Controls.Z, Controls.lo, hOf, HeadFields, createRow, Record}`, `GridCO.{ghost, goldfishScore, voterCount, votesAt, stampBlock, stampVote, resolvedBefore, headTarget?, headLabel?, blockKnown}`.
- Produces: `controls`, `fullTree`, `erasedList`, `liveRoot`, `eligible`, `headInTree`, `proposalsAt`, `voterBlocks`, `headVotes`, `headSupport`, `headVote`, `getHead`, `proposerVotes`, `proposerSupport`, `chainWireRows`, `blockWireRows`, `proposalRows`, `propose`, `fgHead`, `fgBlockOf`, `deepest`, `fgSource`, `fgInputs`, `attest`.

- [ ] **Step 1: Write the failing tests.**

```lean
/-- The FG action of round 1 at a_1 = 14, after the empty gate of slot 2:
fastWrite[2] is empty, so C_fg is none and the height pair is empty; there is
no fallback to S, the root, a slow lease or an older set (spec 669–677). -/
def stC0 : State 4 := clock pT stA 14
example : fastWriteAt stC0 2 = some [] ∧ (fgInputs pT stC0).1 = none ∧
    (attest pT stC0 Record.initial 0).1.height_pair = .empty := by decide
/-- With a live fast write on B2 (set by hand), C_fg = B2 (the deepest member
of fastWrite[2] in the full filtered tree with a lease after a_1). -/
def stC1 : State 4 :=
  { stC0 with fastWrite := [(2, [eraseFG B2])],
    base := { stC0.base with obligations := [(eraseFG B2, 2, 21)] } }
example : (fgInputs pT stC1).1 = some B2 := by decide
/-- An expired lease does not count (spec 1329: `lease[B] > Σ.t`). -/
example : (fgInputs pT { stC1 with base := { stC1.base with obligations := [(eraseFG B2, 2, 14)] } }).1
    = none := by decide
/-- Band eligibility (spec 1068): at v_4 = 17 with no votes, the HEAD walks from
Z = F = B1 (no lease). B2 is eligible because σ[B1].h = 2 < lo = 3; B3 is not
(σ[B2].h = 3, no majority, not current). -/
example : headVote pT { stA with base := { stA.base with now := 17 } } 4 = eraseFG B2 := by decide
```

  Also add: (a) a HEAD whose frozen support names a head that left `act(Σ)` after the freeze: the vote is in `headVotes` but not in `headSupport` (Review Focus 7); (b) `proposalRows` drops a pool row that is already on the chain of the parent, and keeps at most two rows per identity and round with the pool rows first (spec 1255–1274). Compute the expected values by hand before the build.
- [ ] **Step 2: Write `Model/Frame.lean`.** Imports: `AvailableChainFGSA.Model.Handlers`, `AvailableChainFGSA.Model.Clock`.

```lean
variable {n : Nat}

/-- [spec 616–633] The live frame: the FG module's store controls. -/
def controls (p : Params) (st : State n) : Controls (Fin n) := storeControls p.E p.cfg st.fg
/-- [spec 1033–1037] `get_filtered_block_tree(Σ)`. -/
def fullTree (p : Params) (st : State n) : Finset (FGBlock (Fin n)) :=
  storeFrame p.E p.cfg st.fg st.fg.TF
/-- [helper] The erasure of an FG block set, in the order of the base list. -/
def erasedList (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

/-- [spec 648–655, 1086–1098] `live_root`: the deepest live lease target in the
full filtered tree (ties: the greater root), else the FG root Z. -/
def liveRoot (p : Params) (st : State n) : Block :=
  let tree := fullTree p st
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ B ∈ tree, eraseFG B = row.1) then some row.1 else none)
  targets.foldl (fun best b =>
    if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b else best)
    (eraseFG (controls p st).Z)

/-- [spec 1063–1072] `goldfish_eligible` with the band floor: the parent's state
height is below `lo`, or a strict majority, or the store's current slot. -/
def eligible (p : Params) (st : State n) (raw support : List (GridCO.Wire n)) (b : Block) : Bool :=
  decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧ hOf p.E p.cfg P < (controls p st).lo) ||
    decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
    b.slot == st.slot p

/-- [spec 1074–1107] `get_head_in_tree`: GHOST from the live root over `tree`. -/
def headInTree (p : Params) (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) : Block :=
  GridCO.ghost (liveRoot p st) tree (GridCO.goldfishScore st.base.blocks raw support)
    (eligible p st raw support)

/-- [spec 1109–1114] `get_head`: the full filtered tree. -/
def getHead (p : Params) (st : State n) (raw support : List (GridCO.Wire n)) : Block :=
  headInTree p st (erasedList st (fullTree p st)) raw support

/-- [helper] The admitted slot-`s` proposals, with their vote lists. These stay
readable when the block leaves `act(Σ)` (spec 190–193). -/
def proposalsAt (st : State n) (s : Slot) : List (List (HeadWire n) × List (HeadWire n)) :=
  st.proposals.filterMap (fun o => match o.payload with
    | .proposal b raw sup _ => if b.slot = s then some (raw, sup) else none
    | _ => none)

/-- [spec 598–606, 1219–1226] `voter_processed_block_tree(Σ, s)`: blocks of Σ.T
received before `z_{s−1}`, and every ancestor of an admitted slot-`s` proposal. -/
def voterBlocks (p : Params) (st : State n) (s : Slot) : Finset (FGBlock (Fin n)) :=
  st.fg.TF.filter (fun B =>
    decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
    decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P))

/-- [spec 606–612, 1283–1294] The HEAD raw merge: pool votes of slot `s − 1`
received before `z_{s−1}`, and the slot-`(s−1)` votes of every admitted slot-`s`
proposal. -/
def headVotes (p : Params) (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  let frozen := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1))
  (frozen ++ carried).eraseDups

/-- [spec 423–430, 1286–1293] The HEAD support merge: pool votes resolved
before `z_{s−1}` against the CURRENT `act(Σ)`; the declared support of every
admitted slot-`s` proposal whose head is in Σ.T with a valid slot. -/
def headSupport (p : Params) (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  let frozen := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
    GridCO.headLabel? o == some (s - 1) &&
      match GridCO.headTarget? o with
      | some h => GridCO.blockKnown st.base h && decide (h.slot ≤ s - 1)
      | none => false)
  (frozen ++ carried).eraseDups

/-- [spec 1276–1302] `goldfish_vote` at `v_s`: genesis at slot 0; else the head
of the filtered voter view (live controls, M9) from the live root. -/
def headVote (p : Params) (st : State n) (s : Slot) : Block :=
  if s = 0 then .genesis else
    headInTree p st (erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)))
      (headVotes p st s) (headSupport p st s)

/-- [spec 1240–1243] The proposer's votes: every slot-`(s−1)` pool vote; the
support: those that resolve now (active head, valid slot). -/
def proposerVotes (st : State n) (s : Slot) : List (GridCO.Wire n) := GridCO.votesAt st.base (s - 1)
def proposerSupport (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  (proposerVotes st s).filter (fun o => match GridCO.headTarget? o with
    | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s - 1)
    | none => false)

/-- [helper] The signed rows of the stored blocks on the chain of `H`. -/
def chainWireRows (st : State n) (H : Block) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.payload with
    | .proposal b _ _ rows => if Block.preceq b H then some rows else none
    | _ => none)).flatten
/-- [helper] The rows with a round in `I` of the stored blocks of a slot in a round of `I`. -/
def blockWireRows (p : Params) (st : State n) (I : Nat → Bool) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.payload with
    | .proposal b _ _ rows =>
        if I (p.round b.slot) then some (rows.filter (fun a => (a.round?.map I).getD false)) else none
    | _ => none)).flatten

/-- [spec 544–556, 1255–1274] `proposal_attestations(Σ, H)`: pool rows and
stored-block rows of the window `I = [max 0 (r − w_F), r]`, without rows on the
chain of `H`; per identity and round, every pool row, then distinct block rows
until there are two. -/
def proposalRows (p : Params) (st : State n) (H : Block) : List (RowWire n) :=
  let r := p.round (st.slot p)
  let inI : Nat → Bool := fun r' => decide (r ≤ r' + p.wF) && decide (r' ≤ r)
  let onChain := chainWireRows st H
  let A := st.rowPool.filter (fun a => (a.round?.map inI).getD false && !decide (a ∈ onChain))
  let A' := (blockWireRows p st inI).filter (fun a => !decide (a ∈ onChain) && !decide (a ∈ A))
  A'.foldl (fun acc a =>
    if decide (a ∈ acc) || 2 ≤ (acc.filter (fun x => x.auth == a.auth)).length then acc
    else acc ++ [a]) A

/-- [spec 1236–1253; DQ10] `propose_block` at `t_s`, `s > 0`. -/
def propose (p : Params) (st : State n) (s : Slot) : Option (Msg n) :=
  if s = 0 then none else
    let raw := proposerVotes st s
    let sup := proposerSupport st s
    let H := getHead p st raw sup
    some (.proposal (.node H s ⟨s * (H.root.value + 1)⟩) (raw.filterMap liftHead?)
      (sup.filterMap liftHead?) (proposalRows p st H))

/-- [spec 1318–1323] The finality head: `get_head` with the current-slot votes
and their active resolved subset. -/
def fgHead (p : Params) (st : State n) : Block :=
  let s := st.slot p
  let raw := GridCO.votesAt st.base s
  let sup := raw.filter (fun o => match GridCO.headTarget? o with
    | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s)
    | none => false)
  getHead p st raw sup

/-- [helper] The stored FG block of an erased block. -/
def fgBlockOf (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun B => decide (eraseFG B = b))
/-- [helper] The unique deepest member (depth of the erasure), or none. -/
def deepest (X : Finset (FGBlock (Fin n))) : Option (FGBlock (Fin n)) :=
  pickPair X (fun B => decide (∀ C ∈ X, (eraseFG C).depth ≤ (eraseFG B).depth))

/-- [spec 666–677, 1327–1335] `C_fg`: the deepest block of the full filtered
tree that is in `fastWrite[rR]` and has a lease deadline after now. The set is
the one of the scheduled gate `d_{rR}`; there is no older set and no fallback. -/
def fgSource (p : Params) (st : State n) : Option (FGBlock (Fin n)) :=
  let r := p.round (st.slot p)
  let fw := (fastWriteAt st (r * p.R)).getD []
  deepest ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
    match leaseOf st (eraseFG B) with
    | some d => decide (st.base.now < d)
    | none => false))

/-- [spec 1315–1338] `get_fg_vote`: the source and the head fields of the
finality head. -/
def fgInputs (p : Params) (st : State n) : Option (FGBlock (Fin n)) × HeadFields :=
  (fgSource p st, match fgBlockOf st (fgHead p st) with
    | some Hd => HeadFields.ofBlock p.E p.cfg Hd
    | none => ⟨0, genesisRoot, 0⟩)

/-- [spec 1304–1313, 1391–1399; DQ4] `attest` without emission: the row body and
the new record. The identity `i` is supplied by the caller (Q1). -/
def attest (p : Params) (st : State n) (Λ : Record) (i : Fin n) : RowBody × Record :=
  let x := fgInputs p st
  let y := createRow p.E p.cfg Λ i x.1 x.2
  (RowBody.ofRow y.1, y.2)
```

  Report as findings, not fixes: (a) `deepest` and `fgBlockOf` return `none` on a tie; Task 11's invariants make ties impossible for `fgBlockOf`; for `deepest`, the live targets form one chain (spec 452–456), which is a lease-origin fact outside this plan; (b) the fallback head fields `⟨0, genesisRoot, 0⟩` are unreachable when the head is in Σ.T.
- [ ] **Step 3: Run it; it passes.** As in Task 3, Step 3.
- [ ] **Step 4: Astra model check (review gate G6).** Before any proof task, start a Codex astra job: compare `Model/*.lean` line by line with the spec lines in each docstring and with the tree-read inventory. Output `docs/audit/fgsa-model-check-report.md` (blocking, major, minor; verdict). Fix every blocking and major finding in the model and in this plan, with new or changed smoke tests. Re-run the build.
- [ ] **Step 5: CHECKPOINT.** Commit `FGSA model: frame reads and duties`.

---

### Task 7: Write sets, active-view laws and the SA bridge

**Files:**
- Create: `AvailableChainFGSA/Statements/Invariants.lean`, `AvailableChainFGSA/Proofs/Fields.lean`, `AvailableChainFGSA/Proofs/ActView.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 2–6; GridCO lemmas (check each signature and its `[LeasePolicy]` variable before use): `admitVote_blocks`, `admitVote_obligations`, `admitVote_stable` (`History.lean:60`), `admitProposal_obligations`, `admitProposal_now` (`Map.lean:498–517`), `process_stable` (`History.lean`), `gate_blocks` (`Map.lean:940`), `release_subset` (`Basic.lean:140`), `confirmation_mem` (`RecordSlots.lean:150`).
- Produces: `Reachable`, `NestOK`, `SACompat`, `CStoreInv` (Statements); the field lemmas; `actView_onView`; the actView laws; `clock_eq_saClock`.

- [ ] **Step 1: Write `Statements/Invariants.lean`.** Imports: `AvailableChainFGSA.Model.Frame`, `AvailableChainKitFG.Correspondence`.

```lean
/-- The states that the local steps reach from the initial state: ticks at any
times and deliveries of any wire objects, in any order. No engine, no run. -/
inductive Reachable (p : Params) : State p.n → Prop
  | init : Reachable p (initial p.n)
  | tick {st : State p.n} (t : Time) : Reachable p st → Reachable p (clock p st t)
  | deliver {st : State p.n} (o : Wire p.n) : Reachable p st → Reachable p (process p st o)

/-- [bp comp.outputNesting.v2; K2] `F ⪯ S` (erased). -/
def NestOK {n : Nat} (st : State n) : Prop :=
  Block.Preceq (eraseFG st.fg.F) st.base.stableRecord

/-- [bp bp.activeView.v1, bp.reconcile.v1] Every live lease target, saved
nonempty result and fastWrite member is compatible with F. -/
def SACompat {n : Nat} (st : State n) : Prop :=
  (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) ∧
  (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) ∧
  (∀ row ∈ st.fastWrite, ∀ b ∈ row.2, Block.Compatible b (eraseFG st.fg.F))

/-- [bp bp.store.v1; K4] The composite store invariant. `fg` is the FG module's
invariant (K4). `rootInj`: Σ.T is root-injective (DQ2). `baseTree`: the base
list is Σ.T erased. `Smem`: S is stored. -/
structure CStoreInv (p : Params) (st : State p.n) : Prop where
  fg : KitFG.StoreInv p.E p.cfg st.fg
  rootInj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y
  baseTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b
  saCompat : SACompat st
  Smem : st.base.stableRecord ∈ st.base.blocks
```

- [ ] **Step 2: Write the field statements** in `Proofs/Fields.lean`. For each step, one lemma per field group: `admitHead_fg`, `admitHead_base_blocks`, `admitHead_base_stable`, `admitHead_fastWrite`; `admitRow_eq` (only `rowPool` changes: `admitRow p st a = st ∨ admitRow p st a = { st with rowPool := st.rowPool ++ [a] }`); `admitBlock_refused` (`admitBlock … = st` when `parentFG` is `none` or `blockAccepted` is false); `onView_fg`, `onView_base_blocks`, `onView_proposals`, `onView_rowPool`, `onView_fastWrite`; `normalizeS_fg`, `normalizeS_fields` (only `stableRecord`); `reconcile_fg`; `gateStep_fg`, `gateStep_base_blocks`; `clock_fg : (clock p st t).fg = st.fg`, `clock_base_blocks : (clock p st t).base.blocks = st.base.blocks`, `clock_proposals`, `clock_rowPool`. The GridCO steps that `onView` runs keep `blocks`:

```lean
theorem freeze_blocks (q : GridCO.Params) (v : GridCO.State n) (r : Slot) :
    (GridCO.freeze q v r).blocks = v.blocks
theorem release_blocks (p : SA.Params) (v : GridCO.State n) (r : Slot) :
    (SA.release p v r).blocks = v.blocks
theorem saGate_blocks (p : SA.Params) (v : GridCO.State n) (r : Slot) :
    (SA.gate p v r).blocks = v.blocks   -- from GridCO.gate_blocks
```

- [ ] **Step 3: Write the active-view statements** in `Proofs/ActView.lean`.

```lean
/-- [bp bp.activeView.v1] `actView` changes only the block list. -/
theorem actView_blocks (st : State n) (b : Block) :
    b ∈ (actView st).blocks ↔ b ∈ st.base.blocks ∧ Block.Compatible b (eraseFG st.fg.F)
/-- [M2] Running a block-preserving step on the view commutes with `actView`. -/
theorem actView_onView (f : GridCO.State n → GridCO.State n)
    (hf : ∀ v, (f v).blocks = v.blocks) (st : State n) :
    actView (onView f st) = f (actView st)
/-- [bp bp.activeView.v1] (item 3) For fixed Σ.T, a later F gives a smaller view. -/
theorem actView_antitone (st : State n) {F' : FGBlock (Fin n)} (h : FGBlock.Preceq st.fg.F F') :
    ∀ b ∈ (actView { st with fg := { st.fg with F := F' } }).blocks, b ∈ (actView st).blocks
/-- [bp bp.activeView.v1] (item 5; DQ9) Exclusion is stable under F advances. -/
theorem blockExcluded_stable (st : State n) {F' : FGBlock (Fin n)} (h : FGBlock.Preceq st.fg.F F')
    (b : Block) (hx : blockExcluded st b = true) :
    blockExcluded { st with fg := { st.fg with F := F' } } b = true
/-- [helper] A vote admission commutes with `actView` (SA's vote pool reads no block). -/
theorem actView_admitHead (p : Params) (st : State n) (o : Wire n) (b : Block) :
    actView (admitHead p st o b) =
      GridCO.admitVote p.toParams.engine (actView st) ⟨baseAuth o.auth, .head b⟩
```

- [ ] **Step 4: Write the SA bridge** in `Proofs/ActView.lean` (comp D3: "SA writes are copied back"; the main reuse lemma for composition tasks T11–T12).

```lean
/-- [comp D3; M7, M8] Off the gate times, the composite tick is the SA tick on
the active view with the cumulative block list restored. -/
theorem clock_eq_saClock_offGate (p : Params) (st : State n) (t : Time)
    (hg : ¬ (0 ≤ t - 6 * p.Δ ∧ t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)) :
    clock p st t = { st with base := { SA.clock p.toParams (actView st) t with blocks := st.base.blocks } }
/-- [comp D3; M7, DQ5] At a gate time of an unsaved label, the composite tick is
`normalizeS` of the SA tick on the active view, with `fastWrite[s]` added. -/
theorem clock_eq_saClock_gate (p : Params) (st : State n) (t : Time) (s : Slot)
    (hs : s = ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) (hg : 0 ≤ t - 6 * p.Δ)
    (ht : t = SA.gateTime p.toParams s)
    (hnew : GridCO.savedGenuine st.base s = none) :
    ∃ fw, clock p st t = normalizeS { st with
      base := { SA.clock p.toParams (actView st) t with blocks := st.base.blocks },
      fastWrite := st.fastWrite ++ [(s, fw)] }
```

  The time `t` is fixed by the gate, so the freeze and release branches do not run at the same tick; the early branch does (`d_s = e_{s+1}`), and it commutes. `hnew` must hold at the tick after the expiry and the early step; these steps do not write `genuine`. If the exact equality needs more premises, state them and report each one.
- [ ] **Step 5: Prove them.** Field lemmas: `unfold` and `split` on the `if` and `match` branches (as `GridCO.gate_blocks`). `actView_onView`: `simp [actView, onView, hf]` with the structure eta. The antitone and stability lemmas: `eraseFG_preceq` and `block_incompatible_of_preceq` (Task 2), `block_compatible_of_preceq_compatible`. The bridge: unfold `clock`, `SA.clock` (`GridCO.clock`), `onView`; use `actView_onView` at each step and the fact that `expire` and the early step do not read `blocks`.
- [ ] **Step 6: Review gate G7 and CHECKPOINT.** Commit `FGSA store: write sets, active view, SA bridge`.

---

### Task 8: Output nesting, store form (K2; composition T6)

**Files:**
- Create: `AvailableChainFGSA/Statements/Store.lean`, `AvailableChainFGSA/Proofs/Nesting.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Task 7.
- Produces: `OutputNestingStored` (Statement); `outputNesting_v1`, `normalizeS_nest`, `reconcile_nest`, `gateStep_nest`, `process_nest`, `clock_nest`, `outputNesting_stored`.

**Blueprint:** `comp.outputNesting.v1` and `comp.outputNesting.v2` (bp00 §3.1; bp01 §7; DQ7). The proof needs NO other invariant: the gate and every F advance end with `normalizeS`, and every other step writes neither F nor S.

- [ ] **Step 1: Write the statement** in `Statements/Store.lean` (imports `AvailableChainFGSA.Statements.Invariants`):

```lean
/-- [bp comp.outputNesting.v2; K2] At every reachable state, `F ⪯ S`, and both
available accessors return S; for every `a`, without synchrony, including
empty and vetoed gates (spec 563–568). -/
def OutputNestingStored (p : Params) : Prop :=
  ∀ st, Reachable p st → NestOK st ∧ confirmed st = st.base.stableRecord ∧ stable st = confirmed st
```

- [ ] **Step 2: Write the lemma statements** in `Proofs/Nesting.lean`:

```lean
/-- [bp comp.outputNesting.v1] The accessor form: `F ⪯ (if F ⪯ S then S else F)`. -/
theorem outputNesting_v1 (F S : Block) : Block.Preceq F (if Block.preceq F S then S else F)
theorem normalizeS_nest (st : State n) : NestOK (normalizeS st)
theorem reconcile_nest (st : State n) : NestOK (reconcile st)
theorem gateStep_nest (p : Params) (st : State n) (s : Slot) : NestOK (gateStep p st s)
theorem process_nest (p : Params) (st : State n) (o : Wire n) (h : NestOK st) :
    NestOK (process p st o)
theorem clock_nest (p : Params) (st : State n) (t : Time) (h : NestOK st) :
    NestOK (clock p st t)
/-- [bp comp.outputNesting.v2; K2] -/
theorem outputNesting_stored (p : Params) : OutputNestingStored p
```

- [ ] **Step 3: Prove them.** `process_nest`: a head vote or a row changes neither `fg` nor `stableRecord` (Task 7); a refused block changes nothing; an accepted block: `GridCO.process_stable`-style lemma for `admitProposal` (`admitProposal` keeps `stableRecord`), then either F is unchanged (keep `h`) or `reconcile_nest`; the row fold keeps both. `clock_nest`: expiry, freeze, early and release keep `stableRecord` and `fg`; the gate ends with `normalizeS`. `outputNesting_stored`: induction on `Reachable`; `initial` has `F = S = genesis`.
- [ ] **Step 4: Review gate G8 and CHECKPOINT.** Commit `FGSA store: output nesting (K2)`.

---

### Task 9: Reconcile facts (K1, K3)

**Files:**
- Create: `AvailableChainFGSA/Proofs/Reconcile.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 2, 7.
- Produces: `reconcile_obligations`, `reconcile_genuine`, `reconcile_savedGenuine`, `reconcile_fastWrite`, `reconcile_stable`, `reconcile_frame` (K3), `storeControls_reconcile` (K3), `reconcile_idem`, `reconcile_saCompat`, `reconcile_harmless` (K1).

**Blueprint:** `bp.reconcile.v1` (bp00 §3.1; bp01 §6.2–6.3). Write `Fb st := eraseFG st.fg.F`.

- [ ] **Step 1: Write the statements.**

```lean
/-- [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_obligations (st : State n) :
    (reconcile st).base.obligations = st.base.obligations.filter (fun row => activeCompatible st row.1)
theorem reconcile_genuine (st : State n) :
    (reconcile st).base.genuine = st.base.genuine.map (fun row => (row.1, row.2.filter (activeCompatible st)))
/-- A label stays evaluated; a result is kept or emptied, never replaced. -/
theorem reconcile_savedGenuine (st : State n) (r : Slot) :
    GridCO.savedGenuine (reconcile st).base r =
      (GridCO.savedGenuine st.base r).map (fun c => c.filter (activeCompatible st))
theorem reconcile_fastWrite (st : State n) :
    (reconcile st).fastWrite = st.fastWrite.map (fun row => (row.1, row.2.filter (activeCompatible st)))
theorem reconcile_stable (st : State n) :
    (reconcile st).base.stableRecord =
      if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st.base.stableRecord
      else eraseFG st.fg.F
/-- [bp bp.reconcile.v1, bp.frame.v1; K3] Reconcile writes no frame input and no
other field: Σ.T, the FG caches, the stamps, both pools, the proposals, the
time, the frozen and early caches, the release snapshots and G. -/
theorem reconcile_frame (st : State n) :
    (reconcile st).fg = st.fg ∧ (reconcile st).proposals = st.proposals ∧
    (reconcile st).rowPool = st.rowPool ∧
    (reconcile st).base.blocks = st.base.blocks ∧
    (reconcile st).base.blockStamp = st.base.blockStamp ∧
    (reconcile st).base.votes = st.base.votes ∧
    (reconcile st).base.voteStamp = st.base.voteStamp ∧
    (reconcile st).base.proposals = st.base.proposals ∧
    (reconcile st).base.now = st.base.now ∧
    (reconcile st).base.frozen = st.base.frozen ∧
    (reconcile st).base.early = st.base.early ∧
    (reconcile st).base.releaseSnapshots = st.base.releaseSnapshots ∧
    (reconcile st).base.goldfishRecord = st.base.goldfishRecord
theorem storeControls_reconcile (p : Params) (st : State p.n) :
    storeControls p.E p.cfg (reconcile st).fg = storeControls p.E p.cfg st.fg
/-- [bp bp.reconcile.v1] (idempotence for fixed F) -/
theorem reconcile_idem (st : State n) : reconcile (reconcile st) = reconcile st
/-- [bp bp.reconcile.v1] After reconcile every SA target is compatible with F. -/
theorem reconcile_saCompat (st : State n) : SACompat (reconcile st)
/-- [bp bp.reconcile.v1; K1] Harmless reconcile: if F is compatible with every
live lease, saved nonempty result, fastWrite member and S, then reconcile
deletes nothing and only moves S forward (to F, if F ⋠ S). -/
theorem reconcile_harmless (st : State n) (hC : SACompat st)
    (hS : Block.Compatible st.base.stableRecord (eraseFG st.fg.F)) :
    reconcile st = { st with base := { st.base with
        stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord
          then st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (reconcile st).base.stableRecord
```

  Note for the report: bp01 §6.3 proves the fastWrite premise of K1 from the origins of old fastWrite members (the "historical case"). That argument needs write origins over a run. `reconcile_harmless` takes the premise as `hC`; the origin form belongs to composition task T10/T12. State this in the task report.
- [ ] **Step 2: Prove them.** Exact effects: unfold `reconcile`, `normalizeS`; `split`. `reconcile_idem`: the filters are idempotent (`List.filter_filter`, `Option.filter` twice), and `normalizeS` of a nested state is the identity. `reconcile_harmless`: `List.filter_eq_self`, `List.map` with `Option.filter_eq_self`; for S, if `F ⋠ S` then compatibility gives `S ⪯ F`.
- [ ] **Step 3: Review gate G9 and CHECKPOINT.** Commit `FGSA store: reconcile facts (K1, K3)`.

---

### Task 10: Admission agreement

**Files:**
- Create: `AvailableChainFGSA/Proofs/Admission.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 2, 7; `KitFG.{pickPair_eq_of_unique, on_block_of_accepted, update_finality_TF}`.
- Produces: `parentFG_spec`, `eraseFG_fgBlock`, `fgBlock_parent`, `fgBlock_slot`, `fgBlock_root`, `fgBlock_notMem`, `fg_on_block_accepts`, `base_admitProposal_accepts`, `admitBlock_accepted_eq`.

The composite test decides; the FG and GridCO tests must then take their accepting branch. Otherwise the base list and Σ.T would drift apart (comp §4.3, "small lemma").

- [ ] **Step 1: Write the statements.** Add to `Statements/Invariants.lean` the definition `Inv0 p st`, the conjunction `KitFG.StoreInv p.E p.cfg st.fg ∧ (∀ X ∈ TF, ∀ Y ∈ TF, X.root = Y.root → X = Y) ∧ (∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ TF, eraseFG B = b)` (the first three fields of `CStoreInv`).

```lean
/-- [M3] Under root injectivity the parent lookup is exact. -/
theorem parentFG_spec (st : State n) (hinj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y)
    (b : Block) (P : FGBlock (Fin n)) :
    parentFG st b = some P ↔ P ∈ st.fg.TF ∧ eraseFG P = b.parent
/-- [bp bp.carrier.v1] (the flat form of `eraseFG (fg B) = erase B`, DQ1) -/
theorem eraseFG_fgBlock {P : FGBlock (Fin n)} {b : Block} (hb : b ≠ .genesis)
    (hP : eraseFG P = b.parent) (rows : List (RowWire n)) : eraseFG (fgBlock P b rows) = b
/-- [bp bp.frame.v1] The FG module accepts every block that the composite accepts. -/
theorem fg_on_block_accepts (p : Params) (st : State p.n) (h : Inv0 p st) (o : Wire p.n)
    (b : Block) (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st o b P rows = true) :
    on_block p.E p.cfg st.fg (fgBlock P b rows) =
      update_finality p.E p.cfg { st.fg with TF := insert (fgBlock P b rows) st.fg.TF } (fgBlock P b rows)
/-- [comp §4.3] The SA block admission accepts every block that the composite
accepts: the block is appended, with its stamp; `now`, leases, saved results
and S do not change. -/
theorem base_admitProposal_accepts (p : Params) (st : State p.n) (h : Inv0 p st) (o : Wire p.n)
    (b : Block) (raw support : List (HeadWire p.n)) (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st o b P rows = true) :
    let base' := GridCO.admitProposal p.toParams.engine st.base (baseProposal o b raw support) b (raw.map baseHead)
    base'.blocks = st.base.blocks ++ [b] ∧ base'.obligations = st.base.obligations ∧
      base'.genuine = st.base.genuine ∧ base'.stableRecord = st.base.stableRecord ∧
      base'.now = st.base.now
```

- [ ] **Step 2: Prove them.** `parentFG_spec`: `KitFG.pickPair_eq_of_unique`; two candidates `P, P'` have `eraseFG P = eraseFG P'`, so equal roots (`eraseFG_root`), so `P = P'`. `fg_on_block_accepts`: `KitFG.on_block_of_accepted`; the four FG refusals fail: the root test gives `fgBlock P b rows ∉ TF`; `P ∈ TF`; `F ⪯ B` is in `blockAccepted`; `fgBlock_slot`, `fgBlock_parent` and `eraseFG_slot` give the slot test. `base_admitProposal_accepts`: unfold `GridCO.admitProposal` and show `bad = false`: the slot formula is the same (`p.toParams.engine.Δ = p.Δ` by `rfl`); `blockKnown st.base b.parent` from `baseTree` and `hP`; `b ∉ st.base.blocks` because a stored `c = b` has a stored FG block with the root of `b`; the proposer test from `baseAuth`. Then `admitVote_blocks`, `admitVote_obligations`, `admitVote_stable` over the fold (GridCO `Map.lean`, `History.lean`; if a needed fold lemma is `private`, prove the fold form locally).
- [ ] **Step 3: Review gate G10 and CHECKPOINT.** Commit `FGSA store: admission agreement`.

---

### Task 11: The composite store invariant (K4), F monotone, SA compatibility

**Files:**
- Create: `AvailableChainFGSA/Proofs/StoreInv.lean`
- Modify: `AvailableChainFGSA/Statements/Store.lean` (add two statements), `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 8–10; `KitFG.{storeInv_init, storeInv_on_block, on_block_F_mono, update_finality_h_max, update_finality_pair, storeControls_eq_fjControls}`; `GridCO.confirmation_mem`, `GridCO.gate_target_origin` (`GenuineHistory.lean:32`).
- Produces: `StoreInvariant`, `FMonotone` (Statements); `cstoreInv_init`, `cstoreInv_process`, `cstoreInv_clock`, `storeInvariant`, `viewRootInj_TF`, `storeControls_eq`, `fg_step_cases`, `process_F_mono`, `clock_F_eq`, `fMonotone`, `process_hmax_mono`, `process_pair_mono`, `saCompat_gateStep`, `actView_eq_image`.

**Blueprint:** `bp.store.v1` (K4) and `bp.frame.v1` (bp00 §3.1; bp01 §4). Q3 is answered: the FG part IS a `SimplexFG.Store` value, so K4 is "the FG part changes only by `on_block`, and `StoreInv` holds".

- [ ] **Step 1: Add the statements** to `Statements/Store.lean`:

```lean
/-- [bp bp.store.v1; K4] Every reachable state satisfies the composite invariant. -/
def StoreInvariant (p : Params) : Prop := ∀ st, Reachable p st → CStoreInv p st
/-- [bp bp.store.v1] Local F moves only to a descendant, at every step. -/
def FMonotone (p : Params) : Prop :=
  ∀ st : State p.n, (∀ o, FGBlock.Preceq st.fg.F (process p st o).fg.F) ∧
    (∀ t, (clock p st t).fg.F = st.fg.F)
```

- [ ] **Step 2: Write the lemma statements** in `Proofs/StoreInv.lean`:

```lean
theorem cstoreInv_init (p : Params) : CStoreInv p (initial p.n)
theorem cstoreInv_process (p : Params) (st : State p.n) (h : CStoreInv p st) (o : Wire p.n) :
    CStoreInv p (process p st o)
theorem cstoreInv_clock (p : Params) (st : State p.n) (h : CStoreInv p st) (t : Time) :
    CStoreInv p (clock p st t)
/-- [bp bp.store.v1; K4] -/
theorem storeInvariant (p : Params) : StoreInvariant p
/-- [bp bp.carrier.v1; K5 + DQ2] Σ.T satisfies `ViewRootInj` with no hypothesis. -/
theorem viewRootInj_TF (p : Params) (st : State p.n) (h : CStoreInv p st) : ViewRootInj st.fg.TF
/-- [bp bp.frame.v1; K4] The live frame is the FJ_FRAME of Σ.T. -/
theorem storeControls_eq (p : Params) (st : State p.n) (h : CStoreInv p st) :
    controls p st = fjControls p.E p.cfg st.fg.F st.fg.TF
/-- [bp bp.frame.v1] The FG projection stutters or takes one FG `on_block` step. -/
theorem fg_step_cases (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).fg = st.fg ∨ ∃ B, (process p st o).fg = on_block p.E p.cfg st.fg B
theorem fMonotone (p : Params) : FMonotone p
theorem process_hmax_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.h_max ≤ (process p st o).fg.h_max
theorem process_pair_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    lexKey (st.fg.h_j, st.fg.J) ≤ lexKey ((process p st o).fg.h_j, (process p st o).fg.J)
/-- [bp bp.activeView.v1] The erased active view is the image of the FG active view. -/
theorem actView_eq_image (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block) :
    b ∈ (actView st).blocks ↔ ∃ B ∈ activeView st.fg, eraseFG B = b
```

- [ ] **Step 3: Prove them.**
  - `cstoreInv_init`: `KitFG.storeInv_init`; the base list is `[genesis]`; `SACompat` holds on empty lists; `S = genesis`.
  - `cstoreInv_process`, head vote and row: no invariant field changes (Task 7). Refused block: the state is the same. Accepted block: `fg`: `KitFG.storeInv_on_block` with `ViewRootInj (insert B TF)` from `viewRootInj_of_rootInj` (root freshness from `blockAccepted`; parent closure from `P ∈ TF`); `rootInj`: the new root is fresh; `baseTree`: `base_admitProposal_accepts`, `update_finality_TF`, `eraseFG_fgBlock`; `SACompat`: if F is unchanged, leases, results and fastWrite are unchanged (`base_admitProposal_accepts`); if F moved, `reconcile_saCompat`; `reconcile_frame` keeps the other fields; `Smem`: S is unchanged or `eraseFG F` with `F ∈ TF` (`StoreInv.Fmem`). The row fold keeps every field.
  - `cstoreInv_clock`: `fg` and the base list do not change. `SACompat` after the gate: a new lease target `B` satisfies `B ⪯ C` with `C = confirmation (actView st) s` (`gate_target_origin`), and `C` is genesis or active (`confirmation_mem`), so `block_compatible_of_preceq_compatible` applies; the saved result is `C`; the fastWrite set is a filter of the active list; release and expiry only delete rows (`release_subset`). `Smem`: `advance S C` is `S` or `C`, and `C` is stored; `normalizeS` writes `eraseFG F`.
  - `fg_step_cases`, `fMonotone`: `KitFG.on_block_F_mono`, `reconcile_frame`, `clock_fg`.
  - `process_hmax_mono`, `process_pair_mono`: `update_finality_h_max`, `update_finality_pair` with `on_block_of_refused`/`on_block_of_accepted`.
  - `actView_eq_image`: `baseTree` and `compatible_iff_eraseFG` with `viewRootInj_TF`.
- [ ] **Step 4: Review gate G11 and CHECKPOINT.** Commit `FGSA store: composite invariant (K4), F monotone`.

---

### Task 12: Axiom audit, full build, map, handoff

**Files:**
- Create: `AvailableChainFGSA/Tests/Axioms.lean`
- Modify: `AvailableChainFGSA.lean`, `lakefile.toml` (`defaultTargets`), `docs/MAP.md` (one new section)

- [ ] **Step 1: `Tests/Axioms.lean`.** One `#print axioms` line for each public theorem of Tasks 2 and 7–11 (as `AvailableChainSA/Tests/Axioms.lean`). Each must print only `propext`, `Classical.choice`, `Quot.sound`, or no axiom.
- [ ] **Step 2: Axiom scan.** `lake env lean --run scripts/CheckFGSAAxioms.lean --expect outputNesting_stored --expect storeInvariant --expect fMonotone --expect reconcile_harmless --expect reconcile_frame --expect viewRootInj_of_rootInj --expect preceq_of_eraseFG_preceq --expect clock_eq_saClock_gate`. Expected: exit 0.
- [ ] **Step 3: Full build.** Add `"AvailableChainFGSA"` to `defaultTargets`. Run `pgrep -fl lean`; wait for a free slot. Run `lake build --wfail` (the full project target). Expected: PASS for every library. Then `bash scripts/check-fgsa.sh`. Expected: exit 0.
- [ ] **Step 4: Map.** Add a section "FG-SA composite model (store)" at the end of `docs/MAP.md`: one row per file, with its role and the K ids. Plan 1a also edits `docs/MAP.md`; add only the new section, so that a merge has no overlap.
- [ ] **Step 5: Report to the coordinator** (no `log.md` or `state.md` in this worktree unless the coordinator asks). The report has:
  - a table: K id / blueprint id → Lean names → extra hypotheses (for example, `reconcile_harmless` takes the fastWrite premise; bp01 §6.3's historical case is run-level);
  - every difference found against the spec, the blueprint and comp §4, and every smoke-test value that differed from the hand computation;
  - the answers used for DQ1–DQ12 and each audit finding that is still open;
  - the validation commands and their results (build, check script, axiom scan);
  - the inputs for composition task T7: the Q1 boundary table, `blockExcluded_stable`, `wellFormed`, `attest`, the content-root premise (DQ3), the Λ placement (DQ4), and the one-tick-per-time premise that `clock_eq_saClock_gate` needs;
  - the inputs for composition task T1 (registry): `comp.outputNesting.v2`, `bp.store.v1`, `bp.reconcile.v1`, `bp.carrier.v1` with the Lean names.
- [ ] **Step 6: Review gate G12 (final) and CHECKPOINT.** Commit `FGSA store: axiom audit, full build, map`.

## Review gates

```text
┌────────┬─────────────────────┬─────────────────────────────────────────────────────┐
│ Gate   │ When                │ Who and what                                        │
├────────┼─────────────────────┼─────────────────────────────────────────────────────┤
│ G0     │ before Task 1       │ Astra plan audit (Codex, astra model). Verdict      │
│        │                     │ ADOPT or ADOPT WITH FIXES, with every blocking and  │
│        │                     │ major finding applied. Report in docs/audit/.       │
│ G1–G5  │ end of Tasks 1–5    │ independent review (a fresh reviewer agent that did │
│        │                     │ not write the code): each definition against its    │
│        │                     │ spec lines; each test value by hand; the Global     │
│        │                     │ Constraints. Findings go to the task report.        │
│ G6     │ end of Task 6       │ Astra model check of Model/*.lean against the spec  │
│        │                     │ and the tree-read inventory (Task 6, Step 4), plus  │
│        │                     │ the independent review.                             │
│ G7–G11 │ end of Tasks 7–11   │ independent review: each statement against its      │
│        │                     │ blueprint statement (bp00 §3.1); no weakened        │
│        │                     │ statement; no new hypothesis without a report line; │
│        │                     │ axioms of the new theorems.                         │
│ G12    │ end of Task 12      │ final independent review of the whole library and   │
│        │                     │ the report; the coordinator decides on the merge.   │
└────────┴─────────────────────┴─────────────────────────────────────────────────────┘
```

A reviewer blocks the CHECKPOINT on: a model rule that differs from the spec without a report line; a statement weaker than its blueprint statement without a report line; a `sorry`, `admit`, project axiom or native evaluation; an import outside the allowed list; a Q1/Q5 dependency.

## Out of scope

- The run layer (composition T7): the `ProtocolSpec` instance, the hooks binding, `ClockLaws`, stamps, receipts, paths, carried-row signatures, K8, and the run form of nesting.
- The engine choice (Q1) and the deliverable form (Q5): the Λ placement, the own-row processing, `pendingRow`, the `LinkedFG` premise, `FGSAClaims`.
- K6–K11 and theorems (b), (c), (c′), (d) (composition T8–T16).
- The origin form of K1 (bp01 §6.3 historical fastWrite case) and `bp.leaseOrigins.v1` (one-chain live targets, ancestor deadlines). Both need write origins over a run.
- The content-root premise (DQ3) and the registry entries (composition T1).
- The leak ledger. The model is ready for it as a derived function (Global Constraints).

## Risks

```text
┌────┬──────────────────────────────────────┬──────────────────────────────────────┐
│ ID │ Risk                                 │ Mitigation                           │
├────┼──────────────────────────────────────┼──────────────────────────────────────┤
│ R1 │ decide is slow on composite states   │ Bool-valued tests; decide +kernel;   │
│    │ (Finset, derive, GridCO lists)       │ smaller fixtures; report fallbacks   │
│ R2 │ A GridCO lemma fixes gridLeasePolicy │ check the [LeasePolicy] variable of  │
│    │ or is private                        │ each lemma; prove a local form       │
│ R3 │ Plan 1b changes GridCO/SA hooks (E4  │ this plan uses only GridCO/SA state  │
│    │ excludes)                            │ functions, not their ProtocolSpec;   │
│    │                                      │ rebuild after a rebase               │
│ R4 │ Merge overlap with plan 1a in        │ append-only edits; one new MAP       │
│    │ lakefile.toml and docs/MAP.md        │ section; resolve at merge            │
│ R5 │ The FG module test fixtures (B1, B2, │ if they change, copy them into       │
│    │ B3, B1', stF) change                 │ Tests/Smoke.lean                     │
│ R6 │ A new frozen spec version before     │ diff against 2e884811; report each   │
│    │ execution                            │ modeled line (Sources, note 1)       │
│ R7 │ The exact SA bridge equality needs   │ state each extra premise; the bridge │
│    │ more premises than planned           │ is a reuse tool, not a spec claim    │
│ R8 │ The Mac lean slots are shared        │ pgrep before each build; module      │
│    │                                      │ targets during steps                 │
└────┴──────────────────────────────────────┴──────────────────────────────────────┘
```

## Open questions (summary)

- Q1 (engine) and Q5 (deliverable) stay open. This plan does not depend on them (Q1 boundary).
- DQ1–DQ12 above, each with a recommended answer. The plan follows the recommendations. G0 (Astra) and the user can change them before Task 1.
- For composition T7: the one-tick-per-public-time premise (DQ5, `clock_eq_saClock_gate`) and the content-root premise (DQ3).
