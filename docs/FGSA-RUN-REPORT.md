# FG-SA run library report

_Plan: `docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11 (branch of the
plan: worktree available-chain-fgsa-plan, read at 0432f6a). Library:
`AvailableChainFGSARun` (the plan leaves the name open, §3.1; this report uses
the plan's working name). Check: `bash scripts/check-fgsa-run.sh`. The T7.13
report extends this file._

## T7.0 records

Source: the T7.0 report (`codex/reports/t7-0-report.md` in the research
tree, 2026-09-29), verdict PASS WITH RECORDS. The items below are copied from
its §1 (base) and §7 (D1–D8, the records that the plan must carry). Its items
D9–D12 are of class "none" (no record needed): D9 (Delivery.lean differs from
469463f only in docstrings), D10 (the T7.6 item 3 route holds), D11 (a note
for T7.2: `FGSA.parentFG_isSome_iff_root` takes `CStoreInv p st`, so the
root-lookup reading of `depsPresent` needs `CStoreInv`, which the T7.5 bridge
gives at reachable states), D12 (procedure: build `AvailableChainKitV2` before
the manifest check).

### Base

```text
┌────────────────────────────┬────────────────────────────────────────────────────────────────┐
│ Item                       │ Value                                                          │
├────────────────────────────┼────────────────────────────────────────────────────────────────┤
│ Base commit                │ 1aa6885e0b78a6b15d0b3eb35ed0599a64dc6302 ("docs:               │
│                            │ PHASE2A-REPORT final gate state"), worktree                    │
│                            │ ~/worktrees/available-chain-t7, branch fgsa-t7, clean tree     │
│ Phase gate (1) I9          │ 3403e58 is an ancestor of the base                             │
│ Phase gate (2) 2a          │ docs/V2-API.md present; V2Manifest --check exit 0; anchor      │
│                            │ AvailableChain.Framework.V2.anchor present (checked by the     │
│                            │ manifest script)                                               │
│ Phase gate (3) spec sync   │ 1944bb8 (61df54a c43cd52 312542a 66a2dc5) is an ancestor;      │
│                            │ base anchor 713f56f (8e15977, 227dbf5) is an ancestor of it    │
│ Phase gate (4) base        │ 1aa6885 contains all three merges                              │
│ main now                   │ 3e48c9f = 1aa6885 + one docs commit (ARCHITECTURE); no Lean,   │
│                            │ lakefile or script change                                      │
│ Store reference base       │ d0d913a (plan §0, key "store"); ancestor of the base           │
└────────────────────────────┴────────────────────────────────────────────────────────────────┘
```

### Records D1–D8

- **D1 (rename: record).** §3.1a writes some names without their
  sub-namespace. Fully qualified: `AvailableChain.V2.Run.{stateBefore,
  stateBeforeTime, readAt, final, emitsAt, tickIdx?, emittedAt, emits,
  processes, handlesAt, acceptsAt, holder, ownSeats, stateBefore_succ,
  step_tick_eq, tickIdx?_spec, emittedAt_eq_emitsAt,
  mem_emittedAt_iff_emits}`; `AvailableChain.V2.{tick, tick_decomp,
  tick_asleep}`; `AvailableChain.V2.ProtocolSpec.{Object, objSelfVisible}`;
  `AvailableChain.V2.Isolation.{base_tick, foldl_recordOwn_base}`. §3.1
  says only "in `AvailableChain.V2`"; that is true as a prefix only.
- **D2 (rename: record).** The restore forms that §3.1a describes in prose
  have names: `AvailableChain.V2.Engine.stateBefore_stable_clock_restore`
  (hrestore_now, SWF, restore step; no `restartFree`) and
  `AvailableChain.V2.Engine.stateBefore_field_prefix_restore`. The Kit also
  has `_noRestart` forms: `stateBefore_now_source_noRestart`,
  `stateBefore_now_le_event_noRestart`, `stateBefore_now_mono_noRestart`,
  `stateBefore_invariant_noRestart`, `stateBefore_stable_clock_noRestart`,
  `clock_field_origin_noRestart` (all in `AvailableChain.V2.Engine`).
- **D3 (none; record the tool).** `stateBefore_invariant` has no separate
  "factors through base" variant. It takes the `recordOwn` step premise.
  `AvailableChain.V2.Engine.recordOwn_preserve_of_base (iso) (Q : iso.Base →
  Prop)` discharges that premise for a predicate on the base.
- **D4 (none; note for T7.6 item 3).** `clock_field_origin` also takes
  `field init = []` and `∀ st o, field (process st o) = field st` (an
  EQUALITY). For the saved-label list `genuine.map Prod.fst`, T7.6 must
  show that FG-SA `process` (with the `reconcile` in admission) keeps the
  label list exactly. The plan says that `reconcile` keeps labels; the
  premise is as 2a planned, so this is not a premise change.
- **D5 (rename: record).** `AvailableChain.GridCO.excludes : GridCO.Params →
  {n} → GridCO.State n → GridCO.Wire n → Bool` has no `[LeasePolicy]`
  argument. "Bind at `slowLeasePolicy`" has nothing to bind. FG-SA calls it
  at `p.toParams.engine`, as `admitHead` calls `admitVote`. Only
  `GridCO.gateFrom`, `GridCO.clockFrom`, `GridCO.gate`, `GridCO.clock`
  take the policy (FG-SA: `SA.gateFrom`, `SA.clockFrom` at
  `slowLeasePolicy`).
- **D6 (rename: record).** SA has no named genesis equality. The three
  equalities `SA.confirmation p st r = SA.confirmationFrom p .genesis st r`,
  `SA.gate … = SA.gateFrom p .genesis …`, `SA.clock … = SA.clockFrom p
  .genesis …` hold by `rfl` (checked in `FGSACheck.lean`, a scratch file of T7.0). Grid CO has the
  named `GridCO.confirmation_eq_from_genesis`, `GridCO.gate_eq_from_genesis`,
  `GridCO.clock_eq_from_genesis`.
- **D7 (rename: record).** The anchor forms of the Grid CO gate lemmas are
  `GridCO.gateFrom_blocks` (`Proofs/Map.lean:954`),
  `GridCO.gateFrom_eq_writeKeys` (`Proofs/Map.lean:695`),
  `GridCO.gateFrom_target_origin` (`Proofs/GenuineHistory.lean:32`),
  `GridCO.confirmationFrom_mem` (`Proofs/RecordSlots.lean:151`, conclusion
  `B = a ∨ B ∈ st.blocks`), and the extra `GridCO.confirmationFrom_extends`
  (`Proofs/Goldfish.lean:132`, `a ⪯ B`). The genesis names stay as
  corollaries. T7 reaches them only through FG-SA store theorems.
- **D8 (rename: record, citation).** `FGSA.fgHead_stored` is at
  `AvailableChainFGSA/Proofs/StoreInv.lean:756`, not `:749` (T7.W text);
  the spec sync moved it. `FGSA.rootInj_all` is still at `:120`.

### Other names from the T7.0 report

- RunCheck (T7.10; report §3): `AvailableChain.V2.Engine.{allTicks,
  allDeliveries, emittedBy}` and `AvailableChain.V2.Engine.{allTicks_spec,
  allDeliveries_spec, emittedBy_spec}`, in the module
  `AvailableChainKitV2.RunCheck` (file `AvailableChainKitV2/RunCheck.lean`,
  frozen Kit entries). `toyRun_valid` is
  `AvailableChain.V2.Tests.Toy.toyRun_valid`
  (`AvailableChainKitV2/Tests/Toy.lean:341`). Where the report and the plan
  differ on a name, T7 uses the report.

## T7.1 Library skeleton and checks

Files: the `lakefile.toml` entry `AvailableChainFGSARun` (own root, in the
default targets), the root `AvailableChainFGSARun.lean`,
`AvailableChainFGSARun/Tests/Axioms.lean`, `scripts/check-fgsa-run.sh`,
`scripts/CheckFGSARunAxioms.lean`, `scripts/CheckFGSARunLease.lean`.

The check script is adapted from `scripts/check-fgsa.sh` (plan §3.1):

- Kept from the store check (G13 and fold-verify fixes): the comment
  tokenizer; the fail-closed header parser (`!UNPARSED`); `find -L -iname
  '*.lean'`; the root-import check; the native-evaluation grep; the text
  allowlist and the same allowlist again on the compiled import data; build
  coverage; the axiom scan; the lease check with the own-parameter rule and
  the reachability backstop (the rules of `CheckFGSALease.lean`, on the run
  roots); the negative controls of the store check, adapted to the run tree
  (the auditor's files in `scripts/fgsa-controls/` are reused).
- Changed: the allowlist is the layer table of §3.1; the closure test also
  forbids `AvailableChainLStar`; there is no Q1/Q5 boundary grep (the run
  library is the run layer).
- New: the v1/v2 name-clash rule (no plain, `hiding` or `renaming` open or
  export of `AvailableChain.V2`, no selective list with `Auth` or `Signed`,
  no namespace with a component `V2`); the used-constant check (no library
  constant uses a constant of `AvailableChainKit.*`,
  `AvailableChainStatements.*`, `AvailableChainGridCO.Proofs.*` or
  `AvailableChainModel.Generic.Run`; generated equation lemmas of other
  libraries are skipped, as in the lease check). New controls: the v1 engine,
  v1 Kit, v1 statements and Grid CO proof imports (text and compiled); the
  name-clash forms (also in a `.LEAN` file and a linked directory, with a
  selective open that must pass); used constants of the v1 Kit, the v1
  statements, the v1 engine, and a Grid CO proof predicate in a statement
  (the T7.W wrapper rule).
- G-walk control (lead, the T7.W wrapper statement rule): the used-constant
  check scans declaration TYPES as well as values. The control
  `negctl_walkWrapper_proofPredicate` states `GridCO.RootInjectiveBelow
  st.base.blocks` and is proved by the store lemma
  `FGSA.rootInjectiveBelow_base` (allowed), so only its type names the
  forbidden constant; the check must print "FORBIDDEN CONSTANT:
  AvailableChain.FGSA.Run.negctl_walkWrapper_proofPredicate uses
  AvailableChain.GridCO.RootInjectiveBelow (AvailableChainGridCO.Proofs.Roots)".
  It imports `AvailableChainFGSA.Proofs.StoreInv`. After the T7.W merge, the
  lead's text (import `AvailableChainFGSA.Proofs.Head`, the same theorem)
  replaces it; the script has that text in a comment. The lead's namespace
  `AvailableChain.FGSARun` is changed to the library namespace
  `AvailableChain.FGSA.Run`.

Validation at T7.1 (Mac, `pgrep -x lean | wc -l` = 0 before each run):
`lake build --wfail AvailableChainFGSARun` exit 0 (4 jobs);
`bash scripts/check-fgsa-run.sh` exit 0 (0 constants, 592 closure modules,
13 negative controls rejected as expected, the G-walk control included);
`lake env lean --run scripts/V2Manifest.lean --check` exit 0 (280 entries in
17 modules). At T7.1 the library has no declaration, so the script passes
`--allow-empty` to the two compiled checks; T7.2 replaces it with an
`--expect` list.
