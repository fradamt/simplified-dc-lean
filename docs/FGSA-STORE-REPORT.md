# FG-SA model store: report (Tasks 1–13)

Branch `fgsa-composition`. Plan: `docs/plans/2026-09-29-fgsa-model-store.md`.
Gate reports: `docs/audit/fgsa-task{6..12}-opus-review.md`,
`docs/audit/fgsa-model-check-report.md`, and the final audit (G13):
`docs/audit/fgsa-final-audit-astra.md`, `docs/audit/fgsa-final-audit-opus.md`,
with the verification of its fold: `docs/audit/fgsa-final-audit-fold-verify.md`.
This file is the Task 13 report with the G13 corrections.

Scope. All results are LOCAL store facts over the over-approximate `Reachable`
(no input check, any clock value; DQ14). The cross-node results hold only for
store pairs under the store-pair premise `ContentAgree`; they do not establish
an unconditional protocol result across nodes, a common full proposal
payload, a run adapter, or safety across nodes. `FastOrigin` is the local
relation that K1 needs; it is not a proof of every clause of
`bp.leaseOrigins.v1` or K6. Run lifts are composition task T7.

## 1. K table: completed local facts and remaining run lifts

```text
┌──────────────────┬──────────────────────────────────────┬────────────────────────────────────┐
│ K id / bp id     │ Lean names                           │ Extra hypotheses / remaining lift  │
├──────────────────┼──────────────────────────────────────┼────────────────────────────────────┤
│ K1               │ reconcile_harmless_origin (Proofs/   │ origin form: FastOrigin F₀ st,     │
│ bp.reconcile.v1  │ Reconcile); admitBlock_reconcile_    │ F₀ ⪯ F, hL, hG, hS. Block step:    │
│                  │ harmless (Proofs/StoreInv). No       │ CStoreInv st, hP, hacc, hL, hG, hS │
│                  │ fastWrite premise. reconcile_        │ (all at the new F). hL = every row │
│                  │ harmless = HELPER only (it has the   │ of obligations, due leases         │
│                  │ fastWrite premise)                   │ included (G9 m2). Lift: T7 (b), K7 │
│ K2               │ outputNesting_stored,                │ none (no other invariant). Run     │
│ comp.outputNest- │ outputNesting_v1,                    │ lift: T7. Conjuncts 2–3 are rfl    │
│ ing.v1/v2        │ finalized_preceq_stable              │ (DQ7)                              │
│ K3               │ reconcile_frame,                     │ none for reconcile_frame and       │
│ bp.frame.v1,     │ storeControls_reconcile,             │ storeControls_reconcile;           │
│ bp.reconcile.v1  │ storeControls_eq                     │ storeControls_eq needs CStoreInv   │
│ K4 core          │ storeInvariant (CStoreInv, 9         │ none. "F, J ∈ T": Fmem + J_mem     │
│ bp.store.v1      │ fields), fMonotone, process_F_mono,  │ (G11 m2). Tick part of "pair, H    │
│                  │ clock_F_eq, process_hmax_mono,       │ monotone": clock_fg                │
│                  │ process_pair_mono, J_mem             │                                    │
│ K4 metadata      │ metadataInvariant (MetaInv, 9        │ none. "T cumulative", "old stamps  │
│ bp.store.v1      │ fields incl. noGenesisWire),         │ unchanged": process_cumulative,    │
│                  │ process_cumulative, clock_cumulative │ clock_cumulative, MetaInv          │
│ K5 local         │ viewRootInj_TF, viewRootInj_of_      │ CStoreInv (root injectivity of Σ.T │
│ bp.carrier.v1    │ rootInj, compatible_iff_eraseFG,     │ holds by construction, DQ2)        │
│                  │ preceq_of_eraseFG_preceq,            │                                    │
│                  │ rootInjectiveOn_of_viewRootInj       │                                    │
│ K5 cross-node    │ fg_eq_of_eraseFG_eq_across,          │ CStoreInv, MetaInv at both stores, │
│ bp.carrier.v1    │ preceq_iff_across,                   │ ContentAgree st st' (store-pair    │
│                  │ compatible_iff_across,               │ premise, DQ3(b), reverses comp D4; │
│                  │ rootInjectiveOn_across (the two-     │ narrowed at G12). Run form         │
│                  │ chain KitFG.accountable premise);    │ ContentRootInjective: T7.          │
│                  │ contentAgree_self                    │ contentAgree_self: no content      │
│                  │                                      │ premise; needs CStoreInv, MetaInv  │
│ K8 input         │ admitBlock_sufficient,               │ CStoreInv, wellFormed wire, stored │
│ bp.receipt-      │ admitBlock_sufficient_absent         │ parent, slot ≤ Σ.s, fresh root     │
│ Coverage.v1      │                                      │ (DQ2) or absent + root premise,    │
│                  │                                      │ F ⪯ b. Run form of K8: T7          │
│ bp.activeView.v1 │ items 1–6: actView_blocks,           │ items 1, 2, 4 and actView_eq_image │
│                  │ actView_genesis_F (1); actView_      │ need CStoreInv; items 3, 5, 6 need │
│                  │ ancestor_closed (2); actView_        │ none (item 6: K ⪯ F). Genesis      │
│                  │ antitone (3); actView_path (4);      │ result of item 6: actView_genesis_F│
│                  │ blockExcluded_stable, actView_eq,    │ or block_genesis_preceq (G7 m4)    │
│                  │ actView_fields (5); actView_noVeto,  │                                    │
│                  │ actView_releaseCount_zero (6);       │                                    │
│                  │ actView_eq_image                     │                                    │
│ SA bridges       │ clock_eq_saClock_offGate,            │ offGate: t not a gate time. gate:  │
│ comp D3, J3      │ clock_eq_saClock_gate (and _gate'),  │ gate time of s, hnew (label not    │
│                  │ actView_admitBlock_sameF,            │ saved; DQ5). Block: CStoreInv, hP, │
│                  │ actView_admitBlock_movedF            │ hacc, F same / F moved (movedF is  │
│                  │                                      │ the SA admission, filtered by the  │
│                  │                                      │ new F, plus reconcile's 3 writes)  │
└──────────────────┴──────────────────────────────────────┴────────────────────────────────────┘
```

Not done here (out of scope): K6–K11, theorems (b), (c), (c′), (d)
(composition T8–T16); the lease parts of bp.leaseOrigins.v1; every run lift.

## 2. Differences found

Against the spec (archive 2e884811): no new undeclared rule difference at the
stated protocol boundary (checked inputs, scheduled event order; G3–G6
reviews, the Astra model check r195, G13). Declared differences:
- DQ10/DQ2 (G13 Opus m4): under a root collision of the GridCO formula, the
  DQ2 root test refuses an honest block; the spec idealizes distinct roots
  (spec 167, 521). `Tests/RootCollision.lean` shows it.
- Release cutoff (r195 D2; `Reachable` docstring; G13 Astra N2):
  `GridCO.releaseCount` (`AvailableChainGridCO/Model/Protocol.lean:397`)
  tests equivocation in all stored label-r votes; spec 1197–1200 tests the
  votes stamped before `q_r`. They agree at the scheduled release before
  same-time deliveries. They can differ after later votes and a repeated or
  backward clock. No statement claims release equivalence on an arbitrary
  store.
Declared model-only fields:
`goldfishRecord`, `frozen`, `early`, `releaseSnapshots`, `base.proposals`
(DQ8); no FG-SA output or duty reads them. Known limits, both inherited or T7
obligations: `goldfishScore` equals the spec score only when support ⊆ raw
(checked by `wellFormed`, not by `process`; G6 O-m4); `headVote` and
`propose` agree with the spec only when `s = st.slot p` (G6 O-m3).

Against the blueprint:
- DQ1 flat wire: `eraseFG (fg B) = erase B` is `eraseFG_fgBlock`.
- DQ2: the duplicate test is root freshness, not "absent". K8
  (`admitBlock_sufficient`) takes a fresh root; `admitBlock_sufficient_absent`
  takes "absent" plus a root premise (G10 m2).
- K1: `hL` quantifies over every row of `obligations`, including due leases
  that the next tick expires (spec 447–448, 736–741). With "live" read as
  "deadline in the future", the blueprint claim is false for such a row
  (G9 m2). T7 (b) and K7 must show compatibility for due leases too.
- bp.store.v1 "F, J ∈ T": `KitFG.StoreInv` has no J field; `J_mem` proves it.
- Stronger than planned: `admitBlock_accepted_eq` has no `Inv0` premise
  (G10 m1); `fastSet_prefix` has `B ≠ genesis` (G7 m2); `ContentAgree` is
  narrowed (G12 M1), so the four cross-node theorems are stronger.
- One extra `MetaInv` field (risk R11): `noGenesisWire` (G12 m1). It needs no
  new premise; it gives `contentAgree_self`.
- Nesting holds for COMPLETED events; the state inside `admitBlock` before
  `reconcile` can have a moved F and the old S (G8 m3).

Against comp §4: D4 is REVERSED (DQ3(b)): a named content premise, no model
check. D3: the tick bridge needs `hnew` (the evaluate-once guard, DQ5) and,
at run level, one tick per public time. J3: with a moved F the block-step
bridge is the SA admission with the blocks filtered by the new F and
reconcile's three writes, not the plain SA admission.

Smoke tests: every planned value agreed with the hand computation (Tasks 3–6;
each docstring has the computation). R1 fallback: `decide +kernel` for the
`stP` test and six G6 tests (plain `decide` hits the recursion limit). No
value rests on `#eval` alone. The G6 negative controls show that each
plausible wrong rule gives a different value.

## 3. DQ answers used and open findings

DQ1 (a) flat wire. DQ2 (a) root test. DQ3 (b) content premise, narrowed at
G12. DQ4 (a) Λ outside `State`. DQ5 (a) evaluate-once guard. DQ6 (a) spec
HEAD tree at read time. DQ7 v2 reading (F ⪯ S, both accessors = S). DQ8 keep
the model caches, declared. DQ9 no hooks; `blockExcluded`, `wellFormed`;
"processed by root". DQ10 keep the GridCO root formula; limit stated. DQ11
docstring tags now, pin table in T15. DQ12 refuse undecodable carried rows.
DQ13 spec `deepest` tie rule (`deepest_spec`). DQ14 `process` separate from
`wellFormed`; `Reachable` over-approximates.

Open: no gate finding is open (G1–G13 closed; each disposition is in the
plan). The last test gap of r195 N3 (an active stored target that only the
FJ filter excludes) is closed by the `stL` tests in `Tests/Smoke.lean` (G13
Astra N3). Open user decision: DQ10/DQ3 (arithmetic roots plus content premise,
or content-coded roots with an admission check across GridCO/SA/FG-SA; I9).
Q1 (engine) and Q5 (deliverable) stay open; objects are v1-typed (J1).

## 4. Validation

```text
┌────────────────────────────────────────────────────┬──────────────────────────────────────┐
│ Command                                            │ Result                               │
├────────────────────────────────────────────────────┼──────────────────────────────────────┤
│ lake build --wfail (full project target)           │ pass, 3601 jobs                      │
│ bash scripts/check-fgsa.sh                         │ exit 0: build; root imports and      │
│                                                    │ direct-import allowlist on parsed    │
│                                                    │ headers (fail closed; find -L        │
│                                                    │ -iname); native scan; Q1/Q5 grep     │
│                                                    │ (Run, Env, Interface, Claims added); │
│                                                    │ axioms (805 constants, 442           │
│                                                    │ theorems), build coverage, direct    │
│                                                    │ imports of 21 FGSA modules on the    │
│                                                    │ compiled data, import closure (5503  │
│                                                    │ modules, no forbidden library);      │
│                                                    │ lease instances (788 constants, 17   │
│                                                    │ generated equation lemmas skipped,   │
│                                                    │ 335 imported definitions inspected,  │
│                                                    │ 76 lease arguments, backstop over    │
│                                                    │ 4203 reached constants)              │
│ negative controls in check-fgsa.sh                 │ all rejected: unlisted library;      │
│                                                    │ wrong-layer import (KitFG in Model/, │
│                                                    │ Proofs in Statements/); import after │
│                                                    │ a comment and a line break; orphan   │
│                                                    │ modules with a sorry (behind a       │
│                                                    │ commented root import, and with a    │
│                                                    │ .LEAN name; root check and compiled  │
│                                                    │ coverage check); SAPC in the         │
│                                                    │ closure; a «» module name, a prelude │
│                                                    │ line, a .LEAN file and a linked      │
│                                                    │ directory (text allowlist, Q1/Q5     │
│                                                    │ grep, compiled allowlist); lease:    │
│                                                    │ direct default call, alias wrapper   │
│                                                    │ with its own policy parameter,       │
│                                                    │ generic wrapper with an alias policy │
│                                                    │ type, imported wrapper that fixes    │
│                                                    │ the default, LeasePolicy.mk outside  │
│                                                    │ AvailableChain; imported let, beta,  │
│                                                    │ private, irreducible-alias and non-  │
│                                                    │ AvailableChain wrappers (G13 fold    │
│                                                    │ verification)                        │
│ lake env lean --run scripts/CheckFGSAAxioms.lean   │ exit 0                               │
│ --expect <the 15 names of Step 2>                  │                                      │
│ Tests/Axioms.lean (206 #print axioms)              │ only propext, Classical.choice,      │
│                                                    │ Quot.sound (8 theorems: none)        │
│ grep sorry/admit/native_decide/axiom               │ none in AvailableChainFGSA (outside  │
│                                                    │ comments)                            │
└────────────────────────────────────────────────────┴──────────────────────────────────────┘
```

Import closure after the merge with post-1b main (checked read-only on main
5f65103): FGSA's transitive closure reaches the libraries
`AvailableChainGridCO`, `AvailableChainKit`, `AvailableChainKitFG`,
`AvailableChainModel`, `AvailableChainSA`, `AvailableChainSimplexFG` and
`AvailableChainStatements`. `AvailableChainKit` enters through the Grid CO
proofs (`AvailableChainKit.Engine.EngineClock` and `.Execution`, after the
Kit split c79b473); like `AvailableChainStatements`, it is a declared
transitive dependency. No module of `AvailableChainFramework`,
`AvailableChainRegistry`, `AvailableChainSAPC`, `AvailableChainWitnesses` or
`AvailableChainEngineV2` is reached. FGSA imports no Kit module directly, so
the direct-import allowlist does not change.

## 5. Inputs for composition task T7

- Duty slot: `headVote` and `propose` need `s = st.slot p` (G6 O-m3).
- Q1 boundary table (plan §Q1) with the v1 object dependency (J1); a v2
  decode adapter keeps Store, Statements and Proofs (R10).
- `blockExcluded` and `blockExcluded_stable` (DQ9 exclusion hook);
  `wellFormed` and `blockAccepted_of_wellFormed` (input check; every handler
  call must have a checked input, `DeliveryWellFormed`, DQ14).
- "Processed" for a proposal = by root (`∃ Y ∈ Σ.T, Y.root = b.root`, DQ9).
- `attest` takes Λ and returns (row, Λ′); Λ is not in `State` (DQ4); the
  record/emission order and own-row admission (spec 681) are T7 obligations.
- Content premise: the run premise is `ContentRootInjective` (DQ3). Deriving
  the store-pair premise `ContentAgree st st'` for two honest stores needs
  `MetaInv` and the run lemma "every stored wire is a payload that the node
  processed" (G12).
- `ContentAgree` is the store-pair premise (DQ3(b), narrowed at G12 to the
  erased block and the rows); its run form is `ContentRootInjective`. It is
  false on honest-fork runs under the present root formula (DQ10/I9) and on
  runs with faulty content equivocation; the cross-node lemmas are vacuous
  for such store pairs (`Tests/RootCollision.lean`: `not_contentAgree`). One
  store with itself needs no content premise: `contentAgree_self` needs only
  `CStoreInv` and `MetaInv`, which hold at every reachable state.
- DQ10 root limit: `RootInjective` and `ContentRootInjective` fail on honest
  forks (roots `s·(parent+1)` collide) and can be forced by a faulty
  proposer; inherited from GridCO/SA/SA-PC/L*.
- DQ10 and DQ2 together (G13 Opus m4): under DQ10 collisions the DQ2 root
  test refuses honest blocks (`Tests/RootCollision.lean`: a node that holds
  `node(genesis, 4)` refuses the honest `node(node(genesis, 1), 2)`, root 4).
  So the model differs from the spec there; the K8 run form and every
  coverage claim need `RootInjective` for this reason too.
- `clock_eq_saClock_gate` needs one tick per public time (DQ5).
- Release event order (G13 Astra N2): the release at `q_r` must run before
  the deliveries of the same time and must not repeat at `q_r` or run after a
  backward clock; then `GridCO.releaseCount` equals the spec count. One tick
  per public time alone does not state this order.
- K1 reading: "K1 `hL`: live = present in `Σ.lease` (`obligations`),
  including due leases that the next tick expires (spec 447–448, 736–741)".
  So theorem (b) and K7 must show compatibility for due leases as well.
- K8 run form needs `hfresh` from `RootInjective` plus absence (or use
  `admitBlock_sufficient_absent`), and `hwf` from `DeliveryWellFormed`.

## 6. Inputs for composition task T1 (registry)

```text
┌─────────────────────────┬────────────────────────────────────────────────────────────┐
│ Registry id             │ Lean names                                                 │
├─────────────────────────┼────────────────────────────────────────────────────────────┤
│ comp.outputNesting.v2   │ OutputNestingStored, outputNesting_stored,                 │
│                         │ finalized_preceq_stable (v1: outputNesting_v1)             │
│ bp.store.v1             │ StoreInvariant/storeInvariant, CStoreInv, J_mem,           │
│                         │ FMonotone/fMonotone, process_F_mono, clock_F_eq,           │
│                         │ process_hmax_mono, process_pair_mono,                      │
│                         │ MetadataInvariant/metadataInvariant, MetaInv,              │
│                         │ process_cumulative, clock_cumulative                       │
│ bp.frame.v1             │ storeControls_eq, storeControls_reconcile, fg_step_cases,  │
│                         │ reconcile_frame                                            │
│ bp.reconcile.v1         │ reconcile_* exact effects, reconcile_idem,                 │
│                         │ reconcile_harmless_origin (K1), admitBlock_reconcile_      │
│                         │ harmless (K1 at a block step), reconcile_fastOrigin        │
│ bp.carrier.v1           │ Carrier.lean (local), viewRootInj_TF, CrossNode.lean       │
│                         │ (cross-node, ContentAgree), stored_wire_of_block           │
│ bp.activeView.v1        │ the six items above, actView_eq_image, saCompat_gateStep,  │
│                         │ fastOrigin_gateStep                                        │
└─────────────────────────┴────────────────────────────────────────────────────────────┘
```

## 7. Status after plan I9 (2026-09-29)

This section does not change the text above. Plan I9
(`docs/plans/2026-09-29-i9-derived-roots.md`) makes block roots derived
(`FRAMEWORK-DESIGN.md` §12 I9). The user decided the open DQ10/DQ3
question of §3: content-coded roots, with the parent-root check as the
store dependency lookup.

- DQ10 is superseded. The GridCO root formula is removed. Base and FG
  roots use the same `nodeRoot`, and both root functions are injective
  on their whole types (`Block.root_injective`,
  `FGBlock.root_injective`). So the DQ10 root limit of §2, §3 and §5 does
  not hold now: honest forks and faulty proposers cannot give two
  distinct blocks with one root. `RootInjective` holds for every run
  (`rootInjective_all`).
- DQ2 keeps its root test, but its declared difference in §2 is gone.
  The case "same root, distinct block" is impossible now. So the DQ2
  root test refuses a block only when the same block is already stored.
  `Tests/RootCollision.lean` cannot show the old limit; Task 9 changes
  it into positive tests (distinct roots, `ContentAgree` holds, and a
  repeated block is refused as a duplicate). [[CONTROLLER: confirm
  after Task 9]]
- DQ3(b) and `ContentAgree`: planned in Task 9. The base body packs the
  application value and the ordered signed rows (`packBody`). `rowsOk`
  checks this packing in `wellFormed` and in `blockAccepted`; it is a
  content check, not a root check. `MetaInv.wireTree` gets the stored
  content equality. Then `ContentAgree st st'` is a theorem for any two
  stores that satisfy `CStoreInv` and `MetaInv`. The cross-node theorems
  keep their `ContentAgree` premises, which are now redundant.
  [[CONTROLLER: confirm after Task 9: theorem names, the status of the
  run premise `ContentRootInjective` of §5, and the §4 validation
  numbers]]
