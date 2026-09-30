# FG-SA architecture map

_Shared map for three sessions. Created 2026-09-29 from DC-simplify's
draft 1. One screen per section; detail goes in the linked documents.
Update it when a module, an interface, a constraint or the milestone order
changes, and tell the other sessions._

```text
┌────────────────┬──────────────────────────────────┬─────────────────────┐
│ Session        │ Owns                             │ Map sections        │
├────────────────┼──────────────────────────────────┼─────────────────────┤
│ DC-simplify    │ spec, blueprint, research        │ §1–§2, §6–§7        │
│ (tip-stability)│                                  │                     │
│ lean-framework │ engine, framework, I9, 2a/2b/2c, │ §3–§4               │
│                │ 1c                               │                     │
│ fgsa-lean      │ T7/T1, F0–F6 (FG-SA claims in    │ (reports to both)   │
│                │ Lean); docs/FG-COMPOSITION.md    │                     │
│                │ (registry, pins)                 │                     │
│ all            │ milestones, links                │ §5, §8 (shared)     │
└────────────────┴──────────────────────────────────┴─────────────────────┘
```

## 1. Goal and priority

- Target: **FG-SA fully specified and verified** (user, 2026-09-29).
  FG-SA = the plain SA available chain (AC) + the DC finality gadget (FG),
  with the FJ root rule.
- Order: FG-SA needs first, then SA (its base), then the rest. Grid CO,
  SA-PC, L* and SimplexFG work is DEFERRED, not deleted; existing code and
  registry entries stay and stay green (user clarification, 2026-09-29).
- End state: the spec is frozen, and every main blueprint claim is a
  checked Lean theorem about FG-SA runs.

## 2. Protocol architecture (paper)

```text
┌──────────────────────────────────────────────────────────────────────┐
│ Substrate: cumulative tree Σ.T (fixed σ, stamps), admission F ⪯ B,   │
│ receipt premise                                                      │
├───────────────────────────────┬──────────────────────────────────────┤
│ AC = plain SA                 │ FG = DC finality gadget              │
│ votes, leases, fast/slow      │ rows, chain states σ, F, J, h_max,   │
│ lock, genuine results,        │ finality acceptance, Λ record        │
│ available output              │                                      │
├───────────────────────────────┴──────────────────────────────────────┤
│ Composition: joint selection functions                               │
│ live_root · HEAD eligibility · C_fg · proposer head · finality head  │
│ (triple (h_j, J, h_F); finality_pair is FG's client function on it)  │
└──────────────────────────────────────────────────────────────────────┘
 AC → joint: X_r and leases; HEAD votes in the substrate pools (T-VOTE);
          AC services to the joint selections (H2′, HEAD clauses of H2.A
          and H3). S enters proofs only (T-START, T-SMONO).
 joint → FG: C_fg; the finality-head triple, also with no source; the
          carrier chain (honest proposals from slot s+2 have K ⪯ parent
          and carry rows, T-ROWS).
 FG → joint/AC (frame): FJ root Z + contest band; floor lo also relaxes
          AC eligibility; F for act(Σ), admission, reconcile, and the
          gate walk from Σ.F.
```

- Minimal AC→FG channel (blueprint 01 §1, r212/r212b): source
  candidates/C_fg and the carrier chain. The head selections read the
  substrate vote pools directly (proposer: previous-slot pool; finality
  head: current-slot pool), as `propose_block` and `get_fg_vote` do. So
  "HEAD votes are not a third AC→FG stream" holds for this partition
  only: the finality head reads HEAD votes through the joint function.

- The glue goes both ways by design (user): AC creates targets for FG; FG
  feeds back restrictions on the tree. Modular-spec study
  (`tip-stability/codex/scratch/modular-spec-study.md`): the spec splits
  into substrate, FG module, AC module and a composition section; no
  protocol change is needed.
- Proofs compose by induction over the trace index, as in DC. Clean and
  P1 use their stated channel properties; 6Δ inclusion also uses the
  proposer's full-tree walk (a joint function). The finality kernel is a
  composition theorem: it uses the healing witness, source/carrier facts,
  H2′, the HEAD clause of H2.A, H3/H4, the composition services
  T-START/T-SMONO/T-EXACT/T-VOTE/T-WALK, T-ROWS with matching-state bit
  persistence, and FG/substrate facts; Q0 (in QF2/QF4) also uses H5/H6.
  Healing supplies one common witness tuple (r_G, u₀, M, r*, s*, C*)
  through H.22, and μ = μ(run, GST) as a function of the run, not a
  witness field; H-time supplies the GST bound.
- Lean consequence: v2 `Isolation` cannot express the channels
  (`fgsaIso` puts the whole FG store in base), so F0 adds channel files
  in the FG-SA claims library (`Channels`, `ChannelProps`, `Compose`).
- Transport: FG rows travel packed in the block body (I9 `packBody`,
  `rowsOk` in `wellFormed`); the block root commits to them.
- Design rules (user): stay close to DC and justify every divergence;
  latest certificate only; outputs nest by construction; FG never vetoes
  blocks; timeliness only on sending.
- Authority: `spec/fgsa-protocol.tex` (adopted c1ea1db0, 2026-09-29;
  replaces 4e85ff34 with two changes: the pre-GST delivery clause of the
  partial-synchrony premise (OD6, as v2 `PartialSynchrony`) and the
  healing-interface names aligned with the blueprint;
  `spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md`; 4e85ff34 made the SA
  walk start at Σ.F). Blueprint line citations use the 4e85ff34 numbering.
  Proofs: `blueprint/` (00 outline; 01 foundations; 02
  Clean; 03 P1 and inclusion; 21 healing with `HEALING_INPUT`; 22
  finality).

## 3. Lean architecture (available-chain)

Layers (design §1). L0, L1, LM, L2 and L3 import nothing from L4–L6.

```text
┌────┬────────────┬──────────────────────────────────────────────────────┐
│ L  │ Layer      │ Lean libraries                                       │
├────┼────────────┼──────────────────────────────────────────────────────┤
│ L0 │ Engine     │ AvailableChainModel (objects; Block with derived     │
│    │            │ roots after I9; v1 Generic engine);                  │
│    │            │ AvailableChainEngineV2/Engine (v2, from 2a)          │
│ L1 │ Conditions │ AvailableChainStatements (v1); EngineV2/Conditions,  │
│    │            │ EngineV2/Laws (Isolation, HooksSound, OutputsFactor) │
│ LM │ Modules    │ AvailableChainSimplexFG (FG store, chain states,     │
│    │            │ client, evidence)                                    │
│ L2 │ Facets     │ Framework/Facets; v2 Interface (EngineV2)            │
│ L3 │ Catalog    │ AvailableChainFramework (Claim, Profile, Catalog/*)  │
│ L4 │ Instances  │ GridCO (policy-generic; SA = GridCO at               │
│    │            │ slowLeasePolicy), SA, FGSA, SAPC, LStar;             │
│    │            │ Registry/Instances                                   │
│ L5 │ Kits       │ AvailableChainKit (v1), AvailableChainKitV2,         │
│    │            │ AvailableChainKitFG (FG proofs, Pins)                │
│ L6 │ Registry   │ AvailableChainRegistry, catalog.lock, MATRIX.md      │
└────┴────────────┴──────────────────────────────────────────────────────┘
```

A0 step 2 adds `AvailableChainGeneric`, a default library with separate
Statements and Proofs modules in Pure, V2 and AC. Statements expose definitions
and `f_def` lemmas; Proofs have a public section without `@[expose]`.
`AvailableChainGeneric.lean` imports the 21 modules below in order. The library
glob also builds Tests; the facade does not import Tests. Paths below are
relative to `AvailableChainGeneric/` and omit `.lean`.

```text
┌──────────────────────────┬──────────────────────────────────────────────┐
│ Module                   │ Role                                         │
├──────────────────────────┼──────────────────────────────────────────────┤
│ Statements/Pure/Quorum   │ qF; FaultQ, FaultX and Batch bounds          │
│ Statements/Pure/FirstBad │ AGRule, FirstFailure, WindowRule, RetroAt    │
│ Statements/Pure/Schedule │ Patterns, recurrence and window definitions  │
│ Statements/Pure/Walk     │ Suffix premises and E-4 walk statements      │
│ Statements/Pure/Props    │ CompatOn/At, MonoOn, BelowOn, ServedOn       │
│ Statements/V2/Reads      │ Run indices, pubFloor, HonestSlot, Pending   │
│                          │ E-9 time/index statement PROVED              │
│ Statements/V2/Counts     │ faulty and awakeHonest                       │
│ Statements/V2/Obs        │ Time observations with optional proposals    │
│ Statements/V2/Interface  │ FinalityInterface extends the v2 interface   │
│ Statements/V2/Receipt    │ DeliveryWithin; E-9 statements PROVED        │
│ Statements/V2/Regimes    │ Regime cores, LabelSync, LabelFacts, SeedAt  │
│ Statements/AC/Reads      │ ACReads, ACLaws, gate and reconcile reads    │
│ Proofs/Pure/FirstBad     │ Strong induction for the FirstBad rules      │
│ Proofs/Pure/Schedule     │ Pattern, window and recurrence facts         │
│ Proofs/Pure/BlockOrder   │ Block order, compatibility and path facts    │
│ Proofs/V2/Fields         │ ownRecord_fold_restart                       │
│ Proofs/V2/Reads          │ E-9 time/index bridge                        │
│ Proofs/V2/Induction      │ Invariant and interval lifts; kept_from_seed │
│ Proofs/V2/Receipt        │ E-9 proofs; two DeliveryWithin producers     │
│ Proofs/V2/Regimes        │ Six LabelSync and LabelFacts facts           │
│ Proofs/AC/Output         │ output_step_of_restartFree                   │
│ Tests/Axioms             │ Kernel axiom audit of every public theorem   │
│ Tests/FoldRestart        │ Two special cases of the restart fold        │
│ Tests/Schedule           │ Window-bound and recurrence examples         │
└──────────────────────────┴──────────────────────────────────────────────┘
```

- KitFG definition modules: `StoreInvDef` holds the unchanged `StoreInv`;
  `ViewLock` states the strict height bound; `HonestRows` holds the three
  honest-row premises. Each uses `@[expose] public section`.
- KitFG `Certificates` adds E-15 row-step commutativity and idempotence,
  fold permutation and duplicate removal, and transition equality by row set.
- FGSA E-11 adds `LeaseBelowOutputStore` in `Statements/Invariants` and
  `StoreBundle` with `StoreBundleInvariant` in `Statements/Store`. The bundle
  has cstore, meta, nest and lease fields; the E-11 statements are PROVED.
- `AvailableChainFGSA/Proofs/LeaseOutput` proves the E-11 stored-target invariant.
- `AvailableChainFGSA/Proofs/StoreBundle` proves E-11 by bundle induction
  (`storeBundleInvariant`).
- `AvailableChainFGSARun` (T7.2) holds the v2 protocol, label families,
  isolation, wire adapters, and exclusion proofs, with separate Tests.

How the pieces meet:
- FG-SA store: `FGSA.State = { base : GridCO.State, fg : SimplexFG.Store,
  pools, … }` with glue handlers. Base facts come from the policy-generic
  Grid CO proofs at `slowLeasePolicy`; FG store facts come from KitFG.
- Blocks (I9): `Block.node parent slot body`; the root is derived,
  `nodeRoot parent.root slot body`, injective through the `epair` codec.
  FG-SA packs FG rows into the body (`encFGBody`); `rowsOk` is the same
  function in `wellFormed` and `blockAccepted`.
- FG-SA on engine v2 (T7): `Node = {st, rec}`, `base = st`, `rec = Λ`
  (durable). Label families: HEAD labels AP and fresh (`CStar`); FG labels
  `Linked`; proposal labels AP and `SingleSeat`, one label per slot
  (`Interface.propLabel_injective`).
- Walks: `ghost` takes an anchor. The base has `confirmationFrom a`,
  `gateFrom a` and `clockFrom a` (713f56f); the old names are the genesis
  forms. SA uses genesis; FG-SA uses Σ.F (spec sync, 1944bb8).

Engine v2 decisions (design §2), one line each:
- E1 duties and keys: `Auth = seat ℓ i | none`; a proposal duty is a
  one-seat label; no global `n`.
- E2 seats: `seats ℓ`, `Run.seatOf ℓ`; committee models are conditions
  (`CStar`, `Linked`, `SingleSeat`).
- E3 weights: later additions (seat multiplicity plus conditions).
- E4 delivery outcomes: a delivery calls the handler; exclusions are
  explicit; deliverability (`RelayFeasible`) comes in plan 1c.
- E5 own-signature record: `selfVisible`, `recordOwn`, atomic tick;
  `Isolation` factors the AP part through `base`, so AC facts transport to
  the AP projection.
- E6 restart: `restart v t`, `st ↦ restore (durable st)`. FG-SA interim
  form: Λ durable, store reset; the anchor form (Λ + F) comes with the
  optional anchor-and-pruning claim.

## 4. Constraints

- Proofs: no `sorry`, `admit`, `native_decide` or new axioms;
  `decide +kernel` is allowed. Every gate runs an axiom check.
- Toolchain v4.34.1, Mathlib d13f23b7; never `lake update`; never a new `lean_exe`
  (scripts run with `lake env lean --run`). The Mac has 3 Lean slots
  (check `pgrep -fl lean` first); FCR builds run on the NUC.
- Lock: `scripts/CatalogLock.lean` hashes the dependency closure of every
  declaration in the locked modules (framework, statements, catalog; not
  the protocol libraries). A change needs an expected-name list,
  `--write --allow-changes`, a clean `--check`, and a lock-log entry in
  design §8. Companions and optional claims only add lines.
- V2 freeze (2a gate, 1aa6885): every declaration in `docs/V2-API.md` is
  frozen, with a per-entry hash; `scripts/V2Manifest.lean --check` checks
  it. Engine entries are also locked through anchor defs in
  `AvailableChainFramework.V2`. Never edit `anchor`; add a new anchor def.
  New declarations go after the existing ones or in a new module; the
  manifest module blocks are append-only.
- T7 import guard: the FG-SA run library imports no v1 Kit, v1
  Statements, v1 engine or `GridCO.Proofs.*` directly, and a used-constant
  check backs the rule (the import closure cannot be v1-free). FG-SA
  reaches Grid CO walk and score lemmas through wrappers in
  `AvailableChainFGSA.Proofs.*` (option b2; `fgHead_stored` is the
  precedent). Wrapper statements use only model-level constants. The move
  of the pure lemmas to `GridCO/Walk/` (about 70 declarations) is deferred.
- DC Lean is a reference, not a dependency (`using!`, R ≥ 3).
- Process: a plan per phase with an audit; a task review for each task and
  a final branch review; Claude + Astra before big decisions, a full audit
  before major ones; decisions taken without the user are logged. Codex
  always with `-c service_tier="fast"`. Commits by explicit path;
  worktrees under `~/worktrees/`.

- Generic API: `docs/GEN-API.md` records Statements types and values;
  `lake env lean --run scripts/V2Manifest.lean --scope gen --check` checks it.
  Before G-F0a, a Statements edit updates the manifest in the same commit;
  from G-F0a it is append-only (D15).
- `bash scripts/check-build.sh` runs all checks below after a full build.
  `docs/LEAN-ARCHITECTURE.md` gives the module and import rules.

```text
┌───────┬─────────────────────────┬──────────────────────────────────────────┐
│ Check │ Script (scripts/)       │ Rule                                     │
├───────┼─────────────────────────┼──────────────────────────────────────────┤
│ (a)   │ check-module-headers.py │ module headers and public imports        │
│ (b)   │ check-expose.py         │ Proofs expose only allowed definitions   │
│ (c)   │ rebuild-cone-test.sh    │ A proof-only edit rebuilds one module    │
│ (d)   │ CheckProofEqns.lean     │ Proofs export no new equation lemmas     │
│ (e)   │ check-layers.py         │ Module imports follow the layer rules    │
│ (f)   │ shake-report.sh         │ Unused imports; report only, no --fix    │
│ (g)   │ chain-depth.py          │ Longest import chain; report only        │
│ (h)   │ check-transparency.py   │ Transparency option position and reasons │
│ (i)   │ check-gly-rules.sh      │ GLY rules and per-rule baselines         │
└───────┴─────────────────────────┴──────────────────────────────────────────┘
```

## 5. Milestones

```text
┌────┬──────────────────────────────────────┬──────────────────────────┐
│ M  │ Content                              │ Status 2026-09-30        │
├────┼──────────────────────────────────────┼──────────────────────────┤
│ 1  │ I9 derived roots + engine v2 core    │ done: I9 3403e58; 2a     │
│    │ (2a)                                 │ 1aa6885                  │
│ 1+ │ Post-I9: walk anchor                 │ anchor 713f56f and spec  │
│    │ (`confirmationFrom`/`gateFrom`);     │ sync 1944bb8 done; Pins  │
│    │ FG-SA spec sync (walk from F, Pins)  │ re-pin next (fgsa-lean)  │
│ 2  │ T7/T1: FG-SA run instance on v2,     │ T7.0 base ready;         │
│    │ FGSAClaims, registry map             │ T7.2 landed (30a843f)    │
│ A0 │ Step 2: Generic statements and kits  │ I01–I23, I25 landed;     │
│    │ plus the build checks and manifest  │ I24 close gate in review │
│ 3  │ 1c for FG-SA: run construction and   │ to plan; order (before   │
│    │ inhabitation for every horizon       │ 2b/2c) waits for user    │
│ 4  │ F0 statement layer → F1 foundations  │ scoped; F0–F2 draft      │
│    │ → safety lane (Clean, P1/inclusion)  │ running                  │
│    │ ∥ liveness lane (finality kernel,    │                          │
│    │ healing) → F6 GST bounds             │                          │
│ -  │ Deferred: 2b lift, 2c (restart       │ deferred                 │
│    │ extension, I1 floor), Grid CO items, │                          │
│    │ anchor + pruning optional claim      │                          │
└────┴──────────────────────────────────────┴──────────────────────────┘
```

## 6. Decisions that shape the architecture

- I9: root derived from content; the block carries its parent root; the
  store looks up the parent; no wire check (P2P spec deferred).
- Restart: interim form keeps Λ and resets the store; the faithful form
  (Λ + anchor at F) comes with the optional anchor feature.
- SA walk starts at F (user, 2026-09-29).
- Pruning: an optional claim "prunable at F", not an obligation; no root
  set needed.
- Leak claims: parked; not in the first verification target.

## 7. Open architectural questions

- Interface gap: CLOSED in the blueprint (r212/r212b, 2026-09-29):
  `HEALING_INPUT` split with H5/H6, exact map to the spec's H0–H4, kernel
  dependency list, scoreSuffix for X ⪰ D. Open: align the spec's
  `HEALING_INPUT` names (next spec revision, with the OD6 pre-GST
  sentence).
- Registry: new ids fj.descent.v2, fj.twoChanges.core.v2,
  ap.headReachesLo.v6 (blueprint 21); the three old ids are WITHDRAWN for
  current use (policy §0; v5 still true in its scope); fj.frame.v4 comes
  with r213. The re-pin commit (fgsa-lean) follows r213.
- Representation option (needs a proof first): filter AC records by the
  current F at read time, as DC does, instead of the reconcile write.
- The post-gate cut: F0–F2 draft uses a new reader `afterTicks` (no v2
  change).
- One-repair healing is open. Healing bounds (k ≤ 2R+1, G = 8Δ): B_H
  stays 295Δ/343Δ as the general target (the F6 Lean target). Separate
  bounds: HG.7 upper 268Δ/312Δ; HG.8a upper 204Δ/240Δ (lemma L4-R, no
  cut change, no spec change; in review, then r213). Lower bound
  89Δ−1 tick / 105Δ−1 tick for Δ ≥ 2 (reviewed VALID). The cut change B
  (196Δ/228Δ) is a documented option only.

## 8. Where the detail is

- Research (tip-stability): `state.md`, `log.md`, `spec/`, `blueprint/`,
  `codex/`.
- Lean: `docs/FRAMEWORK-DESIGN.md` (framework), `docs/FG-COMPOSITION.md`
  (FG composition), `docs/MAP.md` (contract to Lean), `docs/audit/`.
- Lean module rules: `docs/LEAN-ARCHITECTURE.md`; Generic Statements API:
  `docs/GEN-API.md` (checked by `V2Manifest --scope gen --check`).
- Plans (`docs/plans/`): framework-phase0, phase1a-gate-catalog,
  phase1b-instances, fg-module, fgsa-model-store (all closed);
  i9-derived-roots (merged 3403e58); phase2a-engine-v2-core (merged
  1aa6885; `docs/PHASE2A-REPORT.md`);
  fgsa-composition-t7-t1 (r11 adopted, 2ec3003; in
  `~/worktrees/available-chain-fgsa-plan`).
