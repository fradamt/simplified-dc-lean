# FG-SA architecture map

_Shared map for the lead session (tip-stability, DC-simplify) and the
framework session (available-chain). Created 2026-09-29 from DC-simplify's
draft 1. One screen per section; detail goes in the linked documents.
Update it when a module, an interface, a constraint or the milestone order
changes, and tell the other session. Owners: §1–§2 and §6–§7 lead session;
§3–§4 framework session; §5 and §8 shared._

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
            targets (C_fg: fresh fast source; target/timeout from Λ)
   ┌────────────────────────────────────────────────────────────┐
   │                                                            ▼
┌──┴──────────────────────────┐                 ┌───────────────────────────┐
│ AC = plain SA               │                 │ FG = DC finality gadget   │
│ votes, leases, fast/slow    │                 │ rows, chain states σ,     │
│ lock, genuine results,      │                 │ F, J, h_max, finality     │
│ available output            │                 │ acceptance, Λ record      │
└──▲──────────────────────────┘                 └──┬────────────────────────┘
   │  restrictions on the tree: FJ root + contest band, SA walk from F,    │
   └──────── reconciliation of AC records when F advances ─────────────────┘
```

- The glue goes both ways by design (user): AC creates targets for FG; FG
  feeds back restrictions on the tree.
- Transport: FG rows travel packed in the block body (I9 `packBody`,
  `rowsOk` in `wellFormed`); the block root commits to them.
- Design rules (user): stay close to DC and justify every divergence;
  latest certificate only; outputs nest by construction; FG never vetoes
  blocks; timeliness only on sending.
- Authority: `spec/fgsa-protocol.tex` (adopted 42d557a2; next revision:
  SA walk from F). Proofs: `blueprint/` (00 outline; 02 Clean; 03 P1 and
  inclusion; 21 healing with the `HEALING_INPUT` interface; 22 finality,
  which imports only that interface).

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
- Walks: `ghost` takes an anchor. Planned after the I9 merge:
  `confirmationFrom a` and `gateFrom a` in the base, with the genesis forms
  as the old names; SA uses genesis, FG-SA uses Σ.F.

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
- Toolchain v4.30.0-rc2; never `lake update`; never a new `lean_exe`
  (scripts run with `lake env lean --run`). The Mac has 3 Lean slots
  (check `pgrep -fl lean` first); FCR builds run on the NUC.
- Lock: `scripts/CatalogLock.lean` hashes the dependency closure of every
  declaration in the locked modules (framework, statements, catalog; not
  the protocol libraries). A change needs an expected-name list,
  `--write --allow-changes`, a clean `--check`, and a lock-log entry in
  design §8. Companions and optional claims only add lines.
- V2 freeze: after the 2a gate, every declaration in `docs/V2-API.md` is
  frozen; later stages only ADD declarations.
- T7 import guard: the FG-SA run library imports no v1 Kit, v1
  Statements, v1 engine or `GridCO.Proofs.*` directly, and a used-constant
  check backs the rule (the import closure cannot be v1-free). After the
  I9 merge the pure walk lemmas move to `GridCO/Walk/` with only model
  imports; `RecoverySuffix` lemmas get FG-SA wrappers.
- DC Lean is a reference, not a dependency (toolchain v4.34 vs v4.30,
  `using!`, R ≥ 3).
- Process: a plan per phase with an audit; a task review for each task and
  a final branch review; Claude + Astra before big decisions, a full audit
  before major ones; decisions taken without the user are logged. Codex
  always with `-c service_tier="fast"`. Commits by explicit path;
  worktrees under `~/worktrees/`.

## 5. Milestones

```text
┌────┬──────────────────────────────────────┬──────────────────────────┐
│ M  │ Content                              │ Status 2026-09-29        │
├────┼──────────────────────────────────────┼──────────────────────────┤
│ 1  │ I9 derived roots + engine v2 core    │ executing: I9 Task 9;    │
│    │ (2a)                                 │ 2a Tasks 0–5 done        │
│ 1+ │ Post-I9: walk-lemma move and walk    │ agreed; after the I9     │
│    │ anchor; FG-SA spec sync (walk from   │ merge                    │
│    │ F, Pins)                             │                          │
│ 2  │ T7/T1: FG-SA run instance on v2,     │ plan r10 adopted; starts │
│    │ FGSAClaims, registry map             │ after M1                 │
│ 3  │ 1c for FG-SA: run construction and   │ to plan (before 2b/2c)   │
│    │ inhabitation for every horizon       │                          │
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

- Modular spec: can AC and FG be specified against the two channels, with
  healing as the composition theorem? (study running:
  `codex/scratch/modular-spec-study.md`)
- The post-gate cut is not a v2 read (F0 must choose a reader).
- One-repair healing; healing bound tightening (r206 under review).

## 8. Where the detail is

- Research (tip-stability): `state.md`, `log.md`, `spec/`, `blueprint/`,
  `codex/`.
- Lean: `docs/FRAMEWORK-DESIGN.md` (framework), `docs/FG-COMPOSITION.md`
  (FG composition), `docs/MAP.md` (contract to Lean), `docs/audit/`.
- Plans (`docs/plans/`): framework-phase0, phase1a-gate-catalog,
  phase1b-instances, fg-module, fgsa-model-store (all closed);
  i9-derived-roots and phase2a-engine-v2-core (executing);
  fgsa-composition-t7-t1 (r10 adopted; in `~/worktrees/available-chain-fgsa-plan`).
