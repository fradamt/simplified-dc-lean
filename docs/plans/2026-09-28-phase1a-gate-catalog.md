# Phase 1a: Framework Gate and v1 Catalog Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the framework able to carry the full v1 catalog, and fill it. First, one lock-breaking gate: claims over a carrier (facets and engines), late triggers (I2), shared profile constants (g), `depsPresent` in the hooks (h), and a compiled witness of the no-input gap (I1). Then the standard and strong catalog tiers, the profiles `ac-4.3` and `strong-1`, and their proposition equivalences with today's bundles.

**Architecture:** All changes are in `AvailableChainFramework` (L1–L3) and `AvailableChainRegistry` (L4), plus `scripts/CatalogLock.lean` and `scripts/Registry.lean`. A `Carrier` names the kind of instance that a claim speaks about and the type of its run contexts. `ClaimSpec K`, `Cert`, `Refutation` and `Profile K` become generic over the carrier. The v1 carrier is today's `Instance` with an environment and a v1 run. A facet (for example the strong output) is a structure that extends `Instance`, with its own carrier and a carrier map to v1, so base claims and certificates pull back to it. No protocol library (`AvailableChainGridCO`, `…SA`, `…SAPC`, `…LStar`, `…Witnesses`) changes in this plan.

**Tech Stack:** Lean 4 v4.30.0-rc2 and Mathlib v4.30.0-rc2, Lake, the module system (`module`, `public import`, `@[expose] public section`).

**Spec:** `docs/FRAMEWORK-DESIGN.md` v7: §2 E4 (hooks), §3 (instances and facets), §4 (claim catalog, tiers, profiles, the core floor), §5 (certificates, inhabitation, refutations, registry, freeze), §8 (migration, row 1), §12 (known gaps I1, I2). `docs/PHASE0-REPORT.md` §5.1 (deviations (d), (g), (h), (i)) and §6 (open items). Today's bundles: `AvailableChainStatements/Generic/Claims.lean` (`AvailableChain`) and `AvailableChainStatements/Strong/Claims.lean` (`StrongClaims`).

## Scope and the Phase 1–2 split

Design §8 has Phase 1 (full catalog on v1, eligibility per migrated instance, `MATRIX.md`) and Phase 2 (engine v2 and the lift). They are three plans, in this order. Each later plan depends on the shapes that this plan fixes, so it is written after this plan lands.

```text
┌──────┬───────────────────────────────────┬────────────────────────────────────────┐
│ Plan │ Scope                             │ Needs from earlier plans               │
├──────┼───────────────────────────────────┼────────────────────────────────────────┤
│ 1a   │ THIS PLAN. Gate (carrier, I2, g,  │ Phase 0 (done)                         │
│      │ h, I1 witness, lock and registry  │                                        │
│      │ hardening); standard and strong   │                                        │
│      │ tiers; ac-4.3 and strong-1 with   │                                        │
│      │ their equivalences                │                                        │
│ 1b   │ Instance migration: E4 excludes   │ 1a: Carrier.v1, ClaimSpec K, Profile K,│
│      │ for Grid CO, SA, SA-PC (and the   │ HooksSound with deps_stable, ac-4.3,   │
│      │ SA-PC receipt_acceptedRelay       │ strong-1, the equivalence theorems     │
│      │ re-check, which relies on         │                                        │
│      │ excludes = false today);          │                                        │
│      │ HooksSound, EmitWellFormed,       │                                        │
│      │ HandlerCoverage, Deliverable,     │                                        │
│      │ RelayFeasible, WindowMargin;      │                                        │
│      │ Kit.Engine run extension from     │                                        │
│      │ every valid prefix; inhabitation; │                                        │
│      │ Instance values and certificates  │                                        │
│      │ for Grid CO, SA, SA-PC, L*;       │                                        │
│      │ MATRIX.md; the Kit library split  │                                        │
│ 2    │ Engine v2 (E1–E6), the lift       │ 1a: carrier (a v2 carrier is a new     │
│      │ simulation, a toy Linked, self-   │ Carrier value); 1b: Kit.Engine         │
│      │ visible, restart protocol; the I1 │                                        │
│      │ fix (a run-chosen proposer input) │                                        │
│      │ with this plan's I1 witness as    │                                        │
│      │ its regression test               │                                        │
└──────┴───────────────────────────────────┴────────────────────────────────────────┘
```

The FG module is not connected to the search in any of the three plans (user direction 2026-09-28: fix the floor first).

## Rulings in this plan (for the user's review)

- **Carriers replace type-class facets.** Phase 0 deviation (d) made a facet a type class over `Instance`. A claim `∀ I [HasStrong I], …` is vacuous for an instance without the class, and two class instances can attach to one `I` (PHASE0-REPORT §6, Facet row). In this plan a facet is a structure that extends `Instance` (`StrongInstance`), so the facet value is a field and is bound once. A claim that needs the facet is a `ClaimSpec Carrier.strong`: only a `StrongInstance` can hold a certificate of it. A new facet is an addition: a new structure, its carrier and a `CarrierMap` to v1. Existing claims and certificates pull back through the map (G2). Deviation (d) is superseded.
- **The same carrier generalizes the engine (I5).** A claim quantifies over `K.Ctx I W` (for v1: an environment and a v1 run). Engine v2 (plan 2) adds a new carrier value. It does not change `ClaimSpec`.
- **`ProtocolParams` stays inside the protocol.** A protocol value is built from its parameters (`sapc p`), so `Instance` gets no `pparams` field. Profile constants (`Shared`) are the shared constants of design §3–§4 (deviation (g)). If wrong: a later field, which is an addition.
- **`Instance` gets `Δ_pos : 0 < Δ`.** Without it an instance with `Δ ≤ 0` has no admissible context, and every `holds` is vacuous. `Cert.inhabited` already rejects such an instance, but the equivalence theorems (Task 9) need the field.
- **One lock regeneration.** Tasks 1–4 break `docs/catalog.lock` on purpose. Task 6 hardens the lock script and writes the new lock ONCE, with a dated entry in the design's §8 lock change log. Approval of this plan is the user's approval of that regeneration, as for the receipt-relay lock rewrite (`0dd5993`).
- **The I1 gap becomes a compiled witness, not a fix.** Task 5 proves that a protocol that reads no input (`clockChain`) is a `Candidate`. The fix needs engine v2 (plan 2). The witness lives in `AvailableChainRegistry/Gaps/`, and the registry marks its rows `KNOWN-GAP`, not `LEAN`.
- **HooksSound stays run-level** (deviation (i)); `deps_stable` has the same shape as `processed_stable`.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- Committed proofs use no `sorry`, no `admit`, no project axioms and no `native_decide`. A `sorry` is allowed only between a task's statement step and its CHECKPOINT. `lake build --wfail` fails on every `sorry`. `scripts/Registry.lean` rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound` in a certificate row.
- Work on `main` in `lean/available-chain` (user decision 2026-09-28: commit the work frequently). Commit only the task's files, by explicit path, with a message `Framework: <task title>`. Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md`, or any file of `AvailableChainSimplexFG`, `AvailableChainKitFG`, or the FG scripts.
- Do not change `AvailableChainModel`, `AvailableChainStatements`, `AvailableChainGridCO`, `AvailableChainSA`, `AvailableChainSAPC`, `AvailableChainLStar` or `AvailableChainWitnesses`. `AvailableChainRegistry/GridCOHooks.lean` is in the registry and changes in Task 3.
- Layer rule (design §1): `AvailableChainFramework` modules other than `Kit/` import nothing from `AvailableChainRegistry` or `Kit/`. Catalog helper lemmas that a `transport` proof needs go in `AvailableChainFramework/Catalog/Mono.lean` (L3), not in `Kit/`.
- Builds. During the work: `lake build --wfail AvailableChainFramework AvailableChainRegistry`. At the end (Task 10): the full `lake build --wfail`. The Mac `lean` has 3 machine-wide slots: run `pgrep -fl lean` before a build and wait if 3 compiles run. Scripts run with `lake env lean --run <file>`, never through a `lean_exe`.
- Lock and registry during the gate. `lake env lean --run scripts/CatalogLock.lean --check` exits 1 from Task 1 until Task 6. This is expected. From Task 6 on, it must exit 0 at every CHECKPOINT (the hardened script exits 0 on additions only). `lake env lean --run scripts/Registry.lean` must run at every CHECKPOINT from Task 1 on (Task 1 updates it for the new `Cert` arity).
- `Time` is `abbrev Time := Int` in another module. `omega` does not unfold it in this toolchain: use `linarith`, `Int` order lemmas, or an explicit `(x : Int)` cast (PHASE0-REPORT §5.2, Tasks 4 and 9).
- Root imports. A task that creates a `.lean` file adds `public import <module>` for it to its library root (`AvailableChainFramework.lean` or `AvailableChainRegistry.lean`) in the same commit.
- Each task ends at a CHECKPOINT: the build is green; the registry script runs; the lock check has the result that this section states; the task is committed.
- Prose in comments and docs: ASD-STE100 Simplified Technical English. Tables: Unicode box drawing in fenced `text` blocks.
- Claim ids are immutable. A changed statement of an existing claim keeps its id only in this gate (the lock regeneration is the one approved break); after Task 6 a changed statement is a new id.

## Review Focus

1. **An early trigger for every horizon (I2).** Today `inhabited` accepts one trigger at slot 1 for every `H`. After Task 1, `trigger … H` must put the trigger at a time `≥ H`. Test: Task 1, `includedConfirmed_trigger_late`, and the rebuilt Counter certificate uses a slot `≥ H`.
2. **A facet claim that holds vacuously.** A claim that needs the strong output must not hold for an instance that has no strong output, and it must be refutable for an instance whose strong output is bad. Test: Task 4, `badStrong` refutes the test strong-safety claim.
3. **Profile certificates at different constants.** A profile certificate must use one shared constant for all its claims, and cross-claim conditions (`fastArmingLag ≤ armingLag`) must be checked once. Test: Task 2 (`certs` carry `x.const = e.share shared`), Task 9 (`ac43_valid_cross`).
4. **The lock hides a changed claim.** A changed or removed lock line must fail; an added claim must pass with a notice. Test: Task 6, three scratch runs of the hardened `--check`.
5. **An instance with no admissible context.** With `Δ ≤ 0` there is no environment, so every `holds` is vacuous. Test: Task 1 adds `Δ_pos`; Task 9's equivalence theorems use it.

---

### Task 1: Carriers and carrier-generic claims with late triggers

**Files:**
- Create: `AvailableChainFramework/Carrier.lean`
- Modify: `AvailableChainFramework/Instance.lean`, `AvailableChainFramework/Claim.lean`, `AvailableChainFramework/Cert.lean`, `AvailableChainFramework/Pareto.lean`, `AvailableChainFramework/Profile.lean` (only the `ClaimSpec` → `ClaimSpec Carrier.v1` change; Task 2 rewrites it), `AvailableChainFramework/Catalog/Core.lean`, `AvailableChainFramework.lean`
- Modify: `AvailableChainRegistry/Sanity.lean`, `AvailableChainRegistry/Counter.lean`, `AvailableChainRegistry/CounterRun.lean`, `AvailableChainRegistry/CounterIncluded.lean`, `AvailableChainRegistry/Tests/Pareto.lean`, `AvailableChainRegistry/Tests/NewFacet.lean` (delete its content except a module docstring that points to Task 4; Task 4 replaces it)
- Modify: `scripts/Registry.lean` (the `Cert K c I` arity)

**Interfaces:**
- Consumes: Phase 0 framework.
- Produces: `Validators`, `Carrier` (`Inst`, `Ctx`, `admissible`, `horizon`), `V1Ctx`, `Carrier.v1`, `Instance.Δ_pos`, `ClaimSpec K` with `trigger … (H : Time)`, `ClaimSpec.holds`, `ClaimSpec.inhabited`, `Cert c I`, `Refutation c I`, `RefutationFamily c I` for `c : ClaimSpec K`, `I : K.Inst`.

- [ ] **Step 1: Write `Carrier.lean`.** Move `Validators` here from `Instance.lean` (same text).

```lean
module
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Framework

/-- A finite validator type, bundled so that claims can quantify over it. -/
structure Validators where
  V : Type
  dec : DecidableEq V
  fin : Fintype V

attribute [instance] Validators.dec Validators.fin

/-- What a claim speaks about (design §3; carrier generalization, PHASE0-REPORT
§6 I3 and I5): a type of instances and, for each instance and validator type,
a type of run contexts. The v1 carrier has an environment and a v1 run. A
facet or a new engine is a new carrier value, not a change to `ClaimSpec`. -/
structure Carrier where
  Inst : Type 1
  Ctx : Inst → Validators → Type
  /-- The contexts that a certificate covers (v1: the environment has the
  instance's Δ). -/
  admissible : (I : Inst) → (W : Validators) → Ctx I W → Prop
  /-- The last time of the run of a context. -/
  horizon : (I : Inst) → (W : Validators) → Ctx I W → Time

end AvailableChain.Framework

end
```

- [ ] **Step 2: Rewrite `Instance.lean`.** Import `Carrier` and `Hooks`. Keep the `Instance` fields and add `Δ_pos`. Add the v1 context and carrier. `Carrier.v1` is `@[reducible]`, so that `x.E` and `x.rho` elaborate on `x : Carrier.v1.Ctx I W`.

```lean
structure Instance where
  n : Nat
  P : ProtocolSpec n
  /-- Every certified environment has this Δ. -/
  Δ : Time
  Δ_pos : 0 < Δ
  iface : Interface P
  hooks : HooksSound P

/-- A v1 run context: an environment and a run of the instance's protocol. -/
structure V1Ctx (I : Instance) (W : Validators) where
  E : Env W.V
  rho : Run W.V I.P

/-- The v1 carrier: today's instances with an environment and a v1 run. -/
@[reducible] def Carrier.v1 : Carrier where
  Inst := Instance
  Ctx := V1Ctx
  admissible := fun I _ x => x.E.Δ = I.Δ
  horizon := fun _ _ x => x.rho.horizon
```

- [ ] **Step 3: Rewrite `Claim.lean` over a carrier.** Import `Carrier` only. The structure keeps its fields; `regime`, `conclusion` and `trigger` take `(I : K.Inst)` and `(x : K.Ctx I W)`. `trigger` gets a last argument `H : Time`.

```lean
variable {K : Carrier}

structure ClaimSpec (K : Carrier) where
  id : Lean.Name
  Const : Type
  valid : Const → Prop
  le : Const → Const → Bool
  le_refl : ∀ k, le k k = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  Point : Type
  /-- The runs that the claim speaks about. -/
  regime : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Prop
  /-- What the claim states about such a run. -/
  conclusion : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Prop
  /-- `trigger I k W x p H`: the event that makes the claim non-vacuous occurs
  in the run at a time at least `H`, with its deadline inside the run
  (design §5; PHASE0-REPORT §6, I2). -/
  trigger : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Time → Prop
  /-- A weaker constant keeps the claim. A proof, not metadata. -/
  transport : ∀ (I : K.Inst) (k k' : Const), valid k → valid k' → le k k' = true →
    (∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
      regime I k W x p → conclusion I k W x p) →
    (∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
      regime I k' W x p → conclusion I k' W x p)
  refutable : RefutationKind

namespace ClaimSpec

/-- The claim holds for an instance at a constant. -/
def holds (c : ClaimSpec K) (I : K.Inst) (k : c.Const) : Prop :=
  ∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
    c.regime I k W x p → c.conclusion I k W x p

/-- For every time `H`, the regime has an admissible run of the instance with
a horizon of at least `H`, in which the trigger occurs at a time of at least
`H` (design §5; I2). -/
def inhabited (c : ClaimSpec K) (I : K.Inst) (k : c.Const) : Prop :=
  ∀ H : Time, ∃ (W : Validators) (x : K.Ctx I W) (p : c.Point),
    K.admissible I W x ∧ H ≤ K.horizon I W x ∧ c.regime I k W x p ∧
      c.trigger I k W x p H

end ClaimSpec
```

- [ ] **Step 4: Generalize `Cert.lean` and `Pareto.lean`.** Add `variable {K : Carrier}` and write `(c : ClaimSpec K) (I : K.Inst)` in `Cert`, `Refutation`, `RefutationFamily`, `Cert.weaken`, `Cert.not_refuted`, `Refutation.family_of`, and `c : ClaimSpec K` in every Pareto declaration. No other change. In `Profile.lean`, write `claims : List (ClaimSpec Carrier.v1)` and `ProfileCert (p : Profile) (I : Instance)`; Task 2 replaces the file.

- [ ] **Step 5: Rewrite `Catalog/Core.lean` over `Carrier.v1`.** Every claim is `ClaimSpec Carrier.v1`. `sleepy` keeps its signature. In each claim, `regime := fun I _ W x t₀ => sleepy I W x.E x.rho t₀`, and `conclusion` reads `x.E`, `x.rho`. Safety and prefix triggers are `fun _ _ _ _ _ _ => True` (the regime's `H ≤ horizon` carries the time). The inclusion trigger:

```lean
  trigger := fun I D _ x t₀ H =>
    ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
      HonestAwakeProposer x.E x.rho s ∧ I.P.proposalTime s + D ≤ x.rho.horizon
```

Add this lemma after `includedConfirmed`:

```lean
/-- Review Focus 1 (I2): an inhabitation witness of `includedConfirmed` puts
its proposal at a time of at least `H`. -/
theorem includedConfirmed_trigger_late {I : Instance} {D : Time} {H : Time}
    (h : includedConfirmed.inhabited I D) :
    ∃ (W : Validators) (x : Carrier.v1.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  sorry
```

Proof guide: `obtain ⟨W, x, t₀, _, _, _, s, _, hH, hp, _⟩ := h H; exact ⟨W, x, s, hH, hp⟩`.

`core`, `Candidate` and `not_candidate_of_family` keep their Phase 0 form in this task (Task 2 replaces them).

- [ ] **Step 6: Update the registry instances.** `Sanity.sanity` and `Counter.counterInst` add `Δ_pos := by norm_num` (or `zero_lt_one`). Every certificate's `inhabited` proof changes to the new shape `∃ W x p, admissible ∧ H ≤ horizon ∧ regime ∧ trigger … H`, with `x := ⟨E, rho⟩`. Every `proof` field takes `W x hΔ p hreg` and uses `x.E`, `x.rho`.
  - `Counter.certIncluded`: the trigger slot must be at least `H`. Use the canonical run `canonical 0 N` with `N := (max H 2).toNat + 1` and the slot `s := N - 1`; then `H ≤ s`, `0 < s`, and `s + 1 ≤ N`. Replace `horizon_ge` by a lemma that gives these three facts. `Time` rule of the Global Constraints applies.
  - `Sanity.refutedIncluded` and `Sanity.not_candidate`: only the context shape changes.
  - `Tests/Pareto.lean`: `armedToy : ClaimSpec Carrier.v1`, with `trigger := fun _ _ _ _ _ _ => True` (one more argument).
  - `Tests/NewFacet.lean`: remove `HasStrong` and `safeStrong`; keep a module docstring "Replaced by the strong carrier test (Task 4)." and an empty section, so the root import stays valid.

- [ ] **Step 7: Update `scripts/Registry.lean`.** `Cert`, `Refutation` and `RefutationFamily` now have the arguments `K c I`. Read the claim from `args[1]!` and the instance from `args[2]!`. Everything else stays.

- [ ] **Step 8: CHECKPOINT.** `lake build --wfail AvailableChainFramework AvailableChainRegistry` is green. `lake env lean --run scripts/Registry.lean` regenerates `docs/REGISTRY.md` with the same 8 rows, all `LEAN`. `scripts/CatalogLock.lean --check` exits 1 (expected; Task 6 regenerates). Commit with `Framework: carriers, carrier-generic claims, late triggers`, staging the files above and `docs/REGISTRY.md`.

### Task 2: Profiles with shared constants

**Files:**
- Modify: `AvailableChainFramework/Profile.lean`, `AvailableChainFramework/Catalog/Core.lean`, `AvailableChainRegistry/CounterIncluded.lean`, `AvailableChainRegistry/Sanity.lean`

**Interfaces:**
- Consumes: Task 1 (`ClaimSpec K`, `Cert`, `Carrier.v1`).
- Produces: `Profile.Entry K S`, `Profile K` (`id`, `Shared`, `valid`, `entries`), `ProfileCert p I` (a structure: `shared`, `valid`, `certs`), `Profile.holdsAt`, `ProfileCert.holdsAt`, `Catalog.core : Profile Carrier.v1`, `Catalog.Candidate`, `Catalog.not_candidate_of_family`.

- [ ] **Step 1: Rewrite `Profile.lean`.**

```lean
variable {K : Carrier}

/-- One claim of a profile, with the projection of the shared constants to the
claim's own constant (design §4, profiles; PHASE0-REPORT §5.1 (g)). -/
structure Profile.Entry (K : Carrier) (S : Type) where
  spec : ClaimSpec K
  share : S → spec.Const

/-- A named set of catalog claims with shared constants. `valid` holds the
conditions that relate constants of different claims (for `ac-4.3`, all of
`Constants.Valid`). -/
structure Profile (K : Carrier) where
  id : Lean.Name
  Shared : Type
  valid : Shared → Prop
  entries : List (Profile.Entry K Shared)

/-- One certificate per claim of the profile, all for one instance, all at the
projections of ONE shared constant. -/
structure ProfileCert (p : Profile K) (I : K.Inst) : Type 1 where
  shared : p.Shared
  valid : p.valid shared
  certs : ∀ e ∈ p.entries, {x : Cert e.spec I // x.const = e.share shared}

/-- The claims of a profile hold at one shared constant (no inhabitation). -/
def Profile.holdsAt (p : Profile K) (I : K.Inst) (C : p.Shared) : Prop :=
  p.valid C ∧ ∀ e ∈ p.entries, e.spec.valid (e.share C) ∧ e.spec.holds I (e.share C)

theorem ProfileCert.holdsAt {p : Profile K} {I : K.Inst} (pc : ProfileCert p I) :
    p.holdsAt I pc.shared := by
  sorry
```

Proof guide: `refine ⟨pc.valid, fun e he => ?_⟩`; take `⟨x, hx⟩ := pc.certs e he`; rewrite with `hx` in `x.valid` and `x.proof`.

- [ ] **Step 2: Rewrite `core`, `Candidate` and `not_candidate_of_family` in `Catalog/Core.lean`.** The core shares one constant, the inclusion delay `D`.

```lean
/-- The core floor (design §4): every candidate certifies all four claims.
The shared constant is the inclusion delay `D`. -/
def core : Profile Carrier.v1 where
  id := `core.v1
  Shared := Time
  valid := fun D => 0 ≤ D
  entries :=
    [⟨safeConfirmed, fun _ => ()⟩, ⟨safeStable, fun _ => ()⟩,
     ⟨prefixOrder, fun _ => ()⟩, ⟨includedConfirmed, fun D => D⟩]

/-- A candidate protocol passes the core floor. -/
def Candidate (I : Instance) : Type 1 := ProfileCert core I

/-- A refutation family of a core claim rejects the instance. -/
theorem not_candidate_of_family {I : Instance} {e : Profile.Entry Carrier.v1 Time}
    (he : e ∈ core.entries) (r : RefutationFamily e.spec I) : Candidate I → False := by
  sorry
```

Proof guide: `intro pc; exact (pc.certs e he).1.not_refuted r`.

- [ ] **Step 3: Rebuild the registry users.** `Counter.candidate : Candidate counterInst` is a `ProfileCert` with `shared := 1`, `valid := zero_le_one`, and `certs`. The membership `he : e ∈ core.entries` is a `Prop` and cannot be eliminated into data, so use the Phase 0 pattern (PHASE0-REPORT §5.2, Task 9): `classical`, then `if h1 : e = ⟨safeConfirmed, fun _ => ()⟩ then (by subst h1; exact ⟨certSafeConfirmed, rfl⟩) else if …`, and in the last branch derive `e = ⟨includedConfirmed, fun D => D⟩` from `he` and the three negations. `candidate` stays `noncomputable`. `Sanity.not_candidate` uses the entry `⟨includedConfirmed, fun D => D⟩` and `by simp [core]`.

- [ ] **Step 4: Add a Review Focus 3 test** in `CounterIncluded.lean`:

```lean
/-- Review Focus 3: every certificate of Counter's candidate is at the
projection of the one shared delay. -/
example (e : Profile.Entry Carrier.v1 Time) (he : e ∈ core.entries) :
    (candidate.certs e he).1.const = e.share candidate.shared :=
  (candidate.certs e he).2
```

- [ ] **Step 5: CHECKPOINT.** Build green; the registry has 8 rows, all `LEAN` (`ProfileCert` values are not rows until Task 6). Lock `--check` exits 1 (expected). Commit `Framework: profiles with shared constants`.

### Task 3: `depsPresent` in `HooksSound`

**Files:**
- Modify: `AvailableChainFramework/Hooks.lean`, `AvailableChainRegistry/Sanity.lean`, `AvailableChainRegistry/Counter.lean`, `AvailableChainRegistry/GridCOHooks.lean`

**Interfaces:**
- Consumes: Task 1.
- Produces: `HooksSound.deps_stable`.

- [ ] **Step 1: Add the field** after `processed_stable` (PHASE0-REPORT §5.1 (h); design E4: `depsPresent` is monotone within one epoch; v1 has one epoch per run):

```lean
  /-- `depsPresent` is monotone along a run (design E4). -/
  deps_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.depsPresent (Run.stateBefore P rho i v) o = true →
      P.depsPresent (Run.stateBefore P rho j v) o = true
```

- [ ] **Step 2: Prove it for the three protocols.**
  - Sanity (`alwaysGenesis`): `depsPresent = true`; the proof is `fun … h => h` (as `processed_stable`).
  - Counter: `depsPresent st o = decide (o.payload ≤ st + 1)`; use `stateBefore_mono rho hij v` (as `counter_hooks.processed_stable`).
  - `gridCOx`: `depsPresent st o` is `true` for a HEAD and `blockKnown st b.parent` for a proposal. Use `stateBefore_stable` with the predicate `fun st => depsPresent st o = true`, `clock_blocks` for the clock step and `process_blocks_subset` for the process step, as in the proposal case of `processed_stable`.

- [ ] **Step 3: CHECKPOINT.** Build green; registry unchanged. Lock `--check` exits 1 (expected). Commit `Framework: depsPresent in HooksSound`.

### Task 4: Facets as carriers (the strong output)

**Files:**
- Create: `AvailableChainFramework/Facets/Strong.lean`, `AvailableChainFramework/CarrierMap.lean`
- Modify: `AvailableChainFramework.lean`, `AvailableChainRegistry/Tests/NewFacet.lean`

**Interfaces:**
- Consumes: Tasks 1–2.
- Produces: `CarrierMap K' K` (`inst`, `ctx`, `admissible`, `horizon`), `ClaimSpec.pull`, `ClaimSpec.holds_pull`, `ClaimSpec.inhabited_pull`, `Cert.pull`, `StrongInstance` (extends `Instance` with `strong`), `StrongInstance.sface`, `Carrier.strong`, `CarrierMap.strongV1 : CarrierMap Carrier.strong Carrier.v1`.

- [ ] **Step 1: Write `CarrierMap.lean`.** A map from carrier `K'` to carrier `K` sends each `K'` instance to a `K` instance and identifies their contexts. Base claims then pull back.

```lean
variable {K K' : Carrier}

/-- A carrier map from `K'` to `K` (a facet carrier to its base, design G2):
an instance map and an equivalence of contexts that keeps admissibility and
the horizon. -/
structure CarrierMap (K' K : Carrier) where
  inst : K'.Inst → K.Inst
  ctx : ∀ I W, K'.Ctx I W ≃ K.Ctx (inst I) W
  admissible : ∀ I W x, K'.admissible I W x ↔ K.admissible (inst I) W (ctx I W x)
  horizon : ∀ I W x, K'.horizon I W x = K.horizon (inst I) W (ctx I W x)

namespace ClaimSpec

/-- The claim `c` over `K`, read on `K'` through `m`. Same id, constants and
points. -/
def pull (m : CarrierMap K' K) (c : ClaimSpec K) : ClaimSpec K' where
  id := c.id
  Const := c.Const
  valid := c.valid
  le := c.le
  le_refl := c.le_refl
  le_trans := c.le_trans
  Point := c.Point
  regime := fun I k W x p => c.regime (m.inst I) k W (m.ctx I W x) p
  conclusion := fun I k W x p => c.conclusion (m.inst I) k W (m.ctx I W x) p
  trigger := fun I k W x p H => c.trigger (m.inst I) k W (m.ctx I W x) p H
  transport := by sorry
  refutable := c.refutable

theorem holds_pull (m : CarrierMap K' K) (c : ClaimSpec K) (I : K'.Inst) (k : c.Const) :
    (c.pull m).holds I k ↔ c.holds (m.inst I) k := by
  sorry

theorem inhabited_pull (m : CarrierMap K' K) (c : ClaimSpec K) (I : K'.Inst) (k : c.Const) :
    (c.pull m).inhabited I k ↔ c.inhabited (m.inst I) k := by
  sorry

end ClaimSpec

/-- A certificate of the base instance is a certificate of the pulled claim. -/
def Cert.pull (m : CarrierMap K' K) {c : ClaimSpec K} {I : K'.Inst}
    (x : Cert c (m.inst I)) : Cert (c.pull m) I where
  const := x.const
  valid := x.valid
  inhabited := (ClaimSpec.inhabited_pull m c I x.const).2 x.inhabited
  proof := (ClaimSpec.holds_pull m c I x.const).2 x.proof
```

Proof guides: `transport` — from the `k` form on `K'`, get the `k` form on `K` by `(m.ctx I W).symm` (use `Equiv.apply_symm_apply` and `m.admissible`), apply `c.transport`, and come back with `m.ctx I W x`. `holds_pull` — both directions through the equivalence, as for `transport`. `inhabited_pull` — `→`: map the witness context with `m.ctx`, use `m.admissible` and `m.horizon`; `←`: map back with `(m.ctx I W).symm` and rewrite with `Equiv.apply_symm_apply`.

- [ ] **Step 2: Write `Facets/Strong.lean`.**

```lean
/-- An instance with the strong output (`StrongInterface`): the facet is a
field, so it is bound once (design §3). -/
structure StrongInstance extends Instance where
  strong : P.State → Block

/-- The strong interface of a strong instance. -/
def StrongInstance.sface (I : StrongInstance) : StrongInterface I.P :=
  { I.iface with strong := I.strong }

/-- The carrier of strong instances. Its contexts are the v1 contexts of the
base instance. -/
@[reducible] def Carrier.strong : Carrier where
  Inst := StrongInstance
  Ctx := fun I W => V1Ctx I.toInstance W
  admissible := fun I _ x => x.E.Δ = I.Δ
  horizon := fun _ _ x => x.rho.horizon

/-- Base claims pull back to strong instances. -/
def CarrierMap.strongV1 : CarrierMap Carrier.strong Carrier.v1 where
  inst := StrongInstance.toInstance
  ctx := fun _ _ => Equiv.refl _
  admissible := fun _ _ _ => Iff.rfl
  horizon := fun _ _ _ => rfl
```

- [ ] **Step 3: Replace `Tests/NewFacet.lean`** with a test of Review Focus 2 and of the pull. Use Counter.
  - `counterStrong : StrongInstance := { counterInst with strong := counterIface.stable }`.
  - `certSafeStableStrong : Cert (safeStable.pull CarrierMap.strongV1) counterStrong := Cert.pull _ certSafeStable`.
  - A test claim `testStrongSafe : ClaimSpec Carrier.strong` (id `test.strongSafe.v1`, `Const := Unit`, `Point := Time`, regime `sleepy I.toInstance W x.E x.rho t₀`, conclusion `SafeFrom I.P x.rho I.strong t₀`, trigger `True`).
  - `badStrong : StrongInstance := { counterInst with strong := fun st => if st = 1 then Counter.chain 1 else .genesis }`.
  - `refutedBadStrong : RefutationFamily testStrongSafe badStrong`. Proof guide: take the canonical run `canonical 0 2` with `counterEnv 0` and `canonical_sleepy`; at the node `0` the state after time 0 is 1 and after time 1 is 2 (`stateBeforeTime_eq`, `readAt` of the canonical run; Counter delivers the proposal `t + 1` at time `t`), so the strong read is `chain 1` at `t = 0` and `genesis` at `t = 1`; `MonotoneFrom` fails because `chain 1 ⋠ genesis`.
  - A docstring: "Only a `StrongInstance` can hold a certificate of a `ClaimSpec Carrier.strong`. An `Instance` without the strong output has no such claim: the vacuity of `∀ I [HasStrong I], …` (PHASE0-REPORT §6) cannot occur."

- [ ] **Step 4: CHECKPOINT.** Build green. The registry gets one new `refutation-family` row (`refutedBadStrong`, claim `NON-CATALOG`) and one `cert` row (`certSafeStableStrong`), both `LEAN`. Lock `--check` exits 1 (expected). Commit `Framework: facets as carriers`.

### Task 5: The I1 witness (a no-input protocol passes the floor)

**Files:**
- Create: `AvailableChainRegistry/Gaps/NoInput.lean`
- Modify: `AvailableChainRegistry.lean`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: `Gaps.NoInput.clockChain : ProtocolSpec 1`, `clockInst : Instance`, `clockCandidate : Candidate clockInst`.

This task compiles the gap of design §12 (I1). It does not fix it. Plan 2 fixes it (engine v2 gives the proposer a run-chosen input), and then this candidate must fail to elaborate; plan 2 keeps this file as its regression test.

- [ ] **Step 1: Write the protocol.** It reads no delivered object. Its state is the time of its last tick. Its outputs are the chain of all slots up to that time. Its proposal for slot `s` is the block of slot `s`, which every node can compute.

```lean
/-- The block of slot `k` on the clock chain. -/
def clockBlock : Nat → Block
  | 0 => .genesis
  | k + 1 => .node (clockBlock k) (k + 1) ⟨k + 1⟩

/-- A protocol that reads no input (design §12, I1): it excludes every
object, and its outputs depend on the clock only. -/
def clockChain : ProtocolSpec 1 where
  State := Time
  Label := Empty
  Payload := Nat
  init := 0
  clock := fun _ t => t
  actTime := fun ℓ => ℓ.elim
  duties := fun _ => []
  duties_spec := fun ℓ _ => ℓ.elim
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ ℓ => ℓ.elim
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := sorry
  slotsAt_nodup := sorry
  propose := fun _ s => some s
  gossip := fun _ _ => []
  process := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => true
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def clockIface : Interface clockChain where
  confirmed := fun st => clockBlock st.toNat
  stable := fun st => clockBlock st.toNat
  block := fun k => some (clockBlock k)
  opening := fun _ => True
```

Proof guide for `slotsAt_spec` and `slotsAt_nodup`: copy Counter's proofs (`Counter.lean`, same `slotsAt`).

- [ ] **Step 2: Hooks and instance.** `clockHooks : HooksSound clockChain` (every field is immediate: `process` is the identity, `excludes` is always true, `processed` is always false, `depsPresent` is always true). `clockInst` with `n := 1`, `Δ := 1`, `Δ_pos := zero_lt_one`.

- [ ] **Step 3: The four certificates and the candidate.** At `D = 0`.
  - Safety of both outputs: in a run, the state of a node after its events up to `t` is the time of its last tick at or before `t` (or `0`). Every read is `clockBlock m` for some `m`; `clockBlock a ⪯ clockBlock b` when `a ≤ b`, so reads agree; the last-tick time is monotone in `t`.
  - Prefix: the two outputs are equal.
  - Inclusion at `D = 0`: for a slot `s` with `0 < s`, an honest awake proposer ticks at `s` (`tick_total`; `s` is public with `Δ = 1`), emits `⟨.proposer s, s⟩`, and `block s = clockBlock s`. Every honest node ticks at `s`, so its read at `s` is `clockBlock s`.
  - Inhabitation: a one-validator run with a tick at every integer time `0 … N` and no delivery, as `AvailableChainWitnesses/Sanity.lean` (`exampleRun`, `exampleExecution`, `exampleSynchrony`, `exampleRootInjective`, `exampleSleepy`). `PartialSynchrony` holds because `excludes` is always true and nothing is accepted. `RootInjective`: the roots of `clockBlock k` are `⟨k⟩`. For the late inclusion trigger, take the slot `max H 1` (as a natural number) and a horizon of at least that slot.
  - `clockCandidate : Candidate clockInst` with `shared := 0`.

- [ ] **Step 4: Docstring.** The module docstring states: "KNOWN GAP I1 (design §12). This protocol reads no input and still passes the core floor. The floor is too weak until engine v2 gives the proposer a run-chosen input (plan 2). The explorer stays off until then. The registry marks these rows `KNOWN-GAP` (Task 6)."

- [ ] **Step 5: CHECKPOINT.** Build green. The registry now lists `clockChain`'s four certificates as `LEAN` (Task 6 relabels them). Lock `--check` exits 1 (expected). Commit `Framework: compiled witness of gap I1`.

### Task 6: Lock and registry hardening, and the one lock regeneration

**Files:**
- Modify: `scripts/CatalogLock.lean`, `scripts/Registry.lean`, `docs/catalog.lock`, `docs/REGISTRY.md`, `docs/FRAMEWORK-DESIGN.md` (§8 lock change log only)

**Interfaces:**
- Consumes: Tasks 1–5.
- Produces: `CatalogLock --check` by name; `Registry --check`; registry row kinds `profile-cert` and the `KNOWN-GAP` status.

- [ ] **Step 1: Harden `CatalogLock.lean`** (PHASE0-REPORT §6, Lock rows: I8, M5, M6).
  - Lock modules: add `AvailableChainFramework.Carrier`, `AvailableChainFramework.CarrierMap` and the prefix `AvailableChainFramework.Facets` (L2) to the locked set.
  - Generated names: skip a constant whose last name component is `eq_<n>`, `eq_def`, `eq_unfold`, `sizeOf_spec`, `inj`, `injEq`, `mk.inj` or `mk.injEq`, and a constant that `isAuxRecursor` or `isNoConfusion` reports (M6). Its hash still enters the closure of the constants that use it.
  - Missing body: `closureHash` already fails on a missing constant. It must also fail (exit 2) on an `axiomInfo` in the closure that is not `propext`, `Classical.choice` or `Quot.sound` (M5).
  - `--check` compares BY NAME: read the old lines into a map. For each old name: missing now → print `REMOVED <name>`; a different hash → print `CHANGED <name>`. For each new name not in the old file → print `ADDED <name>`. Exit 1 if any `REMOVED` or `CHANGED`; else exit 0 (print the `ADDED` lines as a notice). A malformed lock line → exit 2.
- [ ] **Step 2: Test the hardened check (Review Focus 4)** on scratch copies, not on `docs/catalog.lock`: let the script take an optional `--lock <path>` argument (default `docs/catalog.lock`). Use three copies: (a) one hash changed → exit 1, `CHANGED <name>`; (b) one line deleted → exit 0, `ADDED <name>` (the environment has a name that the lock does not: this is the "new claim" case); (c) one extra line whose name does not exist → exit 1, `REMOVED <name>`. Record the three outputs in the task report.
- [ ] **Step 3: Harden `Registry.lean`** (PHASE0-REPORT §6, Registry rows).
  - Row kinds: add `(``AvailableChain.Framework.ProfileCert, "profile-cert")` (args `K p I`; the claim column shows the profile name) and `(``AvailableChain.Framework.Catalog.Candidate, "profile-cert")` (args `I`; the claim column shows `core.v1`). `Candidate I` is a `def`, so its type head is `Candidate`, not `ProfileCert`. A certificate of a pulled claim (`ClaimSpec.pull m c`) shows the head `ClaimSpec.pull` with `NON-CATALOG`; print the pulled claim `c` in the claim column instead (read `args[1]!.getAppArgs`), with the suffix `(pulled)`.
  - Status: a row from a module under `AvailableChainRegistry.Gaps` gets the status `KNOWN-GAP` (after the axiom check; an `UNSOUND` row stays `UNSOUND`).
  - Libraries: the scan covers every module whose name starts with one of `instanceLibraries : List Name := [`AvailableChainRegistry]`. A later instance library is one list entry (M1). The script prints the list in the REGISTRY.md header.
  - `--check`: compute the text and compare with `docs/REGISTRY.md`; exit 1 if different, 0 if the same. Without an argument, write the file (as now).
- [ ] **Step 4: Regenerate the lock and write the change log.** Run `--write`. Add a dated entry to `docs/FRAMEWORK-DESIGN.md` §8 "Lock change log": the gate of plan 1a (`docs/plans/2026-09-28-phase1a-gate-catalog.md`), approved with the plan; the changed L1–L3 declarations (list the `CHANGED` and `REMOVED` names of a `--check` run against the old lock before `--write`); the new ones (`ADDED`); no certificate conclusion changed; the registry rows after regeneration. Then run `--check`: exit 0.
- [ ] **Step 5: CHECKPOINT.** Build green. `CatalogLock --check` exits 0. `Registry.lean` writes the table with 2 `profile-cert` rows (Counter `candidate`, `clockCandidate` with `KNOWN-GAP`), and `Registry --check` exits 0 after it. Commit `Framework: lock and registry hardening; gate lock regeneration`.

### Task 7: Standard tier claims

**Files:**
- Create: `AvailableChainFramework/Catalog/Mono.lean`, `AvailableChainFramework/Catalog/Standard.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Consumes: Tasks 1, 6.
- Produces: `Catalog.zeroConstants`, the constant records `EtaConst`, `OutageConst`, `RecoveryConst`, and the claims `includedStable`, `includedStableFast`, `persistOutage`, `persistOutageFast`, `recovered` (all `ClaimSpec Carrier.v1`); the Mono lemmas.

The claims restate the fields of `AvailableChain` (`Generic/Claims.lean`) one by one. Each claim's constant is exactly the constants that its regime and conclusion read. The per-parameter directions are those of design §4: the claim is weaker when θ ↑, θrec ↑, η ↑, A ↑, A_f ↑, ρ ↑, recoveryFull false → true, G ↓, Π ↓. Exact-time inclusion delays are fixed (`le` is equality).

- [ ] **Step 1: Write `Mono.lean`** (statements; proofs in Step 3).

```lean
/-- All constants zero, `θ = θrec = 1/2`, `recoveryFull = false`. A claim sets
only the fields that it reads. -/
def zeroConstants : Constants where
  η := 0
  D_c := 0
  D_s := 0
  D_f := 0
  armingLag := 0
  fastArmingLag := 0
  budget := 0
  recoveryBound := 0
  proposerGap := 1
  θ := 1 / 2
  θrec := 1 / 2
  recoveryFull := false

/-- A larger θ or η makes the η-sleepy inequality harder. -/
theorem etaSleepy_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {C C' : Constants} {rho : Run V P} {t : Time}
    (hθ : C.θ ≤ C'.θ) (hη : C.η ≤ C'.η) (hθ0 : 0 ≤ C.θ)
    (h : EtaSleepy E C' rho t) : EtaSleepy E C rho t := by
  sorry

/-- A smaller gap makes the recurrence premise harder. -/
theorem recurrence_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {E : Env V} {I : Interface P} {rho : Run V P} {start g g' : Time}
    (hg : g' ≤ g) (h : HonestProposerRecurrence E I rho start g') :
    HonestProposerRecurrence E I rho start g := by
  sorry

/-- Safety from a later time. -/
theorem safeFrom_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {rho : Run V P} {g : Output P} {t₀ t₁ : Time} (ht : t₀ ≤ t₁)
    (h : SafeFrom P rho g t₀) : SafeFrom P rho g t₁ := by
  sorry

/-- Inclusion from a later time. -/
theorem includedFrom_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {E : Env V} {I : Interface P} {rho : Run V P} {g : Output P} {t₀ t₁ D : Time}
    (ht : t₀ ≤ t₁) (h : IncludedFrom P E I rho g t₀ D) : IncludedFrom P E I rho g t₁ D := by
  sorry
```

Proof guides: `etaSleepy_mono` — `awakeInClosed E H (t − C.η) t ⊆ awakeInClosed E H (t − C'.η) t` (a wider window), so the card of the union with `faulty` grows; then `C.θ * a ≤ C.θ * b ≤ C'.θ * b < …` (`mul_le_mul`, card casts are `≥ 0`). `recurrence_mono` — for `t` with `t + g ≤ horizon`, also `t + g' ≤ horizon`; the slot in `(t, t + g']` is in `(t, t + g]`. The other two restrict the quantifiers.

- [ ] **Step 2: Write `Standard.lean`.** One constant record per regime family.

```lean
structure EtaConst where
  η : Time
  θ : ℚ
  D : Time

structure OutageConst where
  η : Time
  θ : ℚ
  /-- The arming lag (`armingLag`, or `fastArmingLag` for the fast claim). -/
  lag : Time
  /-- Π, the outage budget. (`Π` is a Lean keyword, so the field is `budget`.) -/
  budget : Time

structure RecoveryConst where
  θrec : ℚ
  full : Bool
  G : Time
  ρ : Time
  D_c : Time
  D_s : Time
```

Claims (ids, constants, validity, order, point, regime, conclusion, trigger). `C(k)` is `zeroConstants` with only the listed fields set.

```text
┌────────────────────┬──────────────────────────────┬────────────────────────────────────┐
│ Claim (id)         │ Const, valid, le             │ Point; regime; conclusion; trigger │
├────────────────────┼──────────────────────────────┼────────────────────────────────────┤
│ includedStable     │ EtaConst; 0 ≤ η, 1/2 ≤ θ ≤   │ Time t₀; StableSleepyRegime with   │
│ std.included.      │ 3/4, 0 ≤ D; le: η ≤ η',      │ C(η, θ); IncludedFrom … stable t₀  │
│ stable.v1          │ θ ≤ θ', D = D'               │ D; inclusion trigger (as core)     │
│ includedStableFast │ Time D; 0 ≤ D; le: equality  │ Time t₀; FastRegime; IncludedFrom  │
│ std.included.      │                              │ … stable t₀ D; inclusion trigger   │
│ stableFast.v1      │                              │                                    │
│ persistOutage      │ OutageConst; 0 ≤ η, θ bounds,│ Time × Time × Time (T, b₀, b₁);    │
│ std.persist.       │ 0 ≤ lag, 0 ≤ budget, budget  │ OutageRegime with C(η, θ, lag as   │
│ outage.v1          │ ≤ η; le: η ≤ η', θ ≤ θ',     │ armingLag, budget);                │
│                    │ lag ≤ lag', budget' ≤ budget │ PersistsThrough … stable T b₀ b₁;  │
│                    │                              │ trigger: H ≤ T ∧ some honest read  │
│                    │                              │ of stable at T is not genesis      │
│ persistOutageFast  │ OutageConst (lag is A_f);    │ as persistOutage, with             │
│ std.persist.       │ the same valid and le        │ FastOutageRegime and C(η, θ, lag   │
│ outageFast.v1      │                              │ as fastArmingLag, budget)          │
│ recovered          │ RecoveryConst; θrec bounds,  │ Unit; RecoveryRegime with C(θrec,  │
│ std.recovered.v1   │ 0 < G, 0 ≤ ρ, 0 ≤ D_c,       │ full, G, ρ); RecoveredAt with      │
│                    │ 0 ≤ D_s; le: θrec ≤ θrec',   │ C(D_c, D_s) at E.t_GST + ρ;        │
│                    │ (full → full'), G' ≤ G,      │ trigger: a slot s with GST + ρ <   │
│                    │ ρ ≤ ρ', D_c = D_c', D_s =    │ pt s, H ≤ pt s, honest awake       │
│                    │ D_s'                         │ proposer, pt s + max D_c D_s ≤     │
│                    │                              │ horizon                            │
└────────────────────┴──────────────────────────────┴────────────────────────────────────┘
```

Write each claim as a `def … : ClaimSpec Carrier.v1 where` with all fields, as `includedConfirmed` in `Core.lean`. The `le` field is `decide (…)` of the conjunction in the table. The `le_trans` proof: `of_decide_eq_true` on both, then `decide_eq_true` of the combined facts (`le_trans`, `Eq.trans`, and for `full`: `fun h => hbc (hab h)` on `Bool` implications written as `(k.full = true → k'.full = true)`). `refutable := .family` for the three inclusion-carrying claims (`includedStable`, `includedStableFast`, `recovered`) and `.run` for the two persistence claims.

`recovered`'s `RecoveredAt` reads `C.D_c` and `C.D_s` only, so write its conclusion with `{ zeroConstants with D_c := k.D_c, D_s := k.D_s }`, and its regime with `{ zeroConstants with θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G, recoveryBound := k.ρ }`.

- [ ] **Step 3: Prove the `transport` fields and the Mono lemmas.** For each claim: from `holds` at `k` and a run in the regime at `k'`, show that the run is in the regime at `k` (Mono lemmas: `etaSleepy_mono`; `T + lag ≤ b₀` from `T + lag' ≤ b₀` and `lag ≤ lag'`; `b₁ − b₀ ≤ budget` from `≤ budget'` and `budget' ≤ budget`; `recurrence_mono`; `θrec` as `etaSleepy_mono`; `full`: the premise `k.full = true → …` follows from `k'.full = true → …`; `GST + ρ ≤ horizon` from `GST + ρ' ≤ horizon`), then map the conclusion (equal delays; `RecoveredAt` at `GST + ρ` gives it at `GST + ρ'` by `safeFrom_mono` and `includedFrom_mono`). The `θ` lower bound `0 ≤ θ` comes from `valid k`.

- [ ] **Step 4: Tests.** In `Standard.lean`, `example`s that the `le` of each claim has the design's direction, for example `example : persistOutage.le ⟨0, 1/2, 1, 5⟩ ⟨0, 1/2, 2, 4⟩ = true := by decide` (lag ↑ and budget ↓ are weaker) and its reverse is `false`. If `decide` does not reduce on `ℚ`, use `by simp [persistOutage]; norm_num`.

- [ ] **Step 5: CHECKPOINT.** Build green. `CatalogLock --check` exits 0 with `ADDED` lines only. Run `--write` to record the additions. Registry unchanged. Commit `Framework: standard tier claims`, with `docs/catalog.lock`.

### Task 8: Strong tier claims

**Files:**
- Create: `AvailableChainFramework/Catalog/Strong.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Consumes: Tasks 4, 7.
- Produces: `StrongIncConst`, `StrongRecConst`, `StrongRecIncConst`, and `strongSafe`, `strongIncluded`, `strongPersist`, `strongRecoveredSafe`, `strongRecoveredIncluded` (all `ClaimSpec Carrier.strong`).

These restate the fields of `StrongClaims` (`Strong/Claims.lean`). The fault cap is weaker when it goes down (`faultCap ↓`, design §4). The regimes read `I.sface` and `I.toInstance`.

- [ ] **Step 1: Constants and claims.**

```text
┌─────────────────────────┬─────────────────────────────┬────────────────────────────────┐
│ Claim (id)              │ Const, valid, le            │ Point; regime; conclusion;     │
│                         │                             │ trigger                        │
├─────────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ strongSafe              │ Nat f; True; le: f' ≤ f     │ Time t₀; SleepyRegime ∧        │
│ extra.strong.safe.v1    │                             │ FaultBound f; SafeFrom strong  │
│                         │                             │ t₀; True                       │
│ strongIncluded          │ StrongIncConst (f, D);      │ Time t₀; Sleepy ∧ FaultBound ∧ │
│ extra.strong.           │ 0 ≤ D; le: f' ≤ f, D = D'   │ FullParticipation;             │
│ included.v1             │                             │ IncludedFrom strong t₀ D;      │
│                         │                             │ inclusion trigger              │
│ strongPersist           │ Nat f; True; le: f' ≤ f     │ Time × Time (T, b₀);           │
│ extra.strong.persist.v1 │                             │ StrongArmedRegime f;           │
│                         │                             │ PersistsFrom strong T b₀;      │
│                         │                             │ H ≤ T ∧ a non-genesis honest   │
│                         │                             │ strong read at T               │
│ strongRecoveredSafe     │ StrongRecConst (f, θrec,    │ Unit; RecoveryRegime C(θrec,   │
│ extra.strong.           │ full, G, ρ); valid: True;   │ full, G, ρ) ∧ FaultBound f;    │
│ recoveredSafe.v1        │ le: f' ≤ f,                 │ SafeFrom strong (GST + ρ);     │
│                         │ θrec ≤ θrec', full → full', │ True                           │
│                         │ G' ≤ G, ρ ≤ ρ'              │                                │
│ strongRecoveredIncluded │ StrongRecIncConst (the      │ Unit; as strongRecoveredSafe;  │
│ extra.strong.           │ above and D); also 0 ≤ D;   │ IncludedFrom strong (GST + ρ)  │
│ recoveredIncluded.v1    │ le also D = D'              │ D; inclusion trigger after     │
│                         │                             │ GST + ρ                        │
└─────────────────────────┴─────────────────────────────┴────────────────────────────────┘
```

`StrongClaims` has no `C.Valid` field (only `SC.Valid`), so the recovery constants of the strong claims have NO validity condition (`valid := True`, and `0 ≤ D` for the inclusion claim). Otherwise `strong1_iff` (Task 9) fails for a `C` that is not valid. The `transport` proofs do not need a sign of `θrec`: only the factor changes, and the card term is `≥ 0`. Record this in the file docstring.

- [ ] **Step 2: `transport` proofs**, as Task 7 Step 3; `FaultBound f'` gives `FaultBound f` for `f' ≤ f`.

- [ ] **Step 3: Test.** `refutedBadStrong` of Task 4 used a test claim. Add `refutedBadStrongSafe : RefutationFamily strongSafe badStrong` in `AvailableChainRegistry/Tests/NewFacet.lean`, with the same run (`FaultBound f` holds: no validator is faulty).

- [ ] **Step 4: CHECKPOINT.** Build green. Lock `--check` exits 0 with `ADDED` only; `--write`. Registry: one new `refutation-family` row. `Registry --check` exits 0 after the write. Commit `Framework: strong tier claims`.

### Task 9: Profiles `ac-4.3` and `strong-1`, and the equivalence theorems

**Files:**
- Create: `AvailableChainFramework/Catalog/Profiles.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Consumes: Tasks 2, 7, 8.
- Produces: `ac43 : Profile Carrier.v1` (`Shared := Constants`, `valid := Constants.Valid`), `strong1 : Profile Carrier.strong` (`Shared := Constants × StrongConstants`, `valid := fun C => C.2.Valid`), `ac43_iff`, `strong1_iff`, `ac43_valid_cross`.

- [ ] **Step 1: The profiles.** `ac43.entries`: `safeConfirmed ↦ ()`, `safeStable ↦ ()`, `prefixOrder ↦ ()`, `includedConfirmed ↦ C.D_c`, `includedStable ↦ ⟨C.η, C.θ, C.D_s⟩`, `includedStableFast ↦ C.D_f`, `persistOutage ↦ ⟨C.η, C.θ, C.armingLag, C.budget⟩`, `persistOutageFast ↦ ⟨C.η, C.θ, C.fastArmingLag, C.budget⟩`, `recovered ↦ ⟨C.θrec, C.recoveryFull, C.proposerGap, C.recoveryBound, C.D_c, C.D_s⟩`. `strong1.entries`: the five strong claims with the projections of `(C, SC)` (`SC.faultCap`, `SC.strongDelay`, and the recovery fields of `C`).

- [ ] **Step 2: The equivalence theorems** (design §4: "the equivalence is between claim PROPOSITIONS").

```lean
/-- `ac-4.3` is today's bundle (design §4, profiles). -/
theorem ac43_iff (I : Instance) (C : Constants) :
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → AvailableChain I.P E I.iface C) ↔
      ac43.holdsAt I C := by
  sorry

/-- `strong-1` is today's `StrongClaims`. -/
theorem strong1_iff (I : StrongInstance) (C : Constants) (SC : StrongConstants) :
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → StrongClaims I.P E I.sface C SC) ↔
      strong1.holdsAt I (C, SC) := by
  sorry

/-- Review Focus 3: a cross-claim condition of `ac-4.3` is checked once, by
the profile. -/
theorem ac43_valid_cross (C : Constants) (h : ac43.valid C) :
    C.fastArmingLag ≤ C.armingLag := h.fastArmingLag_le
```

Proof guides: `ac43_iff` `→`: `C.Valid` needs one environment: use `Validators` `Fin 1` and the environment `⟨I.Δ, I.Δ_pos, 0, le_rfl, fun _ _ => true⟩` (this is why `Δ_pos` exists; Review Focus 5); each entry's `valid` follows from `C.Valid`; each `holds` is the bundle field, with the regimes equal by `Iff.rfl` (a regime reads only the fields that the claim's `C(k)` sets; if `Iff.rfl` fails, unfold the regime structure and use `⟨fun h => { h with }, fun h => { h with }⟩`). The bundle's `monotone` field comes from `SafeFrom.monotone` of the two safety claims. `←`: build `AvailableChain` field by field from the entries. Membership in the literal entry list: `by simp [ac43]`. `strong1_iff`: the same, with `SC.Valid` from the profile's `valid`.

- [ ] **Step 3: CHECKPOINT.** Build green. Lock `--check` exits 0 with `ADDED` only; `--write`. Commit `Framework: profiles ac-4.3 and strong-1 with equivalences`.

### Task 10: Documents and handoff

**Files:**
- Modify: `docs/MAP.md`, `docs/FRAMEWORK-DESIGN.md` (§8 row 0 note on (d), (g), (h); §12 I2 closed, I1 compiled), `docs/PHASE0-REPORT.md` (§6: a status column or a closing note per row that this plan closes)

- [ ] **Step 1: MAP.md.** Add rows for `Carrier.lean`, `CarrierMap.lean`, `Facets/Strong.lean`, `Catalog/{Mono,Standard,Strong,Profiles}.lean`, `Registry/Gaps/NoInput.lean`, and the new script modes (`CatalogLock --check` by name and `--lock`, `Registry --check`).
- [ ] **Step 2: Design and report notes.** In FRAMEWORK-DESIGN §8, below the table, add: "(d) superseded by carriers (plan 1a); (g), (h) delivered (plan 1a); (i) kept." In §12: I2 is closed (late triggers, Task 1); I1 is compiled (`Gaps/NoInput.lean`) and stays open until plan 2. In PHASE0-REPORT §6, mark the rows that this plan closes: Facet, Registry (row kind, `--check`, library list), Lock (I8, M5, M6), Core I1 (compiled, open), Claim I2 (closed), Phase 1 gate (done). Leave the rows for plan 1b open (GridCO excludes, model facts, Engine lemmas, Kit structure, E5/E6).
- [ ] **Step 3: Full build at handoff.** `pgrep -fl lean`; then `lake build --wfail` (every default target). `lake env lean --run scripts/CatalogLock.lean --check` exits 0. `lake env lean --run scripts/Registry.lean --check` exits 0. `grep -rn 'sorry' AvailableChainFramework AvailableChainRegistry scripts` finds no tactic use.
- [ ] **Step 4: CHECKPOINT.** Commit `Framework: plan 1a documents`. Write the plan report (controller): tasks, commits, rulings, checks, and the inputs for plan 1b.
