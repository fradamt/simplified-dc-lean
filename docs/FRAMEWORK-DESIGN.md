# Protocol framework — design (v7, 2026-09-28)

_Status: v7 DRAFT. v6 answered the second Astra audit; v7 answers the
third (`docs/audit/framework-v6-audit-report.md`: REVISE, 3 blocking,
6 major, 0 minor; the framework items W01, W02, W04, W06, W08, W09). The exact FG
statements moved to `docs/FG-COMPOSITION.md`, a separate versioned
registry that follows the research. This file fixes the framework and
the FG interface shapes only. The user APPROVED §0–§6 and §9 on
2026-09-28; §7 stays DRAFT until Phase 4._

_History: v0–v2 core design agreed by both sessions. v3–v4 user FG
decisions (fixed Simplex FG, anchors, modular recovery, HavocFG). v5
answers the first Astra audit. v6 answers the second; §11 maps the
findings._

## 0. Purpose and scope

The current repository proves one fixed bundle (`AvailableChain`,
Draft 4.3) per protocol. This design replaces the bundle with a framework
that stays stable while the protocol search changes direction.

```text
┌────┬───────────────────────────────────────────────────────────────────┐
│ G1 │ Protocol-agnostic within the engine scope (below).                │
│ G2 │ Additive evolution: a new assumption, claim, output kind or key   │
│    │ scheme is an addition; existing certificates stay valid.          │
│ G3 │ Partial certification: an instance certifies any subset of the    │
│    │ claims, at any number of parameter points, over one fixed         │
│    │ protocol and facet bundle.                                        │
│ G4 │ Mechanical comparison: checked transports and Pareto sets.        │
│ G5 │ Composition with one fixed, verified FG (our Simplex FG) through   │
│    │ a typed interface.                                                │
│ G6 │ Cheap falsification: executable instances, kernel-checked         │
│    │ refutations.                                                      │
└────┴───────────────────────────────────────────────────────────────────┘
```

Non-goals: probability inside Lean; one generic proof for all
protocols; porting verified-consensus; unbounded ("eventually")
liveness (every catalog claim has a deadline).

**Engine scope.** Engine v2 covers scheduled-duty models: a finite
validator set; labels with a fixed act time and seat count; committees
or the full validator set, with public assignment conditions;
identity-free honest code (no private key or private randomness); one
global time; a static honest set; finite runs; emission only on ticks.

Out of scope by decision (user, 2026-09-28): private VRF
self-selection. Also outside v2, each needing a new engine version with a
lift simulation: clock drift (one logical duty at different local
times); signed replies on receipt; explicit compromise or key erasure;
unbounded liveness.

Additions inside the scope (not covered by existing certificates):
integer stake weights (seat multiplicity, weighted links and quorum
lemmas; the unit-weight FG proofs do not transfer by themselves); fixed
size sampled committees with a Balanced-ε premise; public fixed-size age
buckets; inclusion-list committees; multiple proposers with proposal
identifiers and a selection claim; DAG state in scheduled models (the FG
needs a chain projection); monotone corruption traces with new regimes;
late joiners in a fixed validator set (after E6); protocol-driven relay
with send provenance; signature aggregation with extraction proofs; a
second FG as a new module with its own composition proofs (a gadget whose
private record controls AP proposals needs a new isolation interface).

## 1. Layers

```text
┌────┬──────────────┬───────────────────────────────┬────────────────────┐
│ L  │ Layer        │ Content                       │ Change policy      │
├────┼──────────────┼───────────────────────────────┼────────────────────┤
│ L0 │ Engine       │ events, world, run, emission, │ versioned; content │
│    │              │ restart, own-record step      │ hash frozen        │
│ L1 │ Conditions   │ run predicates; regimes;      │ append-only        │
│    │              │ execution-prefix predicates   │                    │
│ LM │ Modules      │ fixed-component definitions:  │ versioned; content │
│    │              │ Simplex FG, duty frames,      │ hash frozen        │
│    │              │ policy type, AP template      │                    │
│ L2 │ Facets       │ what an instance exposes      │ append-only        │
│ L3 │ Catalog      │ claim specs, transports,      │ append-only;       │
│    │              │ relation lemmas               │ immutable ids      │
│ L4 │ Instances    │ protocol + parameters +       │ free               │
│    │              │ facets; certificates and      │                    │
│    │              │ refutations                   │                    │
│ L5 │ Kits         │ proofs: engine, Goldfish, FG, │ free; never        │
│    │              │ compose                       │ imported by L0–L3  │
│ L6 │ Registry     │ generated matrix; explorer    │ generated          │
└────┴──────────────┴───────────────────────────────┴────────────────────┘
```

L0, L1, LM, L2 and L3 import nothing from L4–L6. LM holds definitions
only. A hole in L1–L3 is fixed by a new versioned entry plus, when
useful, a relation lemma to the old one.

## 2. Engine v2 (L0)

**E1. Duties and keys.** `Auth = seat (ℓ : Label) (i : Fin (seats ℓ)) | none`.
A proposal duty is a one-seat label. `act st ℓ` produces every duty
payload. `ProtocolSpec` has no global `n`.

**E2. Seats and assignment.** `seats : Label → Nat`,
`Run.seatOf ℓ : Fin (seats ℓ) → V`. Committee models are L1 conditions:
`CStar F` (seats = |V| and a proved `Fin (seats ℓ) ≃ V`), `Linked F` (one
fixed bijection for all labels in F), `SingleSeat F`, and later
`Weighted w F`, `Balanced ε F`. Honest code never sees keys. The
protocol declares its AP label family `APLabels` and its FG label family
explicitly (E5).

**E3. Weights** are additions (seat multiplicity plus conditions).

**E4. Delivery outcomes and deliverability (audit V01).**
A delivery of `o` calls the handler; for each `o'` with `handles o o'`,
the protocol classifies the call's effect on `o'` as one of:
- *accepted*: `processed o'` becomes true;
- *permanently rejected*: `excludes o'` holds from then on;
- *temporarily refused*: the state does not change for `o'`, and
  `excludes o'` is false (for example SA-PC's PC before
  `pcEnvelopeReady`; a future-label faulty HEAD).

A refusal that can never end in the current epoch is a PERMANENT
rejection, and the protocol must report it through `excludes` (async
review of v7). Examples: Grid CO's HEAD for label r after slot r+1 (the
clock only goes forward; `Model/Protocol.lean:306`), and a HEAD from a
seat that already has two HEADs at label r (a third equivocation).
Today Grid CO sets `excludes := fun _ _ => false`, so Phase 1 must
define it for these two cases, and for SA and SA-PC too.

The network conditions are about handler calls, as today. Temporary
refusal is allowed and needs no flag. Obligations (`HooksSound P`):
- `excludes` is stable under `clock`, `process` and `recordOwn` within
  an epoch, and implies that `process` leaves the state unchanged.
  `restore` may clear an exclusion that depends on lost receipts (the
  equivocation case), but not a time-based one;
- `processed` and `depsPresent` are monotone WITHIN ONE RESTART EPOCH of
  the node (`processed` may be derived; audit W04);
- `handles o o'` implies `o = o' ∨ carries o o'`.

Feasibility contract (audit W01). `HooksSound` alone does not give
continuation: a protocol can emit a malformed object after one trigger,
and then no synchronous run passes the next broadcast deadline. So every
instance also proves:
- `EmitWellFormed`: every object that an honest node emits satisfies
  `wellFormed`;
- `HandlerCoverage`: a delivery of `o` makes a handler call for `o` and
  for every `o'` with `handles o o'`, as the outcome classification says;
- `Deliverable`: every dependency of an honest emission was ACCEPTED by
  the emitter before the emission (a faulty object is allowed), and the
  emitter's acceptance order is a finite delivery plan;
- `RelayFeasible`: if an honest node accepts `o` at t, then at an honest
  receiver that has accepted `o`'s dependencies, a delivery of `o` before
  t + Δ (after GST, or on a healthy prefix) is accepted or permanently
  rejected (`excludes`), not temporarily refused.

The acceptance-relay regime condition gets the same exemption as the
handler-call relay in `PartialSynchrony`: no obligation for an object
that the receiver excludes at the deadline. Today `AcceptedObjectRelay`
and `HealthyAcceptedObjectRelay` (`Generic/Conditions.lean`) have NO
exemption. So for Grid CO and SA, a faulty HEAD released to one honest
node in the last Δ of its window takes the run out of EVERY regime:
today's certificates do not cover that adversary behavior. This is a
coverage gap in the current contract. Phase 1 fixes the condition and
checks again each SA and SA-PC proof that uses `acceptedRelay` (it may
use acceptance only before the object's exclusion time).

`WindowMargin` (per instance, per object class; async review): the last
cutoff at which a rule reads the object, plus Δ, is at most the
receiver's exclusion time. With it, the exempt relay implies the old
relay at every cutoff that the proofs use. Grid CO/SA: the label-r HEAD
cutoffs are t_r+2Δ, +3Δ, +5Δ and +6Δ (`earlyTime`, `freezeTime`,
`releaseTime`, `gateTime`); the window closes at t_r+8Δ; margin 2Δ ≥ Δ.
An excluded third equivocation is harmless: the late test drops the
seat on two accepted copies. FG rows: check the same margin for the
w_F inclusion window in Phase 4.

`Kit.Engine` proves the run-extension theorem from these four and
`HooksSound`: every valid execution prefix in a regime extends by the
canonical synchronous scheduler to any horizon, with both handler calls
and acceptance relay. This gives continuation from every accepted input,
including inputs that trigger malformed emissions (which the contract
forbids).

Two limits (async review):
- Temporary refusal and synchrony. If the only delivery within Δ is
  temporarily refused, the handler-call premise is met but the object is
  not processed. A proof may assume later processing only if (a) the
  regime includes the optional L1 condition `ReOffer` (the object is
  delivered again within Δ after the first time it is no longer refused,
  after GST), or (b) the protocol buffers the object in its state and
  processes it later, or (c) the object reaches acceptance through the
  relay premise (today's SA-PC). Each instance states which.
- The run-extension theorem guarantees handler calls on the delivery
  plan, not acceptance. A receiver may permanently reject an object that
  the emitter accepted (for example FG admission with a different F,
  possible only at a > f); excluded objects carry no obligation.

These are NEW eligibility obligations. They are proved per migrated
instance; they are not silently added to the v1 hooks (V07, M03).

**E5. Own-signature record.**
- `selfVisible : Label → Bool`, `recordOwn : State → Object → State`.
- `World.step` takes the run context (seat assignment and `awake`).
- Atomic tick: `clock`; every due payload from that post-clock state;
  signing; `recordOwn` folded over self-visible objects in label order,
  then seat order; release.
- Separation: every label in `APLabels`, and every label in a `CStar`
  family, has `selfVisible = false`.
- Isolation laws, with `base : State → B`:
  - `base` after `clock` and `process` is a function of `base` before and
    of the time or object; `recordOwn` does not change `base`;
  - `act` on `APLabels`, all gossip and every output getter factor
    through `base`;
  - restore law: `base (restore d)` depends only on the base-visible part
    of `d` (for an FG composite: F and its basis), never on record-only
    data (audit V11: otherwise a restart could copy a self-visible seat
    index into the base);
  - hook projection: `wellFormed`, `depsPresent`, `processed`,
    `excludes` and `handles` restricted to AP objects factor through
    `base`, so delivery regimes transport between a composite and its AP
    projection.

**E6. Restart.** `Event.restart v t`; order at one time: restart, ticks,
deliveries. Step: `st ↦ restore (durable st)`. For an FG composite,
`durable` = Λ + F + the F basis; h_max and J are derived again from
received chain states. Each restart starts a new EPOCH of the node. Receipt facts (`processed`,
`depsPresent`) reset with the epoch (audit W04): a block outside the
durable part is lost, and it can be delivered again (the freshness check
allows it). Delivery obligations toward a restarted node cover objects
re-offered after its rejoin; regimes with restarts add a rejoin
condition (state transfer or re-offer of the needed objects).
Output monotonicity and inclusion compare reads of one node only within
one epoch; a separate optional entry `catchUp` states that a rejoined
node reaches its last exposed output within a bound (V11). Existing
regimes add `NoRestart`.

**Lift (v1 → v2).** A simulation, not only equal reads: disjoint label
sum; `proposer s` ↦ seat 0 of `prop s`; `proposerOf s` = that seat's
holder; old committee bijections from `CStar`'s proved equivalence (with
the dependent `Fin` casts); old duty and proposal order preserved; no
self-visible labels, `NoRestart`, trivial `durable`. Every v2 run in the
lifted legacy regime has a corresponding v1 run. The lift transports
claim PROPOSITIONS; certificate eligibility (E4, §5) is proved
separately per instance. Estimate: several engineer-weeks (audit).

## 3. Instances and facets (L2, L4)

```lean
structure Instance where
  P       : ProtocolSpec
  pparams : ProtocolParams      -- k, L, τ, q, Δ, …: fixed protocol identity
  facets  : FacetBundle P       -- every exposed facet, once
  hooks   : HooksSound P
  deliv   : Deliverable P
  iso     : RecordIsolated P
```

Protocol parameters and facets are bound once. Claim constants are NOT
in the instance; they belong to certificates (§5). So one instance can
hold several certified tradeoff points of one claim (for example SA's P1
with (A, Π) and fast P1 with (A_f, Π); SA-PC recovery at h > a and at
a ≤ f with different ρ).

Facets: `ChainOutputs`, `Proposals` (labels, times, proposal identifier,
`block`, `opening`), `Protected`, `Base`, `Durable`, and the FG facets
of §7. Every output getter reads only `base`. Claims are schemas over
output names. Phase 0 selects an extensible representation for
`FacetBundle`, `FacetNeeds`, `ProtocolParams` and constant records
(typed maps or separate facet records), because adding a field to a
frozen Lean structure changes its declaration.

## 4. Claim catalog (L3)

```lean
structure ClaimSpec where
  id        : Lean.Name
  needs     : FacetNeeds
  Const     : Type                           -- this claim's constants
  valid     : Const → Prop
  le        : Const → Const → Bool           -- decidable; `le c c'`: c' is
                                             -- at least as weak as c
  le_refl   : ∀ c, le c c
  le_trans  : ∀ a b c, le a b → le b c → le a c
  holds     : Instance → Const → Prop
  transport : ∀ I c c', valid c → valid c' → le c c' →
                holds I c → holds I c'
  trigger   : Instance → Const → Run → Prop  -- the claim's trigger occurs
                                             -- with its deadline in the run
  inhabited : Instance → Const → Prop        -- §5
  refutable : RefutationKind
```

- Per-parameter behaviour (audit tables): the claim is weaker when θ ↑,
  θrec ↑, η ↑, A ↑, A_f ↑, ρ ↑, recoveryFull false → true, G ↓, Π ↓,
  faultCap ↓, and D ↑ for persistent inclusion. Exact-time inclusion is
  `fixed` in D: its `le` is equality on D.
- `transport` is a proof, not metadata. Composite comparisons compose
  transports; `le_refl` and `le_trans` make that sound.
- Relation lemmas may combine certificates of ONE instance and require
  equal values for their shared constants. Example:
  `Safe o ∧ included o D ⇒ includedPersist o D` (same D). `Safe o` is one
  conjunction: agreement and per-node monotonicity, as today's `SafeFrom`.
- `includedPersist o D` (B is in every honest read of `o` at every time
  from `s + D` to the horizon) is a DERIVED lemma in `Kit.Core`, not a
  catalog entry: every instance is safe (core floor), so it follows from
  `Safe o` and `included o D` (user decision 2026-09-28).
- Regimes with a minimum horizon (Outage b₁, Recovery GST + ρ, StrongArmed
  b₀) are closed under complete time truncation only above it. Causal
  arguments use separate EXECUTION-PREFIX predicates (L1), not the
  complete-run regimes; an event-list prefix inside one time can break
  `tick_total`.

**Profiles.** A profile is a set of catalog ids plus shared constant
names. A profile certificate is a set of certificates of one instance
that agree on the shared constants. `ac-4.3` is today's bundle: the
equivalence is between claim PROPOSITIONS (`AvailableChain ↔` the
conjunction of the `ac-4.3` `holds`). Eligibility (hooks,
deliverability, inhabitation) is separate, because `AvailableChain`
contains none of it (V07). `strong-1` is `StrongClaims`.

Tiers:

```text
┌──────────────┬───────────────────────────────────────────────────────┐
│ Tier         │ Entries                                               │
├──────────────┼───────────────────────────────────────────────────────┤
│ core (floor) │ Safe(confirmed), Safe(stable), prefix(stable ⪯        │
│              │ confirmed), included(confirmed) under Sleepy          │
│ standard     │ included(stable) under StableSleepy, fast             │
│              │ inclusion, persistence (general, fast), recovered     │
│              │ variants                                              │
│ extra        │ strong claims; base exports; P1 from a recovered      │
│              │ handoff; noFutureRead; catchUp; later additions       │
│ fg-ready     │ AP-side FG entries (FG-COMPOSITION.md)                │
│ composite    │ derived by Kit.Compose (FG-COMPOSITION.md)            │
└──────────────┴───────────────────────────────────────────────────────┘
```

The core is a FLOOR (user decision 2026-09-28): an instance is a
candidate protocol only if it certifies every core claim. A refutation
of a core claim rejects the instance. Selection of claims ("all but
one", optional extras) applies only above the core. The explorer and
the Pareto comparison consider only instances that pass the floor.
Unsafe or not-live protocols are out of scope.

## 5. Certificates, refutations, registry (L4, L6)

```lean
structure Cert (c : ClaimSpec) (I : Instance) where
  const     : c.Const
  valid     : c.valid const
  inhabited : c.inhabited I const
  proof     : c.holds I const

structure Refutation (c : ClaimSpec) (I : Instance) where
  const     : c.Const
  valid     : c.valid const
  proof     : ¬ c.holds I const
```

**Inhabitation (V07).** `inhabited I c`: for every horizon H there is a
run of I in the claim's regime, with horizon ≥ H, in which the claim's
TRIGGER occurs with its deadline inside the run: for inclusion, an
honest awake proposer slot; for persistence, a non-genesis armed read;
for FG entries, a nonempty source. Boundary cases are allowed (no fault
when the regime forbids one). `Kit.Engine` supplies the runs through the
run-extension theorem (E4). Transport of `holds` does not transport
`inhabited`.

**Refutations.** Finite runs for bounded claims; parameterized finite
families for "no constant works" (as the Sanity theorem does for every
D). Kernel checking with `decide_cbv` or a reflective checker whose
soundness covers the execution, the regime and the failed conclusion;
`native_decide` is not allowed. Executable checkers exist only for
instances with finite representations and equivalence proofs.

**Registry.** Checked attributes (`@[cert]`, `@[refutes]`) verify the
elaborated type, including instance and constants; a theorem with extra
unproved premises is not a certificate. Per instance and claim the
registry keeps the Pareto set of proved constants, the refuted
constants, the proof status (Lean certificate, paper, conditional),
assumptions, output names and module versions. A paper result never
appears as a Lean certificate.

**Freeze.** `catalog.lock`: per L1, LM, L2, L3 declaration, a
deterministic hash of the transitive dependency closure (types, bodies,
inductives, opaque bodies via `getUsedConstantsAsSet`; fail if a body is
unavailable). Per L0 and LM version, a frozen content hash. The
toolchain and Lake manifest are pinned. Each certificate records its
instance, constants and dependency hashes. The freeze is syntactic; it
does not replace kernel checking.

## 6. Kits and explorer (L5, L6)

- `Kit.Engine`: honest origin; transfer within Δ after GST and on a
  healthy prefix; relay closure; clean start; the run-extension theorem
  and inhabitation (E4, §5).
- `Kit.Goldfish`: the substrate of Grid CO, SA, SA-PC and L*. Optional.
- `Kit.FG`, `Kit.Compose`: see §7 and FG-COMPOSITION.md.
- Explorer: executable instances; regime and conclusion checkers;
  refutation files.

## 7. FG composition: interface shapes

The exact FG statements, their proof status and their sources are in
`docs/FG-COMPOSITION.md`. Each registry entry PINS its statement (full
text and hypotheses, copied), its module variant, and the SHA-256 of the
source file at registration (audit W08). A changed statement is a new
id; a proof-status change is a separate, dated status line. The entries
enter the catalog as versioned ids. This section fixes only the shapes that the
framework must support.

**7.1 Decisions (user).** The FG is our Simplex FG, as a small family of
VERSIONED MODULE VARIANTS, each fixed: `SimplexFG.nj` (DC's NJ rule) and
`SimplexFG.fj` (the PRIMARY variant: the user adopted FJ for FG-SA on
2026-09-28, with NJ as the alternative; the FJ root rule: a frontier test, root F and
band {H} in a contest). FJ changes the frame rule, so it is a module
variant with its own frame and noninterference interface, not a
base-selection plug-in (audit W06). The FJ interface is r148 F9 (the
sources of honest rows at heights ≥ M+1 stay canonical), with the
descent/reset lemma, F10 and F12; it is not HNI. APs vary. FG heights never skip. Every
height pair (target or timeout) needs the AP's source; with none, the
pair is empty. FG interference is relative to a height m. Fallback: an AP
that cannot meet the AP-side entries is certified white-box.

**7.2 Duty frame (LM; audit V09).** `frameOf : View → Frame` returns the
duty frame (F_d, Z_d, H_d, (j_d, J_d), D_d) and the view V_d, with
D_d = {B ∈ V_d : F_d ⪯ B, Z_d ⪯ B, ∃ W ∈ V_d, B ⪯ W ∧ h(W) ≥ H_d − 1}
and Z_d = J_d if H_d = j_d + 1, else F_d. The view is the duty's frozen
view closed under the F basis. This is the R1 VARIANT of DC: DC reads
live control caches; R1 reads the duty view. Two correspondence theorems
(versioned, in `Kit.FG`) relate the frame to the R1 variant of DC's
viable tree and to its filtered tree, separately (the root covers the
prefix up to Z_d). `anchors` (the entries at H_d − 1 in D_d) are a derived
view of the frame; the AP may pick among them with its `AnchorChoice`.

**7.3 AP template and policy type (LM; audit V10).**
- `Policy`: the type of honest FG signing rules. A policy reads the FG
  sub-state, the record, and the AP facets through `base`; it emits
  objects only on the FG label family (`Linked`); it writes only the
  record. The AP transitions are fixed.
- `APTemplate`: an AP spec with a policy slot. `inst T σ : Instance` is
  the composite for policy σ.
- An AP-side certificate is a FAMILY certificate (audit W02):
  `FamilyCert c T := { const, valid, proof : ∀ σ : Policy, c.holds (inst T σ) const,
  inhabited : c.inhabited (inst T simplex) const }`. The proof is uniform
  over σ; the witness is required only for the Simplex policy.
- Family entries state only AP SERVICE facts: repair within ρ, production
  of a common source, carrier and row service, source safety. They never
  state FG progress (a height rise): an arbitrary policy can withhold all
  progress rows. So (L) splits: its service part (repair by u+ρ, a
  common fresh source, row folding, carrier retention) stays in `ap.*`
  entries, and the rise moves to `comp.rise.*` entries. Height progress, and every Simplex law (provenance,
  quorum uniqueness, causal cap, no slashing), are derived in
  `Kit.Compose` after specialization to the Simplex policy.

**7.4 Composition (`Kit.Compose`).** It combines AP-side certificate
families, specialized to the Simplex policy, with `Kit.FG` lemmas, in
the causal induction over execution prefixes, with separate invariants
for clean history, post-reset source history (per-body first-transfer
time), and armed-prefix Outage history (V03). Base selection returns a
witness record, not a bare condition (audit W09): the causal cut M, a
height x > M, the first honest row above x after the cut with its
first-transfer view facts, and the arm witness (the NJ prefix record
facts, the actual finalized checkpoint F*, or the FJ facts of its
variant). Run-wide HNI is DERIVED inside the joint induction, not taken
as an input. Its outputs are the
composite entries of FG-COMPOSITION.md (`comp.fgHealed`, `comp.healed`,
and finality entries that stay conditional until their timed
obligations are proved).

## 8. Migration (phases)

```text
┌───┬───────────────────────────┬─────────────────────────────────────────┐
│ P │ Work                      │ Acceptance                              │
├───┼───────────────────────────┼─────────────────────────────────────────┤
│ 0 │ Compiled prototype on v1: │ Instance, ClaimSpec with transport and  │
│   │ interfaces, extensible    │ trigger, Cert, profiles, checked        │
│   │ facet/constant records,   │ attributes, a Pareto comparison,        │
│   │ two claims, Sanity, a toy │ catalog.lock; Safe and included         │
│   │ E4 classification, a toy  │ certified or refuted for Sanity; E4 and │
│   │ E5/E6 step, the           │ Deliverable checked for Grid CO; the    │
│   │ run-extension theorem     │ run-extension theorem for a toy spec    │
│ 1 │ Full catalog on v1        │ ac-4.3 and strong-1 proposition         │
│   │                           │ equivalences; eligibility per migrated  │
│   │                           │ instance; MATRIX.md; build --wfail      │
│ 2 │ Engine v2 + lift          │ v1 propositions transported; a toy      │
│   │                           │ Linked, self-visible, restart protocol  │
│ 3 │ Kits, explorer, checker   │ r107, Sanity, Accumulation, CE-1        │
│   │                           │ rediscovered                            │
│ 4 │ LM Simplex FG, frames,    │ correspondence theorems; FG-COMPOSITION │
│   │ policy, template; Kit.FG; │ entries at the status the research has  │
│   │ Kit.Compose; FG-SA        │ reached                                 │
└───┴───────────────────────────┴─────────────────────────────────────────┘
```

Phases 0–2 land before the FG-SA Lean instance starts.

## 9. Changes to standing rules (approved by the user 2026-09-28)

- `AGENTS.md`: "Keep [the engine] close to that source" becomes "Engine
  v2 is the reference; changes need a lift simulation".
- `CONTRACT.md`: "one bundle every instance proves" becomes "catalog,
  instances and profiles"; Draft 4.3 stays as profile `ac-4.3`.

## 10. Open items

- Recommendation: stop paper audits here and let Phase 0 test the
  interfaces with the Lean compiler (the audits' own recommendation). The
  FG interface shapes (§7) stay DRAFT until Phase 4; the core (§0–§6)
  is ready for approval.

- User decisions (2026-09-28): core §0–§6 APPROVED; §9 rule changes
  APPROVED; core tier = floor of safety + confirmed inclusion (§4).
- FG research (tracked in FG-COMPOSITION.md): r149 (strengthened (S),
  (S_slow), (L), (X)); r148 (FJ root rule); "ρ once globally"; full
  healing at q_s*; the timed finality obligations.

## 11. Audit disposition

```text
┌──────┬──────────────────────────────────────────────┬──────────────────┐
│ ID   │ Fix                                          │ Where            │
├──────┼──────────────────────────────────────────────┼──────────────────┤
│ v4 B01, V08 │ protocol params and facets per       │ §3, §4, §5       │
│      │ instance; constants per certificate; Pareto  │                  │
│ v4 B02 │ exact inclusion fixed in D; persistent     │ §4               │
│      │ inclusion; Safe-premised relation lemma      │                  │
│ v4 B03, V01, V07 │ delivery outcomes; accepted-     │ E4, §5           │
│      │ dependency deliverability; run extension;    │                  │
│      │ trigger witnesses; propositions vs           │                  │
│      │ eligibility                                  │                  │
│ v4 B04–B06, V02–V06 │ exact FG statements moved to  │ §7,              │
│      │ FG-COMPOSITION.md (r147 N1/N2/Ret, HNI(m),   │ FG-COMPOSITION   │
│      │ body-level (S), separate invariants, row     │                  │
│      │ service, carrier keep, conditional finality) │                  │
│ V09  │ duty frame with Z; viable and filtered       │ §7.2             │
│      │ correspondences; R1 variant named            │                  │
│ V10  │ policy type, AP template, certificate        │ §7.3             │
│      │ families, specialization rule                │                  │
│ V11, v4 M02 │ restore law, hook projection, AP     │ E5, E6           │
│      │ label family, epochs, fold order             │                  │
│ V12, v4 N01 │ status moved to FG-COMPOSITION.md;   │ §10, FG-COMP.    │
│      │ exact versioned statements, no shorthand     │                  │
│ v4 M01, M03, M07, M08, M09, N02 │ fixed in v5      │ —                │
└──────┴──────────────────────────────────────────────┴──────────────────┘
```

## 12. What certificates do not cover

Validity of execution data; data availability or possession; conformance
of a deployed client (implementation refinement). These need their own
entries or a separate refinement project. `noFutureRead` is an
extra-tier entry.
