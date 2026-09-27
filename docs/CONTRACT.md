# available-chain — contract draft

_Draft 4.2 (2026-09-27), committee model C*. Purpose: a small Lean repo
whose engine and claims are fixed, so that any suitable protocol can be an instance if it proves the
claims. Source of the engine: verified-consensus
`DecoupledConsensusModel/Generic` (Env, ProtocolSpec, Run) and
`DecoupledConsensusStatements/Generic`._

## 1. Decisions

```text
┌────────────────────────┬─────────────────────────────────────────────────┐
│ Topic                  │ Decision                                        │
├────────────────────────┼─────────────────────────────────────────────────┤
│ Sleep                  │ Asleep nodes receive and process, but do not    │
│                        │ tick (no emission). Join rule = "listen for a   │
│                        │ while"; no state transfer is modelled.          │
│ Committees             │ Model C* (mean-field seats): every label has a  │
│                        │ committee of all n seats; the run assigns seats │
│                        │ to validators by a fresh hidden bijection per   │
│                        │ label. Claims hold for every assignment. This   │
│                        │ is the exact form of "perfectly representative" │
│                        │ (no sampling error). See §2a.                   │
│ Weights                │ Unit seats: every validator has weight 1.       │
│ Corruption             │ Static: the faulty set is fixed for the run and │
│                        │ its size is the regime's threshold. No adaptive │
│                        │ corruption.                                     │
│ Scope                  │ Outputs stable and confirmed only. No FG, no SG.│
│ Genericity             │ Generic engine and outputs. Slots, proposers,   │
│                        │ proposal times, duty labels and blocks stay in  │
│                        │ the model (not 100% generic, by choice).        │
│ Liveness               │ Through honest-proposal inclusion, as in        │
│                        │ verified-consensus.                             │
│ Sleepy start           │ GST = 0 and t₀ = 0. A later GST needs recovery. │
│ Recovery              │ An instance sets θrec and recoveryFull.         │
└────────────────────────┴─────────────────────────────────────────────────┘
```

## 2. Engine (fixed)

- **Env:** Δ, t_GST, `awake : V → Time → Bool`. No weights (unit seats).
- **ProtocolSpec n:** `State`, `Label`, `Payload`, `init`, `clock`,
  `actTime`, `duties`, `act`, `proposalTime`, `slotsAt`, `propose`,
  `gossip`, `process`, and the delivery hooks (`wellFormed`, `depsPresent`,
  `processed`, `excludes`, `handles`, `carries`). Wire objects are
  `Signed Label n Payload` (authentication and payload). The type does not
  mention validators.
- **Run:** honest set (static corruption), horizon, event list (ticks,
  deliveries), `seatOf : Label → Fin n ≃ V`, `proposerOf : Slot → V`.
- **Step:** a tick runs `clock`; a delivery runs `process`. Emission never
  changes the state. At a tick, an awake node emits: for each label due now,
  `act st ℓ` signed with its seat of ℓ; for each of its slots due now,
  `propose st s` signed with `proposer s`; and unsigned `gossip st t`. An
  asleep node emits nothing but still receives, processes, and runs its
  clock.
- **Signatures:** an object held by an honest seat or proposer was emitted
  by it. Faulty seats and proposers sign anything at any time.
- **Delivery:** arbitrary before GST; after GST every honest emission
  reaches every honest node in less than Δ. Accepted objects also reach
  acceptance at every honest reader within Δ when the deadline is in the
  run. A healthy outage prefix has the same acceptance guarantee before b₀.

## 2a. Committee model C* (rules)

```text
┌────┬────────────────────────────────────────────┬───────────────────────┐
│ K  │ Rule                                       │ Where                 │
├────┼────────────────────────────────────────────┼───────────────────────┤
│ K1 │ Seat authentication per label, with a      │ Auth, Run.seatOf      │
│    │ fresh run-chosen bijection per label       │                       │
│ K2 │ No identity in honest code: no V, one      │ ProtocolSpec n        │
│    │ init, no keys; the engine signs            │                       │
│ K3 │ Emission never changes state; own objects  │ World.step            │
│    │ return only by delivery                    │                       │
│ K4 │ Unit seats                                 │ Env (no weights)      │
│ K5 │ Honest seat signs once, at actTime ℓ, if   │ duties_spec,          │
│    │ awake; faulty seats unconstrained          │ Run.emittedAt         │
│ K6 │ Committee = all n seats (absolute vs       │ Run.seatOf            │
│    │ relative thresholds use awake)             │                       │
│ K7 │ Implementation obligation: a fresh private │ not checkable in Lean │
│    │ VRF per label; a seat signs at one instant │                       │
│    │ only. Bundle same-instant duties in one    │                       │
│    │ label, or use separate labels.             │                       │
│ K8 │ Witnesses with faults, a sleeper, and two  │ Witnesses             │
│    │ distinct honest views; the accumulation    │                       │
│    │ attack must be a valid run                 │                       │
│ K9 │ Optional slack ε (finite committees)       │ later                 │
│ K10│ Disclosures: no corruption of revealed     │ this document         │
│    │ committees; joiners receive full history   │                       │
└────┴────────────────────────────────────────────┴───────────────────────┘
```

Why RLMD-GHOST is not an instance: no signature links votes of different
labels, so "latest message per validator" cannot be written. Links in
payloads are unauthenticated and faulty seats can forge them. K3 removes the
one gap of C* against real committees: a node cannot learn or use its own
seats, so it uses only what an unsampled node can compute.

## 3. Interface (what an instance exposes)

- `confirmed, stable : P.State → Block`;
- `block : P.Payload → Option Block` (the block a proposal proposes);
- `opening : Slot → Prop` for the recurrence premise.

The proposal schedule is in the protocol (`proposalTime`, `slotsAt`); the
proposer is run data. `Block` has no proposer identity. Removed: `committee`,
`proposer`, `proposedBlock`, `finalized`, and all certificate, evidence and
slashing fields.

## 4. Regimes (fixed menu; instances cannot add premises)

Notation at time t: H_t = honest validators awake at t; H_[t−η,t] = honest
validators awake at some time in [t−η, t]; A = faulty validators (static,
always counted). Weights are counts (unit seats). Under C* every committee
has the fractions of the whole set, so the premises are stated on the whole
set.

All regimes require `RootInjective E I rho`. This is the collision-resistance
premise for block roots. Its scope contains genesis and every ancestor
(including the tip itself) of a block returned by `I.block` on a delivered
or emitted payload. Within this scope, equal roots imply equal blocks.
Sleepy, Outage, and Recovery use the same predicate. StableSleepy and Fast
inherit it from Sleepy. This does not restrict the raw `Block` datatype.

Outage participation premises hold at every `0 ≤ t < b₀`, including
times before the protected read `T`. The healthy prefix starts at genesis.

**η-sleepy condition with threshold θ** (TSQ type, decision A):

    w(H_t)  >  θ · w(H_[t−η,t] ∪ A)        for every t in the regime

- θ = 1/2 gives w(H_t) > w(A) + w(dropped), where dropped = H_[t−η,t] \ H_t:
  the honest validators awake now outweigh the faulty ones plus the honest
  ones that went to sleep in the last η (the FreshMajority shape).
- The instance declares θ in [1/2, 3/4]. θ = 1/2 gives the strongest
  instance claim: its threshold premise holds for the most runs. η is an
  instance parameter. The contract requires Π ≤ η.

```text
┌──────────────┬───────────────────────────────────────────────────────────┐
│ Regime       │ Premise                                                   │
├──────────────┼───────────────────────────────────────────────────────────┤
│ Sleepy       │ GST = t₀ = 0, synchrony and accepted-object relay;        │
│              │ at every t, w(H_t) > w(A)                                 │
│ StableSleepy │ Sleepy, and the η-sleepy condition with threshold θ       │
│ (θ, η)       │ (for the stable claims)                                   │
│ Fast         │ Sleepy with full honest participation and w(A) < W/4      │
│              │ (honest > 3/4). Decided by the user.                      │
│ Outage       │ StableSleepy(θ, η) counts before b₀; healthy delivery    │
│              │ and accepted relay before b₀; arbitrary delivery in       │
│              │ [b₀, b₁)                                                  │
│ Recovery     │ arbitrary before GST; after GST, θrec·(h_t+a)<h_t;       │
│              │ full participation if recoveryFull; honest awake         │
│              │ opening proposer every G                                  │
└──────────────┴───────────────────────────────────────────────────────────┘
```

## 5. Claims (the bundle every instance proves)

```text
┌────────────────────┬──────────┬──────────────────────────────────────────┐
│ Claim              │ Regime   │ Conclusion                               │
├────────────────────┼──────────┼──────────────────────────────────────────┤
│ confirmedSafe      │ Sleepy   │ honest confirmed reads are compatible    │
│ stableSafe         │ Sleepy*  │ honest stable reads are compatible       │
│ monotone           │ Sleepy   │ no honest read of either output retreats │
│ nested             │ always   │ stable ⪯ confirmed at every honest read  │
│ confirmedIncluded  │ Sleepy   │ an honest proposer awake at slot s       │
│                    │          │ proposes, and its block is in every      │
│                    │          │ honest confirmed read by                 │
│                    │          │ proposalTime s + D_c                     │
│ stableIncluded     │ StableS. │ same for stable, by + D_s                │
│ stableIncludedFast │ Fast     │ same, by + D_f (target: small)           │
│ stableResilient    │ Outage   │ a stable read at T persists through      │
│                    │          │ [b₀, b₁) if b₀ ≥ T + A and b₁ − b₀ ≤ Π  │
│ recovered          │ Recovery │ the Sleepy claims hold from GST + ρ      │
└────────────────────┴──────────┴──────────────────────────────────────────┘
```

`Sleepy*` means the plain Sleepy regime for safety. The stable inclusion
claim uses StableSleepy(θ, η).

`ExecutionValid` implies that every event has nonnegative time. Thus each
state before time zero is `P.init`. Sleepy needs no separate clean-start
field. An outage can start after a healthy prefix. Recovery can start from
an arbitrary reachable state before GST.

`nested` is cheap (an accessor can enforce it); its value is only with the
two safety claims.

## 6. Constants (the instance's output)

θ and θrec in [1/2, 3/4], recoveryFull, η, D_c, D_s, D_f, arming lag A,
budget Π ≤ η, recovery bound ρ, and
the Recovery premise parameter G (gap between honest awake opening
proposers; ρ may depend on G). All in units of Δ and regime parameters; none may depend on the run.
Protocols are compared by these constants.

## 7. Non-vacuity

- A witness execution for each regime (in `AvailableChainWitnesses`).
- An accepted-object witness with an active cross-reader relay deadline.
- A sanity instance ("always output genesis") that proves the safety claims
  and provably fails `confirmedIncluded`.

## 8. Open choices

1. DECIDED: local repo at ~/ethereum/lean/available-chain (no remote).
   Toolchain leanprover/lean4:v4.30.0-rc2 with Mathlib v4.30.0-rc2, as in
   verified-consensus and fast-confirmation: the engine ports without API
   drift, and the local Mathlib cache is reused.
2. DECIDED: fast regime = full participation and honest > 3/4.
3. DECIDED: participation drop in a separate StableSleepy(θ, η) regime
   (decision A). Each instance declares θ.
4. Time: keep verified-consensus `Time`.

## Draft 4 decisions and reasons

- Sleepy starts at time zero with GST zero. When GST is later, recovery is
  necessary. The engine and `ExecutionValid` prove the clean initial state.
- Each instance sets θ. This keeps the η-sleepy premise explicit and lets
  the instance state the strength that its proof supports.
- Recovery uses a current-count threshold θrec and an optional full
  participation flag. This permits healing after an arbitrary prefix and
  permits an instance to use relative-half participation.
- Accepted-object relay is a regime field. A handler call alone can reject
  an object, so it cannot establish cross-reader acceptance.
- There is one `AvailableChain` bundle. Grid CO uses θrec = 1/2 and
  recoveryFull = false. L* uses θrec = 3/4 and recoveryFull = true.
- Grid CO declares θ_R and proves that its grid level exceeds each faulty
  count `a ≥ 1` when `h ≤ n` and `θ_R·(h+a) < h`. The bound `h ≤ n` holds
  for an awake count in the n-validator model.

## Draft 4.1 change

The outage fields `sleepyBefore` and `etaSleepyBefore` now require their
count conditions from time zero, not from the protected read time `T`.
This applies the standing decision that Sleepy-family premises start at
genesis. It excludes the Draft 4 pending-gate counterexample described in
`GRIDCO-STATUS.md`. No other contract field or claim changed.

## Draft 4.2 change

The shared `RootInjective E I rho` premise makes collision resistance of
block roots explicit. It covers genesis, delivered and emitted proposal
blocks, and all their ancestors. This is the scope needed by the reference
`NamedRootCollisionFree` and `RootInjectiveBelow` proofs. The round-14
root-collision run does not meet this premise. See `GRIDCO-STATUS.md`,
“Resolved in Draft 4.2”. No claim or constant changed.
