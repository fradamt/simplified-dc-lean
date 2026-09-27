# Contract to Lean map

`M` means `AvailableChainModel`; `S` means `AvailableChainStatements`.
Statement names are in `AvailableChain.Statements.Generic`; model names are
in `AvailableChain` or `AvailableChain.Generic`. Sources are relative to
`../decoupled-consensus/verified-consensus`.

## Grid CO: complete Draft 4.3 contract

`AvailableChain.GridCO.gridContract_from_engine` in
`AvailableChainGridCO/Proofs/Contract.lean` proves `GridContract p G E`
for `0 < G` and `E.Δ = p.Δ`. Every run premise comes from the common
contract regimes. See [Grid CO status](GRIDCO-STATUS.md) for constants,
premises, and the brief history of resolved issues.

The instance keeps three layers:

- `Model/Protocol.lean`: parameters, schedule, signed HEADs, proposal
  views, stores, GHOST, counted obligations, release, gates, and `gridCO`.
- `Statements/Contract.lean`: `gridInterface`, `roundedLevel`,
  `gridConstants`, and `GridContract`. It contains no claim proofs.
- `Proofs/`: engine lemmas and the complete contract proof.

The main proof paths below use files in `AvailableChainGridCO/Proofs/`.

- `Basic.lean` proves timing, constant validity, and `outputOrder`.
  `Windows.lean` defines gate and release inputs, `SynchronousLabel`,
  `CleanThroughLabel`, seat alignment, and `ProposalRelayReady`.
  `Regimes.lean` derives these label and relay premises from the regimes.
- `Execution.lean`, `History.lean`, `Stamps.lean`, `Handling.lean`,
  `ClockBounds.lean`, `Receipts.lean`, `Paths.lean`, `HeadTargets.lean`,
  and `ReceiptOrigins.lean` connect events, receipts, paths, and reads.
  `Votes.lean` proves authentication and count bounds; `RecordSlots.lean`
  proves slot order and fresh-record replacement.
- `Goldfish.lean`, `Relay.lean`, and `Map.lean` prove local walk, gate,
  snapshot-count, and obligation invariants. `CrossView.lean` proves
  `sameLabel_from_engine`; `Snapshot.lean` proves `snapshot_from_engine`.
  `Release.lean` bounds conflicting rows that survive release.
- `Walk.lean`, `Support.lean`, `Transfer.lean`, `Frozen.lean`,
  `TransferViews.lean`, and `MergedViews.lean` prove ordinary HEAD
  transfer. `Preservation.lean` proves `preserve_from_engine`.
  `GenuineHistory.lean` then gives clean history; `CleanSafety.lean`
  proves `clean_safety_from_engine` and `monotone_from_engine`.
- `Roots.lean` derives root uniqueness from the contract. `Proposals.lean`
  proves honest emission and proposal views. `WalkTransport.lean`,
  `ProposalAdoption.lean`, `ProposalDelivery.lean`, `ProposalViews.lean`,
  `ProposalViewRelay.lean`, and `ProposalTransport.lean` prove delivery
  and adoption. `ProposerTransfer.lean` and `ProposalHeads.lean` connect
  ordinary proposal parents to honest HEADs. `CleanInclusion.lean` proves
  `included_from_engine` with delay `6Δ` for all three inclusion fields.
- `Coverage.lean` proves clean coverage and public row writes.
  `Protection.lean` proves preservation from armed rows.
  `Outage.lean` proves `stable_resilient_from_engine`, including the
  pending gate and renewal, with `A = 4Δ` and `Π = min(η,L)`.
- `RowOrigins.lean`, `RecoverySupport.lean`, and `RecoveryPersistence.lean`
  prove exact row sources and permanent support. `RecoveryStages.lean`
  proves row and source support after `K` stages. `RecoveryRepair.lean`
  proves record repair; `RecoverySuffix.lean` proves the safe suffix.
  `Recovery.lean` proves `recovered_from_engine` within `K(L+Δ)+G+10Δ`.
- `Contract.lean` constructs the bundle directly. The library root imports
  it and `Tests/Smoke.lean`; all proof modules are in the default build.

## SA: slow arming with one release level

`AvailableChain.SA.saContract_from_engine` in
`AvailableChainSA/Proofs/Contract.lean` proves the full Draft 4.3 bundle.
`fastP1_from_engine` in `Proofs/FastOutage.lean` proves the fast outage field of that bundle. See [SA status](SA-STATUS.md) for the rules, constants,
proof path, and validation.

The instance has three layers:

- `Model/Protocol.lean`: SA parameters and the shared engine with the
  slow-arming lease policy. Raw empty and vetoed gate results are saved.
- `Statements/Contract.lean`: `saInterface`, `saConstants`,
  `SAContract`, and the proof helper `HighParticipationBefore`.
- `Proofs/`: clean claims, both outage bounds, source support, recovery,
  and the complete bundle. `Tests/Smoke.lean` checks the lease rules;
  `Tests/Axioms.lean` audits the new public theorems.

The shared engine and proofs remain under `AvailableChainGridCO/`.
`LeasePolicy` defaults to Grid CO; SA selects `slowLeasePolicy`.
`RawHistory.lean` tracks saved local results. `LocalTransfer.lean`
handles the pending outage HEAD without assuming a covering lease.
`RecoveryRepair.lean` and `Recovery.lean` now expose admission-based
source support and common contract assembly. The grid instance retains
its original admission rule and `gridContract_from_engine` theorem.

## SA-PC: persistent TA certificates (in progress)

`AvailableChainSAPC` adds the executable SA-PC model and the additive
strong companion in `AvailableChainStatements/Strong/`. The base contract is frozen at Draft 4.3. See [SA-PC status](SAPC-STATUS.md)
for proved facts, exact gaps, and validation.

`State.base` reuses the Grid CO/SA engine. Complete signed HEADs and PC
metadata stay in the SA-PC archive and proposal store. Active choices add
F4 and mandatory finite roots. The gate gives each prefix its own PC
guard, with the lease loop outside the stable-record PC veto.

`Statements/Contract.lean` declares the base bundle, including fast P1,
and the strong companion with the requested constants. Current proofs
cover constants, nesting, local SA projections, signature provenance,
cap-test soundness and permanence, raw lease sources, and derivation of
the cap from Recovery. Timed receipt bounds, admitted path closure, exact
timely-save and freeze origins, save retention, and honest ack/preparation
sources are now proved. The complete SA-PC bundle inhabitants are pending.

## Common model and contract

Draft 4.2 defines `BlockInRun` and `RootInjective` in
`AvailableChainStatements/Generic/Conditions.lean`. Sleepy, Outage, and
Recovery require this root premise; StableSleepy and Fast inherit it.
All witness runs satisfy it.

```text
┌────────────────────────────┬────────────────────────────────────────────┬───────────────────────────────┐
│ Contract item              │ Lean name                                  │ File                          │
├────────────────────────────┼────────────────────────────────────────────┼───────────────────────────────┤
│ §2 time, environment       │ Time; Generic.Env                          │ M/Objects/Time; M/Generic/Env │
│ §2 protocol, wire objects  │ Generic.ProtocolSpec n; Signed; Auth;      │ M/Generic/Run;                │
│                            │ ProtocolSpec.Object                        │ M/Objects/Seats               │
│ §2 run and assignments     │ Generic.Run (seatOf, proposerOf);          │ M/Generic/Run                 │
│                            │ Run.holder                                 │                               │
│ §2 step, emission, sleep   │ World.step; Run.emittedAt; Run.emits       │ M/Generic/Run                 │
│ §2 signatures              │ UnforgeableSignatures                      │ S/Generic/Conditions          │
│ §2 delivery                │ PartialSynchrony; HealthyPrefixDelivery;   │ S/Generic/Conditions          │
│                            │ accepted-object relay                      │                               │
│ §2a K1, K6 seats per label │ Auth.seat; Run.seatOf : Label → Fin n ≃ V  │ M/Objects/Seats; M/.../Run    │
│ §2a K2 no identity         │ ProtocolSpec n has no V                    │ M/Generic/Run                 │
│ §2a K3 emission-neutral    │ World.step (tick = clock only)             │ M/Generic/Run                 │
│ §2a K4 unit seats          │ Env has no weights; counts in conditions   │ M/Generic/Env                 │
│ §2a K5 act once            │ duties_spec; duties_nodup; emittedAt       │ M/Generic/Run                 │
│ §3 interface               │ Interface; Output; readAt                  │ S/Generic/Interface           │
│ §4 participation, faults   │ awakeAt; awakeInClosed; faulty;            │ S/Generic/Conditions          │
│                            │ AwakeMajority; EtaSleepy;                  │                               │
│                            │ FullParticipation; BelowQuarter            │                               │
│ §4 proposer recurrence     │ HonestProposerRecurrence                   │ S/Generic/Conditions          │
│ §4 regimes                 │ SleepyRegime; StableSleepyRegime;          │ S/Generic/Regimes             │
│                            │ FastRegime; OutageRegime; FastOutageRegime │                               │
│                            │ RecoveryRegime                             │                               │
│ §5 properties              │ SafeFrom; MonotoneFrom; OutputOrder;       │ S/Generic/Properties          │
│                            │ HonestProposalAt; HonestAwakeProposer;     │                               │
│                            │ IncludedFrom; PersistsThrough              │                               │
│ §5 claims                  │ AvailableChain; RecoveredAt                │ S/Generic/Claims              │
│ §6 constants               │ Constants; Constants.Valid                 │ S/Generic/Constants           │
└────────────────────────────┴────────────────────────────────────────────┴───────────────────────────────┘
```

```text
┌──────────────────────────────────────────────────┬──────────────────────────────────────────────────────┐
│ Lean names                                       │ Source, and change                                   │
├──────────────────────────────────────────────────┼──────────────────────────────────────────────────────┤
│ Slot; BlockId; genesisRoot; Time                 │ Model/Objects/{Identifiers,Time}.lean; unchanged     │
│ Block and ancestry (preceq, prec, compatible)    │ Model/Objects/Blocks.lean; no proposer field, no V   │
│ Event; World; Run.stateBefore/…/final            │ Model/Generic/Run.lean; unchanged                    │
│ ProtocolSpec n                                   │ Generic/Run.lean ProtocolSpec V; new: no V, tick     │
│                                                  │ split into clock/act/propose/gossip, labels, slots   │
│ World.step                                       │ tick applies clock only (K3)                         │
│ Run                                              │ adds seatOf, proposerOf                              │
│ Run.emittedAt; emits                             │ recomputes emission from state, awake, assignments   │
│ Run.processes; handlesAt; acceptsAt              │ deliveries only; handles takes the delivered object  │
│ Env                                              │ Generic/Env.lean; electorate removed (unit seats)    │
│ Interface                                        │ Statements Interface; only outputs, block, opening   │
│ UnforgeableSignatures                            │ by holder of the authentication                      │
│ ExecutionValid                                   │ no sleep field: the engine gates emission            │
│ PartialSynchrony; HealthyPrefixDelivery          │ Statements Conditions.lean; unchanged                │
│ AwakeMajority; EtaSleepy; BelowQuarter           │ counts instead of weights                            │
│ HonestProposerRecurrence                         │ SingleProposerRecurrence; proposer awake             │
│ IncludedFrom                                     │ requires a proposal only from an awake honest        │
│                                                  │ proposer                                             │
│ Regimes, Claims, Properties (others)             │ Statements Generic; types adapted                    │
└──────────────────────────────────────────────────┴──────────────────────────────────────────────────────┘
```

`OutageRegime` uses `HealthyPrefixDelivery` only before `b₀`; it imposes no
delivery bound in `[b₀,b₁)`. Its two count premises apply from time zero,
including times before the protected read T. Draft 4.3 adds
`FastOutageRegime` and `stableResilientFast`, with the same persistence
conclusion and the fast arming lag. The witness also proves that fast
arming need not satisfy the general lag test.

## L* instance (definitions and statement; no claim proofs)

`LStar` below means `AvailableChain.LStar`. The pinned Goldfish source is
`../decoupled-consensus/verified-consensus/docs/PROTOCOL.md` §§2.1–2.3 and
`DecoupledConsensusModel/Protocol/`. The lock source is
`guarded-override.md` §§2, 3.1, 4.2, 10.1, with the checked list in
`lstar-recovery.md` §2.

```text
┌──────────────────────────────┬─────────────────────────────────────────────────────┐
│ Lean name                    │ Source rule                                         │
├──────────────────────────────┼─────────────────────────────────────────────────────┤
│ Params; proposalTime;        │ L* t_r, v_r, e_r, d_r, expiry; memory η           │
│ voteTime; earlyTime; gateTime│                                                     │
│ Msg; State; admitVote;       │ Goldfish HEAD, proposal view, vote/block handlers │
│ admitProposal; process       │                                                     │
│ resolvedBefore; proposerView;│ Goldfish resolution and previous-slot views        │
│ voterView; voterSupportView; │                                                     │
│ voterTree                    │                                                     │
│ goldfishScore; ghost;        │ Goldfish score, GHOST, eligibility, fork choice    │
│ goldfishEligible; forkChoice │                                                     │
│ earlyVotes; savedEarly;      │ L* early subtree snapshot, historical D and q    │
│ memoryDenominator; quorum    │                                                     │
│ confirmation; gate; clock   │ Genuine Goldfish gate; lock acquire/renew/expire  │
│ advance; stable; confirmed  │ L* separate S and G records and nested accessor   │
│ lstar; lstarInterface        │ Contract §2a ProtocolSpec and §3 interface        │
│ lstarConstants;              │ Contract §6, L* result constants and statement   │
│ LStarContract                │                                                     │
│ Tests.smokeRun; smokePass    │ Three honest HEADs, one silent faulty seat        │
└──────────────────────────────┴─────────────────────────────────────────────────────┘
```

The executable model is in `AvailableChainLStar/Model/Protocol.lean`; the
contract statement is in `AvailableChainLStar/Statements/Contract.lean`.
`Proofs/FastOutage.lean` derives fast P1 from a general P1 proof; the
general proof remains pending.
The `#eval` check is in `AvailableChainLStar/Tests/Smoke.lean`.

## Witnesses (§2a K8, §7)

`AvailableChainWitnesses` is a Lake library and a default target. It does not
change the model or statement libraries.

```text
┌─────────────────┬───────────────────────────────────────────────────┬─────────────────────────────┐
│ Witness         │ Proved facts                                      │ File                        │
├─────────────────┼───────────────────────────────────────────────────┼─────────────────────────────┤
│ alwaysGenesis   │ Safety, monotonicity, and nesting for every run;  │ Witnesses/Sanity.lean       │
│                 │ a valid Sleepy run refutes inclusion for every D  │                             │
│ pooledLMD       │ Valid synchronous 2-honest/1-fault per label;     │ Witnesses/Accumulation.lean │
│                 │ spent B votes, late X votes, and a Y read reorg   │                             │
│ Regime premises │ Sleepy, StableSleepy (θ = 3/4), Fast, both Outage │ Witnesses/Regimes.lean      │
│                 │ regimes, Recovery; one fault and distinct views   │                             │
│                 │ one sleeping honest node where permitted          │                             │
└─────────────────┴───────────────────────────────────────────────────┴─────────────────────────────┘
```

The regime run relays an accepted object at time zero to all honest readers.
`acceptedRelayNonvacuous` records an active cross-reader deadline. A later
faulty object gives distinct honest views. The Recovery witness has an
actual honest proposal at slot 2. The
`RecoveryRegime` type does not require this: its recurrence can have no
windows if `proposerGap` exceeds the remaining horizon, and `opening` does
not require `propose` or `block` to return a value. A future contract decision
can strengthen that premise. No witness uses `native_decide`.

`Sanity.confirmedIncluded_claim_fails` states the failure for every integer
delay `D`. Its run has one honest, awake proposer and public ticks through
`max 1 (1 + D)`. The protocol always returns genesis and permanently excludes
all objects, which agrees with its state transition.

The accumulation witness models the vote pooling issue cited in
[RLMD-GHOST §1.2.1](https://arxiv.org/html/2302.11326v3). Labels 0, 1, and 2
act at times 0, 1, and 2. Their two honest seats vote for parent B, while
their faulty seat withholds a vote for hidden child X. At time 3, Y becomes
visible and both honest seats of label 3 vote for Y. The three X votes reach
both honest nodes at time 4. `WithheldFaultyVote` records a signing time equal
to each vote's act time, since faulty signing is outside `Run.emits`.
`noFaultySeatDeliveryEarly` proves that every
delivered faulty seat object arrives at or after its label's act time.
`honestParentVotes`, `honestVisibleVotes`, and `pooledCounts` prove the six
spent B votes, two Y votes, and three X votes. The tally counts every received
seat vote across labels and uses no validator identity. `attackSynchrony`
proves `PartialSynchrony` through the time-5 horizon, including relay of the
released X votes. `accumulationWitness` proves that an honest confirmed read
contains Y at time 3 and does not contain Y at time 4.

Fast has full honest participation from time zero. Recovery has an honest
sleeper before GST at time 1.
