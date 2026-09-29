# Contract to Lean map

## Receipt relay update (2026-09-28)

The dated relay note in `CONTRACT.md` supersedes references below to
accepted-object regime fields. The public regimes now require receipt
relay. The shared `GridCO/Proofs/ReceiptRelay` and `Paths` modules derive
vote settlement and block storage. `ScoreExtension` supplies the common
seat, score, and eligibility algebra; `ProposalTransport` constructs it
from actual runs. Exact proposal vote-set helpers are replaced.
`SAPC/Proofs/ReceiptRelay` derives exact complete-object relay and provides
specialized regime methods for its archive consumers. No model rule or
public contract conclusion changes.


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
  `Execution.lean` keeps only the Grid CO forms of the schedule lemmas.
  The engine-generic lemmas (namespace `AvailableChain.Engine`) are in
  the library `AvailableChainKit` (see "Kit and engine v2 sketch").
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

## SA-PC: persistent TA certificates

`AvailableChain.SAPC.sapcContract_from_engine` in
`AvailableChainSAPC/Proofs/Contract.lean` proves the full Draft 4.3 bundle,
including SA-PC `fastP1_from_engine`. `sapcStrong_from_engine` in
`Proofs/StrongContract.lean` proves the additive strong companion.
Both require `G > 0` and `E.Δ = p.Δ`. No requested claim remains pending.
The base contract is unchanged. See [SA-PC status](SAPC-STATUS.md).

Recovery uses exact lease sources, SA's shared source-support induction,
and F4 transfer. `RecoveryBoundary` proves the two-lease support boundary;
`RecoveryRoots` and `RecoveryProposal` prove common exact proposal HEADs;
`RecoveryService`, `RecoveryGate`, and `RecoveryRepair` prove a common PC
and record repair within `2L+G+8Δ`. `RecoverySafety` proves the base safe
suffix. `RecoveryStrong` proves recovered strong safety and inclusion,
including late certificate reveals. The requested recovery cap follows
from the unchanged full-participation Recovery regime with `θrec = 2/3`.

The following implementation notes record the earlier proof rounds.
Their pending-work statements are historical; round 22 closes those gaps.

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
sources are proved. `BaseArchive` connects cached keys to original signatures;
`TimelyDelivery` and `AckDelivery` connect delivered quorums to saves and
PC completion. `Assembly` proves archive-scan completeness. `CertificateRelay`
proves PC and cap-proof relay at the contract deadlines. `ActiveCounts`
bounds detected equivocators in base-cache and merged HEAD views without
an actual fault cap. `BaseViews` and `DeclaredSupport` prove archive sources,
label preservation, and support subsets for frozen and carried views.
`FrozenViews` connects ordinary saved views to their exact clock sources.
`Floor` proves the active declared-path witness and local F4 transfer;
`EffectiveScores` proves active q-score dominance over conflicting branches.
`Proposals` and `ProposalDelivery` prove actual emission, acceptance, and
path delivery before HEAD. `HeadTargets` and `HeadEmission` prove admitted
targets, slot bounds, complete honest HEAD emission, and target-path relay.
`ProposalViews` reuses the SA merge proofs to include the proposer's raw
and declared support keys in each HEAD view. `CertificateService` proves
PC completion before the 6Δ gate from exact preparations and extending
next HEAD choices under full participation at those duties and the cap.
`RecentArchive` supplies the base-key-or-equivocation alternative for
recent archived signatures. `TimelyTransfer` proves q-score transfer,
active next-HEAD coverage with compatible finite roots, and common
disablement after a compatible-root departure. `MergedReceipts` proves
reverse relay of the complete merged raw view. `QuorumGenuine` proves
same-label timely-N/genuine compatibility without a fault cap.
`EarlyReceipts` proves strict-cutoff presence from base stamps.
`GenuineTransfer` constructs the shared SA transfer interface for actual
SA-PC views, proves raw genuine compatibility at one label, and transfers
genuine prefixes to the actual next HEAD with explicit root premises.
Above-f support permits any selected PC; lower support uses selected-PC
compatibility. `TransferRegimes` derives relay premises from the fixed
synchronous and healthy-prefix conditions. Honest proposal choices and clean inclusion are proved in round 18.
Pending outage transfer and the complete bundle proofs remain open.
The clean root proofs are described below.
`Statements/CleanInvariant` now defines `cleanRunPath` from actual run
sources and `JointCleanInvariant` without a path argument. The old
conditional predicate is named `CleanPathFacts`. `RunCleanPath` and
`RunCleanTicks` prove the new initial, delivery, freeze, between-duty,
and capped proposal steps. `GenuineHistory` proves unconditional record,
saved-result, and finite-row source membership, plus finite-root
compatibility from ordered genuine history. Shared `HistoryInduction`
contains the extracted label induction used by both SA and SA-PC.
`Preservation` derives actual raw batch preservation from Sleepy and
honest HEAD coverage, reusing SA's confirmation theorem. Its
`clean_genuine_history_of_pc` leaves only active-PC compatibility as a
label-induction input. `CleanService` proves honest N/PC prefix witnesses
and exact raw proposal service from common exact HEADs. The clean safety
and 6Δ reductions consume the corrected invariant. The round-15 modules
below prove uncapped event preservation, safety, and monotonicity.
Round 18 completes common proposal choices and clean inclusion.

`Tests/CleanInvariantCounterexample` retains the complete capped Sleepy
run that refutes the round-9 arbitrary path-extension obligation. It also
checks that the new path excludes the losing sibling and contains the
actual next timely save. `Pending/RejectedCleanInduction` holds the old
statement, and `Pending/CleanInductionCounterexample` refutes it.
`Pending/CleanInduction` retains the historical exact proposal-choice
obligation and its round-18 proof. The event and PC-transfer obligations
are also discharged.
No pending module is imported by a default target. See the status document.

## Common model and contract

Draft 4.2 defines `BlockInRun` and `RootInjective` in
`AvailableChainStatements/Generic/Conditions.lean`. Sleepy, Outage, and
Recovery require this root premise; StableSleepy and Fast inherit it.
All witness runs satisfy it.

`CleanPCPath` proves capped PC membership in the canonical source path
and the strict selected-PC label bound. `RunCleanHeads` proves capped
HEAD/release preservation, including the final incomplete HEAD.
`RunCleanTransfer` derives timely continuation and a selected-PC prefix
of the pending genuine result without a following-gate horizon premise.
`MergedReceipts.local_back_receipts` and the factored genuine transfer
proof supply the local reverse receipt condition.
`RunCleanFacts` reconstructs source facts and restricts the capped
invariant to earlier prefixes. `RunCleanGates` proves source comparison,
ordered history, and the full capped early/gate step. `RunCleanCapped`
proves the capped run invariant and derives safety and monotonicity of
both base outputs under that cap. The round-15 induction removes the
cap for safety and monotonicity. Round 18 completes common proposal
choices; see `SAPC-STATUS.md`.

`Disabled` proves the full SA clock projection after disablement and
retains the joint invariant at the mode-changing receipt. `RunCleanHeads`
proves the uncapped disabled HEAD step. `RunCleanFacts` now reconstructs
and restricts source facts without the cap, using `q>a`. `RunCleanUncapped`
derives finite roots below timely saves from actual lease sources, proves
common disablement after departure, and proves first transfer for an
active gate PC. `RunCleanActiveTransfer` proves uncapped timely
continuation before an active input and selected-PC coverage of the pending raw result.
`RunCleanAuthority` retains continuation after disablement.
`RunCleanDisabledGates` proves the full disabled early/gate step;
`RunCleanActivePath` compares new and old sources at active ticks.
`RunClean` combines these steps into `clean_run_invariant` and
`clean_safety_from_engine`. Both base outputs have cross-reader safety
and local monotonicity under plain Sleepy, with no added fault cap.
Both P1 claims, strong claims, recovery, and both complete bundle
inhabitants remain pending. Round 18 completes proposal choices and inclusion.

Round 16 adds `ProposalOrigins`, `ProposalCounts`, `ProposalMerge`,
`ProposalTransport`, and `ProposalFloors`. These prove common proposal
participant counts, equivocation tests, declared-support scores, and
active F4 floors without a cap. The ordinary view transport reuses
`GridCO.ProposalViewTransport`. The shared GHOST transport proof now
also permits extra candidates whose scores are below the protected
path. Exact HEAD choices still need PC selection and finite-root
placement; common floors alone do not prove inclusion.

Round 17 adds `ProposalCertificates`, `ProposalAuthority`,
`ProposerTransfer`, `ProposalRoots`, and `ProposalHeads`. Frozen evidence
reaches the proposer, the carried live PC is valid at HEAD, and exact
selection retains the frozen encoding at equal rank. The selected rank
is common without a cap. Under plain Sleepy, active targets and F4
anchors are common. The shared SA receipt and GHOST proofs place finite
roots and active PC targets on the ordinary proposer walk and prove
that the honest proposal has that parent in either mode. A disabled
HEAD chooses the exact proposal, including when its proposer was active.
Round 18 completes active-tree eligible-path reflection and walk transport.

Round 18 adds `ProposalEligibility`, `Clean`, and `GateAdmission` and
extends `ProposalHeads`. The shared SA receipt interface gives a strict
non-equivocating majority in the proposer view. Common scores reflect
eligible old paths; authentication identifies the fresh proposal. The
shared adoption theorem now accepts extra ineligible paths, with its
original API retained. Exact active and disabled HEAD choices then give
both base inclusion claims under Sleepy and the StableSleepy and Fast
fields in `6Δ`, without a cap. The former pending proposal obligation has
a proof. Local gate lemmas establish first-prefix lease acquisition when
the raw descendant is PC-vetoed and preservation of an already protected
record prefix. Both run-level P1 claims still need the healthy-prefix and
pending-boundary proofs. Strong claims, recovery, and bundle assembly
also remain pending.

Round 19 adds `LeaseProtection`, `OutageProtection`, `GateRead`,
`HealthyBatch`, `SlowHistory`, `LocalTransfer`, and `PendingProtection`.
The shared `ProtectionInduction` supplies the same event induction and
public-read bridge for SA and SA-PC. Actual prefix leases persist until
their deadlines under arbitrary delivery and mode changes. Healthy early
batches give pending raw results and fast admission; immutable raw windows
give slow admission. Local pending HEAD transfer needs no relay or prior
lease. `pending_prefix_protection` combines these facts but still requires
healthy-prefix record and PC-authority premises. Neither contract P1 claim
is proved yet; strong claims, recovery, and the bundle inhabitants remain
pending. No contract or executable rule changed.

Round 20 completes both P1 claims in `Proofs/Outage.lean`:
`stable_resilient_from_engine` and SA-PC `fastP1_from_engine`. The shared
`RunPrefix` and `HealthyPrefix` proofs let `HealthyRun` reuse the uncapped
clean induction through a healthy cutoff equal to a gate. `HealthyHistory`
and `PendingAuthority` derive the pending finite and PC guards from actual
sources, with no cap. `RecordHistory` and `HealthyCoverage` connect stable
reads to healthy HEADs and records. The shared `History` field proof keeps
the original SA/Grid CO API. Slow-window and fast-count admission then
close the pending protection interface and both exact contract claims.

`StrongClean` proves `strong_safe_from_engine` and
`strong_included_from_engine` under the explicit cap. The proof orders PC
targets by preparation label and supplies exact `6Δ` PC service. Sound
arming, persistence with no budget, late-reveal protection, Recovery, and
the two bundle inhabitants remain pending. No contract or executable rule
changed. Earlier round summaries above describe their historical status.

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

## Framework prototype (Phase 0)

`AvailableChainFramework` is a Lake library and a default target. It has
no protocol. It is a type-scanning catalog and certificate framework over
the contract (`AvailableChainStatements`). Its namespace is
`AvailableChain.Framework`. See [FRAMEWORK-DESIGN.md](FRAMEWORK-DESIGN.md)
§8 for the Phase 0 row, the accepted deviations and the lock change log.
Plan 1a (`docs/plans/2026-09-28-phase1a-gate-catalog.md`) added claim
domains, facets, shared profile constants, late triggers, the standard and
strong tiers, and the profiles `ac-4.3` and `strong-1`. The tables below
show the state after plan 1a. File paths below are relative to
`AvailableChainFramework/`.

```text
┌──────────────────┬─────────────────────────────────────────────┬───────────────────────┐
│ Module           │ Contents                                    │ File                  │
├──────────────────┼─────────────────────────────────────────────┼───────────────────────┤
│ ClaimDomain      │ Validators (bundled V, DecidableEq,         │ ClaimDomain.lean      │
│                  │ Fintype); ClaimDomain (id, Inst, Ctx,       │                       │
│                  │ admissible, horizon): the instances that a  │                       │
│                  │ claim speaks about and their run contexts   │                       │
│ Hooks            │ Outcome (E4 classification); classify;      │ Hooks.lean            │
│                  │ HooksSound (5 fields: excludes_inert,       │                       │
│                  │ excludes_stable, processed_stable,          │                       │
│                  │ deps_stable, handles_carries)               │                       │
│ Instance         │ Instance (n, P, Δ, Δ_pos, iface, hooks);    │ Instance.lean         │
│                  │ V1Ctx (an environment and a v1 run);        │                       │
│                  │ ClaimDomain.v1                              │                       │
│ Claim            │ RefutationKind; ClaimSpec K (id, Const,     │ Claim.lean            │
│                  │ valid, le, le_refl, le_trans, Point,        │                       │
│                  │ regime, conclusion, trigger with a time H,  │                       │
│                  │ transport, refutable); holds; inhabited     │                       │
│                  │ (the trigger at a time of at least H)       │                       │
│ Cert             │ Cert; Refutation; RefutationFamily;         │ Cert.lean             │
│                  │ Cert.weaken; Cert.not_refuted;              │                       │
│                  │ Refutation.family_of (all over a claim      │                       │
│                  │ domain K)                                   │                       │
│ DomainMap        │ DomainMap K' K (an instance map and an      │ DomainMap.lean        │
│                  │ equivalence of contexts); ClaimSpec.pull;   │                       │
│                  │ holds_pull; inhabited_pull; Cert.pull;      │                       │
│                  │ ClaimDomain.ofV1; DomainMap.ofV1            │                       │
│ Facets/Strong    │ StrongInstance (extends Instance with the   │ Facets/Strong.lean    │
│                  │ strong output); StrongInstance.sface;       │                       │
│                  │ ClaimDomain.strong; DomainMap.strongV1      │                       │
│ Profile          │ Profile.Entry (a claim and the projection   │ Profile.lean          │
│                  │ of the shared constant); Profile K (id,     │                       │
│                  │ Shared, valid, entries); ProfileCert (one   │                       │
│                  │ shared constant, one certificate per entry  │                       │
│                  │ at its projection; Type 1);                 │                       │
│                  │ Profile.holdsAt; ProfileCert.holdsAt        │                       │
│ Pareto           │ stronger; pareto; pareto_sub; pareto_covers │ Pareto.lean           │
│                  │ (every constant is covered by a Pareto      │                       │
│                  │ constant)                                   │                       │
│ Catalog/Core     │ sleepy; safeOf; safeConfirmed; safeStable;  │ Catalog/Core.lean     │
│                  │ prefixOrder; includedConfirmed;             │                       │
│                  │ includedConfirmed_trigger_late; core (the   │                       │
│                  │ floor profile; Shared := Time, the D of     │                       │
│                  │ includedConfirmed); Candidate (Type 1);     │                       │
│                  │ not_candidate_of_family                     │                       │
│ Catalog/Meaning  │ meaning pins: <claim>_holds_iff and         │ Catalog/Meaning.lean  │
│                  │ <claim>_inhabited_iff for the four core     │                       │
│                  │ claims, in the Phase 0 form with L1         │                       │
│                  │ predicates only                             │                       │
│ Catalog/Mono     │ zeroConstants; the monotonicity lemmas that │ Catalog/Mono.lean     │
│                  │ the transport proofs use: etaSleepy_mono,   │                       │
│                  │ recurrence_mono, safeFrom_mono,             │                       │
│                  │ includedFrom_mono, and <regime>_mono for    │                       │
│                  │ StableSleepy, Outage, FastOutage, Recovery  │                       │
│                  │ and recoveredAt                             │                       │
│ Catalog/Standard │ the standard tier over ClaimDomain.v1:      │ Catalog/Standard.lean │
│                  │ EtaConst; OutageConst; RecoveryConst;       │                       │
│                  │ includedStable; includedStableFast;         │                       │
│                  │ persistOutage; persistOutageFast;           │                       │
│                  │ recovered; persistTrigger; for each claim   │                       │
│                  │ <claim>_le_trans, <claim>_transport and     │                       │
│                  │ <claim>_trigger_late;                       │                       │
│                  │ <claim>_no_witness_at_zero_budget for the   │                       │
│                  │ two persistence claims                      │                       │
│ Catalog/Strong   │ the strong tier over ClaimDomain.strong:    │ Catalog/Strong.lean   │
│                  │ StrongIncConst; StrongRecConst;             │                       │
│                  │ StrongRecIncConst; strongSafe;              │                       │
│                  │ strongIncluded; strongPersist;              │                       │
│                  │ strongRecoveredSafe;                        │                       │
│                  │ strongRecoveredIncluded;                    │                       │
│                  │ strongIncludedTrigger; for each claim       │                       │
│                  │ <claim>_le_trans and <claim>_transport;     │                       │
│                  │ <claim>_trigger_late for each claim with a  │                       │
│                  │ trigger other than True                     │                       │
│ Catalog/Profiles │ the five regime adapters                    │ Catalog/Profiles.lean │
│                  │ (stableSleepyRegime_iff, outageRegime_iff,  │                       │
│                  │ fastOutageRegime_iff, recoveryRegime_iff,   │                       │
│                  │ recoveredAt_iff); ac43 (ac-4.3:             │                       │
│                  │ Shared := Constants, nine claims); ac43_iff │                       │
│                  │ (↔ AvailableChain); ac43_valid_cross;       │                       │
│                  │ strong1 (strong-1:                          │                       │
│                  │ Shared := Constants × StrongConstants, five │                       │
│                  │ claims); strong1_iff (↔ StrongClaims)       │                       │
└──────────────────┴─────────────────────────────────────────────┴───────────────────────┘
```

Plan 1b Task 0 moved `Kit/Core` and `Engine/V2Sketch` out of this
library, to `AvailableChainKit` and `AvailableChainEngineV2` (see "Kit
and engine v2 sketch"). `AvailableChainFramework` does not import them.

A claim domain (`ClaimDomain`) names the type of the instances that a
claim speaks about and the type of their run contexts. `ClaimSpec K`,
`Cert`, `Refutation` and `Profile K` are generic over the claim domain
`K`. The v1 claim domain `ClaimDomain.v1` has `Instance` and `V1Ctx`. A
facet is a structure that extends `Instance`, with its own claim domain
and a `DomainMap` to v1 (`Facets/Strong.lean`). A base claim and its
certificates pull back along the map (`ClaimSpec.pull`, `Cert.pull`).

The five regime adapters of the profiles are in `Catalog/Profiles.lean`,
not in `Catalog/Mono.lean`. `Catalog/Mono.lean` has only the monotonicity
lemmas that the `transport` proofs use.

`AvailableChainRegistry` is a Lake library and a default target. It holds
protocol instances over the framework, their certificates and refutations,
and compile-only tests. Its namespace is `AvailableChain.Registry`. File
paths below are relative to `AvailableChainRegistry/`.

```text
┌──────────────────┬─────────────────────────────────────────────┬───────────────────────┐
│ Module           │ Contents                                    │ File                  │
├──────────────────┼─────────────────────────────────────────────┼───────────────────────┤
│ Sanity           │ sanity (the Sanity instance); hooks;        │ Sanity.lean           │
│                  │ certSafeConfirmed; certSafeStable;          │                       │
│                  │ certPrefix; refutedIncluded                 │                       │
│                  │ (RefutationFamily); not_candidate           │                       │
│ Tests/Pareto     │ armedToy (a two-constant test claim: an     │ Tests/Pareto.lean     │
│                  │ arming lag and a budget); the Pareto        │                       │
│                  │ direction example                           │                       │
│ Tests/NewFacet   │ counterStrong (Counter with its stable      │ Tests/NewFacet.lean   │
│                  │ output as the strong output);               │                       │
│                  │ certSafeStableStrong (a pulled base         │                       │
│                  │ certificate); testStrongSafe (a test claim  │                       │
│                  │ with its own id); badStrong;                │                       │
│                  │ refutedBadStrong; refutedBadStrongSafe;     │                       │
│                  │ certStrongSafeCounter (a strong-tier        │                       │
│                  │ certificate)                                │                       │
│ GridCOHooks      │ gridExcludes (E4 exclude); gridCOx;         │ GridCOHooks.lean      │
│                  │ gridCOx_hooks (HooksSound); clock_votes     │                       │
│                  │ (Task 7 Step 1 finding: no clock evaluation │                       │
│                  │ removes votes); gate_votes;                 │                       │
│                  │ inWindow_not_excluded                       │                       │
│ Counter          │ counter (a toy height protocol);            │ Counter.lean          │
│                  │ counterIface; counter_hooks; counterInst    │                       │
│ CounterRun       │ canonical (the synchronous run from         │ CounterRun.lean       │
│                  │ genesis); canonical_execution;              │                       │
│                  │ canonical_synchrony; canonical_relay;       │                       │
│                  │ canonical_sleepy; certSafeConfirmed;        │                       │
│                  │ certSafeStable; certPrefix                  │                       │
│ CounterIncluded  │ counter_included (exact-time inclusion at   │ CounterIncluded.lean  │
│                  │ D = 1); certIncluded (a proposal slot at a  │                       │
│                  │ time of at least H); candidate (Counter     │                       │
│                  │ passes the core floor at D = 1)             │                       │
│ Gaps/NoInput     │ KNOWN GAP I1: clockChain (reads no input);  │ Gaps/NoInput.lean     │
│                  │ clockInst; certSafeConfirmed;               │                       │
│                  │ certSafeStable; certPrefix; certIncluded;   │                       │
│                  │ clockCandidate (passes the core floor at    │                       │
│                  │ D = 0)                                      │                       │
└──────────────────┴─────────────────────────────────────────────┴───────────────────────┘
```

```text
┌────────────────────────────────────┬──────────────────────────────────────────┬─────────────────────┐
│ Script                             │ Check                                    │ Exit codes          │
├────────────────────────────────────┼──────────────────────────────────────────┼─────────────────────┤
│ scripts/CatalogLock.lean --check   │ compares the locked declarations with    │ 0 same, or ADDED    │
│ [--lock <path>]                    │ the lock by name; prints REMOVED,        │ lines only; 1 a     │
│                                    │ CHANGED and ADDED lines; also checks the │ REMOVED or CHANGED  │
│                                    │ axioms of each locked declaration and    │ line; 2 a usage     │
│                                    │ that no two claims have one id           │ error, a bad lock   │
│                                    │                                          │ line, a missing     │
│                                    │                                          │ declaration, a bad  │
│                                    │                                          │ axiom or two claims │
│                                    │                                          │ with one id         │
│ scripts/CatalogLock.lean --write   │ writes the lock; refuses a REMOVED or    │ 0 written; 1        │
│ [--allow-changes] [--lock <path>]  │ CHANGED line unless --allow-changes is   │ refused, nothing    │
│                                    │ given                                    │ written; 2 as for   │
│                                    │                                          │ --check             │
│ scripts/Registry.lean [--check]    │ writes docs/REGISTRY.md; with --check,   │ 0 written, or the   │
│                                    │ compares the generated text with the     │ same; 1 different;  │
│                                    │ file and writes nothing                  │ 2 a usage error or  │
│                                    │                                          │ an unreadable file  │
│ scripts/CheckFrameworkAxioms.lean  │ every constant of                        │ 0 clean; 1 a bad    │
│                                    │ AvailableChainFramework,                 │ axiom; 2 nothing    │
│                                    │ AvailableChainRegistry,                  │ found or a usage    │
│                                    │ AvailableChainKit and                    │ error               │
│                                    │ AvailableChainEngineV2 uses only         │                     │
│                                    │ propext, Classical.choice, Quot.sound    │                     │
│                                    │ (this rejects sorryAx and the axioms of  │                     │
│                                    │ native_decide); reads built data         │                     │
└────────────────────────────────────┴──────────────────────────────────────────┴─────────────────────┘
```

`scripts/Registry.lean` scans the libraries in `instanceLibraries` (now
only `AvailableChainRegistry`) for constants whose type is `Cert c I`,
`Refutation c I`, `RefutationFamily c I`, `ProfileCert p I` or `Candidate
I`, and writes one row per constant to `docs/REGISTRY.md`. The file header
names the scanned libraries. A `ProfileCert` or `Candidate` row has the
kind `profile-cert`, and its claim column shows the profile `id` (for
example `core.v1`). A certificate of a pulled claim shows the base claim
with `(pulled)`. A type behind leading binders (`∀ …, Cert c I`) is
CONDITIONAL and is still written as a row, with status `CONDITIONAL (not a
certificate)`: it is a row of the table, not a certificate. Every other
row's status is `LEAN` only if `Lean.collectAxioms` finds no axiom outside
`propext`, `Classical.choice`, `Quot.sound`; any other axiom (including
`sorryAx`) gives status `UNSOUND(<axiom names>)`. A row of a module under
`AvailableChainRegistry.Gaps` has status `KNOWN-GAP` in place of `LEAN`
(plan 1a Task 0, `gapsPrefix`). A row's claim column keeps the claim's
name and appends `NON-CATALOG` if the `ClaimSpec` is not declared in a
module under `AvailableChainFramework.Catalog`. `docs/REGISTRY.md` is
generated; do not edit it by hand.

`scripts/CatalogLock.lean` locks every declaration that Lean did not
generate in the modules `Hooks`, `Instance`, `Claim`, `Cert`, `Profile`,
`Pareto`, `ClaimDomain` and `DomainMap` of `AvailableChainFramework`, and
in every module under `.Catalog` and `.Facets`. It also locks every
declaration of the library whose type is a `ClaimSpec`, a `Profile`, a
`Profile.Entry` or a `ClaimDomain`. The hash of a line is a hash of the
set of declarations that the locked declaration reaches (its closure), in
a fixed order. Thus a new declaration does not change the line of an old
declaration that does not reach it. A theorem hashes its statement only,
so a new proof of the same statement keeps the hash (design deviation (e),
`FRAMEWORK-DESIGN.md` §8). For this reason, each new claim puts its
`transport` and `le_trans` proofs in named theorems. `Kit` is not locked.
The default lock file is `docs/catalog.lock`. Run `--check` after a build,
because the script reads the built `.olean` files.

`scripts/CheckFrameworkAxioms.lean` also reads built data. Run all three
scripts with `lake env lean --run scripts/<file>.lean` after `lake build
AvailableChainFramework AvailableChainRegistry AvailableChainKit
AvailableChainEngineV2`.

## Kit and engine v2 sketch (plan 1b)

Plan 1b Task 0 (`docs/plans/2026-09-29-phase1b-instances.md`) moved the
engine-generic lemmas and the Framework Kit into the library
`AvailableChainKit` (L5), and the engine v2 sketch into the library
`AvailableChainEngineV2` (L0). Both are Lake libraries and default
targets. No name and no namespace changed; only file paths and imports
changed. `AvailableChainKit` imports only `AvailableChainModel`,
`AvailableChainStatements`, Mathlib and its own modules.

```text
┌──────────────────────────────┬──────────────────────────────────────────┬──────────────────────────────────────────┐
│ Module                       │ Contents                                 │ Moved from                               │
├──────────────────────────────┼──────────────────────────────────────────┼──────────────────────────────────────────┤
│ AvailableChainKit.Core       │ namespace AvailableChain.Framework.Kit:  │ AvailableChainFramework/Kit/Core.lean    │
│                              │ block_preceq_trans;                      │                                          │
│                              │ includedPersist_of_safe (a derived       │                                          │
│                              │ lemma, not a claim)                      │                                          │
│ AvailableChainKit.Engine.    │ namespace AvailableChain.Engine: the     │ AvailableChainGridCO/Proofs/Execution    │
│ Execution                    │ schedule bridges (stateBefore_succ_event,│ (the engine part; the Grid CO forms stay │
│                              │ readAt_eq_stateBefore, …)                │ in Grid CO Proofs/Execution.lean)        │
│ AvailableChainKit.Engine.    │ ClockLaws; now bounds; invariants        │ AvailableChainGridCO/Proofs/EngineClock  │
│ EngineClock                  │                                          │                                          │
│ AvailableChainKit.Engine.    │ runPrefix and its read lemmas            │ AvailableChainGridCO/Proofs/RunPrefix    │
│ RunPrefix                    │                                          │                                          │
│ AvailableChainKit.Engine.    │ prefixEnv; healthyPrefix_* regime        │ AvailableChainGridCO/Proofs/HealthyPrefix│
│ HealthyPrefix                │ transfer                                 │                                          │
│ AvailableChainKit.Engine.    │ genesisEnv; healthyInterior_sleepy       │ AvailableChainGridCO/Proofs/             │
│ HealthyInterior              │                                          │ HealthyInterior                          │
│ AvailableChainKit.Engine.    │ state_interval_induction;                │ AvailableChainGridCO/Proofs/             │
│ ProtectionInduction          │ read_field_eq_clock                      │ ProtectionInduction                      │
│ AvailableChainKit.Engine.    │ clock_field_origin_since                 │ AvailableChainGridCO/Proofs/             │
│ SourceHistory                │                                          │ SourceHistory                            │
│ AvailableChainKit.Engine.    │ stateBefore_stable (a state property     │ AvailableChainRegistry/GridCOHooks.lean  │
│ Stable                       │ that clock and process keep holds for    │ (was AvailableChain.Registry.GridCO)     │
│                              │ the rest of the run)                     │                                          │
│ AvailableChainEngineV2.      │ namespace AvailableChain.Framework.      │ AvailableChainFramework/Engine/          │
│ Sketch                       │ V2Sketch: SpecV2; Isolated (E5);         │ V2Sketch.lean                            │
│                              │ Restorable (E6); tickV2; restartV2;      │                                          │
│                              │ toyV2 (a two-field toy spec)             │                                          │
└──────────────────────────────┴──────────────────────────────────────────┴──────────────────────────────────────────┘
```

`stateBefore_stable` is the only moved declaration with a new full name:
its namespace is now `AvailableChain.Engine`. `time_le_of_key_le` and
`filter_false_of_index_ge` in `Engine/Execution.lean` are no longer
private, because the Grid CO part of `Execution.lean`, now in another
file, uses them. Grid CO's private `block_preceq_trans` (`Map.lean`) and
the Kit's `block_preceq_trans` have different statements; both stay.

## Simplex FG module (DC-fj)

The FG module `SimplexFG.fj` is DC's FG without SG and grades, with the FJ
root rule in place of NJ. Its plan is `docs/plans/2026-09-28-fg-module.md`;
its registry is `docs/FG-COMPOSITION.md`. Both libraries are default
targets. The module does not import the framework, the engine, or an AP.
`AvailableChainKitFG/Pins.lean` records the coverage of each registry id
clause by clause (Lean names and extra hypotheses, or the paper step, the
registry id, or the AP fact that carries the clause).

```text
┌─────────────────────────┬──────────────────────────────────────────┬─────────────────────────────┐
│ Library                 │ Contents                                 │ Namespace                   │
├─────────────────────────┼──────────────────────────────────────────┼─────────────────────────────┤
│ AvailableChainSimplexFG │ LM, definitions and decide examples      │ AvailableChain.SimplexFG    │
│                         │ only: rows and blocks, the chain state   │                             │
│                         │ with no NJ height, E1/E2 evidence, the   │                             │
│                         │ FG client, the DC-fj store (one          │                             │
│                         │ cumulative admitted tree, on_block,      │                             │
│                         │ update_finality, activeView), the FJ     │                             │
│                         │ controls, filteredFrom, fjFrame          │                             │
│ AvailableChainKitFG     │ L5, proofs: DC certificate ports, the    │ AvailableChain.KitFG        │
│                         │ pinned FG lemmas (fg.* and fj.* ids),    │                             │
│                         │ the store invariant and store controls,  │                             │
│                         │ and the pin table (Pins.lean)            │                             │
└─────────────────────────┴──────────────────────────────────────────┴─────────────────────────────┘
```

```text
┌─────────────────────────────┬──────────────────────────────────────────────┬─────────────────────┐
│ Script                      │ Check                                        │ Exit codes          │
├─────────────────────────────┼──────────────────────────────────────────────┼─────────────────────┤
│ scripts/check-fg.sh         │ builds the two libraries once (--wfail),     │ 0 all pass; else    │
│                             │ then runs the root-import check and the four │ the failed step's   │
│                             │ checks below; stops at the first failure     │ code                │
│ scripts/check-fg-syntax.sh  │ no native evaluation outside comments in the │ 0 clean; 1 found; 2 │
│                             │ two FG libraries: native_decide, +native,    │ missing directory,  │
│                             │ native := true, ofReduceBool, ofReduceNat    │ root file or files  │
│ scripts/CheckFGAxioms.lean  │ every constant of the two libraries uses     │ 0 clean; 1 bad      │
│                             │ only propext, Classical.choice, Quot.sound   │ axiom; 2 nothing    │
│                             │ (this rejects sorryAx and the _native axiom  │ found, usage error  │
│                             │ of native_decide); --expect N … checks that  │ or missing name     │
│                             │ the names exist; reads built data            │                     │
│ scripts/FGPinIds.lean       │ prints the manifest of the elaborated pin    │ 0 clean; 2 a pinned │
│                             │ table; --check-names checks that each pinned │ name is not an FG   │
│                             │ Lean name is an FG constant; reads built     │ constant            │
│                             │ data                                         │                     │
│ scripts/check-fg-pins.sh    │ builds the two libraries, runs               │ 0 clean; 1 registry │
│                             │ FGPinIds.lean; strict manifest grammar and   │ mismatch; 2 build   │
│                             │ trailers; no pin id is also a notFormalized  │ failed, bad or      │
│                             │ id; each source resolves to its registered   │ missing manifest    │
│                             │ version with the pinned hash and matches its │                     │
│                             │ §0.1 row; each id has an entry and one Index │                     │
│                             │ row; no active id SUPERSEDED                 │                     │
└─────────────────────────────┴──────────────────────────────────────────────┴─────────────────────┘
```

Run `bash scripts/check-fg.sh` for all checks. The Lean scripts read the built
`.olean` files, which Lean does not compare with the sources: run them alone
only after `lake build AvailableChainSimplexFG AvailableChainKitFG`, with
`lake env lean --run scripts/<file>.lean`.
