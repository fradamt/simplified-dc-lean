# WC corruption growth: proved components and exact open facts

Base: `88c616d`. Branch: `wc-growth`. Date: 2026-10-07.

## Public statement

`WeakContinuationGrowthClaim p G` means
`∀ {V} [DecidableEq V] [Fintype V] {In} (c : AppCodec In) (ΔF : Time),
BoundedGrowthRecovery₂ p c G ΔF`.

For every bounded strong source, choose u, Q, and iSource once, before
quantifying over E' and rho. The source keeps Recovery₂'s one-third cap.
The continuation has Base₂, rho.honest ⊆ source.honest, equal full seat
maps, equal retained input/awake values and ordered signed local events
through the inclusive endpoint, equal GST and Δ, endpoint coverage,
family partial synchrony, separate pending source broadcast/relay duties,
Δ ≤ ΔF, FinalitySlashableBound, and faulty < awakeHonest strictly after
the endpoint. Relay keeps the source post-acceptance processed-state guard
and its original deadline. There is no handover half-cap premise.

The result is WeakContinuationLiveAt₂ at rho's own
`afterTicksIdx rho (gateTime u)`: compatibility, monotonicity, seed,
finalBelow, both outputs, inclusion, and conditional available growth.
There is no finality-liveness conclusion. The claim is not yet closed.

## Proved

- Replay/EventReplay: retained local state and event replay, strict reads,
  matched ticks, inclusive reads, and independent completed-gate indices.
- Seed: refreshed S, height, finalBelow, and live targets transfer locally.
- Counts/Origins/StepInit/Frame: half-cap FaultQ, scoped no-evidence low
  finality, initialization, and all three frame interfaces.
- Assembly/WeakContinuationGrowthSeed: certificate origins are rebuilt
  with continuation FaultQ. The signer is honest in rho. Carrier scope is
  rebuilt from a retained store. A nonempty suffix supplies a retained
  validator and participation at every covered time after GST.
- Dynamics: WCFiniteFacts at any index from local producers; finite event
  facts; delivery, gate tick, non-gate tick, and restart preservation;
  WCGStepStatement and WCGSeededInductionStatement; HEAD batches, receipts,
  retrospective transfer, output service, and WCGFinalBelowStatement.
  Causal consumers take WCFinalityTargetEarlierStatement as a producer.
  Assembly supplies the unchanged wc_finalityTargetEarlier through Export.
- Assembly/WeakContinuationGrowth: proposal pivot, named admission, exact
  HEAD, and WCGInclusion6Statement. The companion frame discharges its
  producer. wcg_seededLiveAt combines induction, finalBelow, and inclusion.
  wcg_liveOfSeed discharges every internal producer from Base₂, synchrony,
  Δ ≤ ΔF, FaultQ, accountability, vote participation, and WCSeed.
  It reuses the original safety and growth theorems. No public regime
  acquired an internal seed, invariant, service, or inclusion premise.
- Assembly/WeakContinuationGrowthSeed: wcg_finiteSeed constructs all
  finite fields from Base₂ and FaultQ. wcg_heightSeed constructs the source
  seed from HealingInput. wcg_sourceWitness selects the uniform source
  witness from the existing HTimeClaim interface. No sibling Assembly
  import or layer exception is needed for these producers.
- EventReplay: every public getter replays through the endpoint.
  wcg_empty_outputs transfers both public outputs' compatibility and
  monotonicity for an empty suffix, with no FaultQ or participation premise.

## Exact missing facts, in work order

1. Complete retained seed replay. Given hS, hc, a nonempty suffix, and the
   selected source WCSeed, construct
   `WCSeed p c E' rho w (afterTicksIdx rho (gateTime w.u))`.
   The unresolved fields are `gates`, `nextHeads`, and `highSources`.
   - Gates: map the retained source gate to rho's index below its cut;
     transfer gateResultAt and gatePassedAt at that mapped index.
   - HEADs: map each source nextHeads tick below rho's cut and transfer
     its deterministic head/path. Rebuild its receipts at rho's index.
   - High sources: map a pre-cut rho HonestRowAt to the corresponding
     source occurrence. Transfer the source and gate reads, then apply
     the source seed's highSources bound. Preserve signed objects and
     local order. Do not assume equal global indices.
   All finite fields can now be rebuilt by wcg_finiteSeed. Certified
   origins and removed source signers are no longer a missing fact.
2. Induction, HEAD/output service, finalBelow, and inclusion are proved
   at the weaker interfaces. No missing event-preservation fact remains.
3. Public assembly: supply the retained seed from item 1, derive the vote
   participation telescope from wcg_participation and firstVoteAfterGST,
   and apply wcg_liveOfSeed. Join this with the empty branch below and
   the one source witness to close WeakContinuationGrowthClaim.
   Source selection through wcg_sourceWitness still takes HTimeClaim as
   its producer; the closed existing H-time proof is not yet joined here.
4. Empty suffix: wcg_empty_outputs handles public getter compatibility
   and monotonicity. Still prove all event-index SSafeFromCut₂ fields,
   proposal inclusion, and conditional growth by retained prefix replay.
   Extend the covered-time output transfer to the full outputs read domain.
   Local event agreement does not equate the two global event indices.
   Do not infer FaultQ when rho.horizon = source.horizon.
5. Full non-vacuity: the corrected five-validator candidate has source
   faults 0 and continuation faults 2. It proves 5 < 3*2 and 2 < 3.
   Delta is 2. The source horizon is 0. The continuation horizon is 1,
   before the next public tick. There are 5 source ticks and 3 retained
   ticks. The final timed execution passed in 3.20 seconds.
   The test checks sorted keys, no duplicate events, horizon bounds,
   honest-only events, all public ticks, real duty-engine transitions,
   empty emissions, genesis-only named scope, local replay, and majority.
   This source is not StrongRecoverySearchPrefix₂. Still construct and
   prove a bounded strong source and its complete growth continuation:
   Base₂, authentication (including carried objects), linked/CStar data,
   collision freedom, synchrony, pending duties, and FinalitySlashableBound.
   The long seven-validator candidate and its unverified endpoint fixture
   are replaced. There is no compile-time #eval or long default runner.

## Checks and commits

- Lead approved WeakContinuationGrowth after WeakContinuationLive in
  the fixed ORDER. This is the only checker change. No allow-list,
  frozen baseline, or layer exception changed.
- Frozen Statements/Claims, FGSAClaims, and original WC proof files
  have no changes. The API manifest adds only the companion entries.
- `7d6a94f`: companion statement, claim, API manifest, and approved ORDER.
- `e29b2af`: initial proved components.
- `07c1822`: retained certificate origins, carrier scope, and participation.
- These checkpoints passed the complete pre-commit list, including
  check-build/checker-self-tests, precheck, NEG=0 claims, and axiom audits.
  Logs: `.lake/wcg-resume-*.log` and `.lake/wcg-seed-*.log`.
- The later modules passed the final checks below. Their separate
  module commits are in the branch history. No push is authorized or attempted.

### Final validation, 2026-10-07

- Full `lake build`: PASS (4363 jobs).
- `bash scripts/check-build.sh`: PASS, including checker-self-tests.
- Separate layers, GLY, and `bash scripts/precheck.sh .`: PASS.
- `NEG=0 bash scripts/check-fgsa-claims.sh`: PASS, including warning-free
  builds, compiled axiom/coverage/constant-use audit, leases and imports.
- CheckProofEqns: 751 proof modules, 1033 exports, zero unaccepted.
- `NEG=0 bash scripts/check-fgsa-manifest.sh`: PASS. All 1200 entries in
  52 modules are complete and have matching hashes.
- Component audit: 64 theorems. Only propext, Classical.choice, Quot.sound.
- The corrected five-validator candidate: PASS in 3.20 seconds. This is
  the finite short-regime check described above, not full non-vacuity.
- `git diff --check`: PASS. Logs: `.lake/wcg-complete-*.log`.
- The same unchanged Lean source tree was validated before the separate
  completed-module commits. Each commit stages only its own module files
  and the matching entries in the axiom audit.
