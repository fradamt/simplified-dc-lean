# WC corruption growth: status and exact open facts

Base: `88c616d`. Branch: `wc-growth`. Date: 2026-10-06.

## Statement

`WeakContinuationGrowthClaim p G` quantifies over V, In, c, and ΔF.
For every bounded strong source, choose u, Q, and iSource once, then
quantify over E' and rho. The source keeps Recovery₂'s one-third cap.
The continuation has Base₂, rho.honest ⊆ source.honest, equal full seat
maps, equal retained input/awake values and ordered signed local events
through the inclusive endpoint, equal GST and Δ, endpoint coverage,
family partial synchrony, separate pending source broadcast/relay duties,
Δ ≤ ΔF, FinalitySlashableBound, and faulty < awakeHonest strictly after
the endpoint. Relay keeps its original source post-acceptance processed
state guard and original deadline. There is no handover half-cap premise.
The result is WeakContinuationLiveAt₂ at the continuation's own
`afterTicksIdx rho (gateTime u)`: compatibility, monotonicity, seed,
finalBelow, both outputs, inclusion, and conditional available growth.
No finality-liveness conclusion is included.

## Proved components

- Replay.lean: filtered local world replay, inclusive reads, completed ticks.
- EventReplay.lean: retained event membership, strict reads, matched tick
  states with independent source and continuation indices.
- Seed.lean: store equality at each run's cut; refreshed S, height,
  finalBelow, and live lease targets transfer to retained validators.
- Counts.lean: participation implies 2a < n; this gives FaultQ.
  The strict suffix produces this cap only when it is nonempty.
- Origins.lean: non-genesis named scope implies FinalityBlock; genesis
  is treated separately. Whole-run accountability excludes evidence on
  named scope. Low finalizations are below CStar and QStar without FaultX.
- StepInit.lean and Frame.lean: companion initialization and the three
  frame interfaces use FaultQ and accountability, without a one-third cap.
- Assembly/WeakContinuationGrowth.lean reuses wc_finalityTargetEarlier,
  wc_seededSafety, and wc_growth_of_safety_inclusion through existing lane
  Exports. Its live wrapper still requires the internal invariant,
  finalBelow, and inclusion producers. It is not the closed claim.

## Exact missing proof facts

1. Full retained seed: from the bounded source's WCSeed, local agreement,
   continuation Base₂, and continuation FaultQ, construct
   `WCSeed p c E' rho w (afterTicksIdx rho (gateTime w.u))`.
   Remaining fields include gates, nextHeads, highSources and finite
   origins. In particular, rebuild `WCFiniteFacts.certified` from retained
   honest quorum origins. Do not transfer a removed source signer.
2. Source witness assembly: select the existing healing witness uniformly.
   `wc_heightSeed` is in the old Assembly module. Reuse must respect
   Assembly imports, or supply a new producer through the permitted lanes.
3. Build participation at every vote from w.u + 1: use retained full
   participation through T and the public strict-suffix field after T.
   Event preservation: prove `WCGStepStatement`, including delivery
   reconciliation, non-gate ticks, gate ticks, and restart cases. Combine
   it with wcg_init to prove WCGSeededInductionStatement. Frame is proved;
   high-finality causality is available through the Assembly adapter.
4. Prove WCGFinalBelowStatement and WCGInclusion6Statement with the weaker
   telescope. These need the service/HEAD, receipt, transfer, and output
   wrappers. Then feed the proved Assembly live wrapper.
5. Empty suffix: rho.horizon = source.horizon gives no half cap. Prove
   prefix-only safety/inclusion/growth by retained replay. Do not use
   wcg_suffix_faultQ without its strict horizon premise.
6. Close WeakContinuationGrowthClaim without adding any internal seed,
   invariant, service, or inclusion premise to the public regime.
7. Full non-vacuity: the executable seven-validator candidate uses actual
   FG-SA ticks and handlers for 264 times, with source faults 2 and suffix
   faults 3 < 4 retained honest. Full Base₂, pending duties, synchrony,
   collision freedom, and FinalitySlashableBound must still be proved.
   A passing execution check alone does not discharge these propositions.

## Approved guard registration

`scripts/check-fgsa-claims.sh` has a fixed Statements `ORDER`. Register
`WeakContinuationGrowth` after `WeakContinuationLive`. Its imports are
`FinalityApi` and `WeakContinuationLive`. The lead approved this exact ORDER addition on 2026-10-06. It is now
registered. No other checker, allow list, baseline, or layer exception
has changed. The required checks are being rerun before the first commits.

The earlier B4 and cross-lane requests are withdrawn. Proof interfaces
live in the new lane; cross-lane theorem reuse occurs in Assembly through
existing Exports. The candidate test uses an own-library import route.
The API manifest was regenerated. Its existing prose and entries stay
unchanged; only the new companion entries are added. Frozen files remain
byte-identical. No claim-to-claim proof or Claims-to-Claims import was added.

## Validation

The results below are from the previous run. New validation results
will be appended after the approved ORDER registration. No push is authorized.

### Previous-run validation results

- `lake build`: PASS, 4361 jobs before final import comments and removal
  of one unused import. All component and axiom test builds pass.
- Axiom audit: 21 component/adapter theorems. Only `propext`,
  `Classical.choice`, and `Quot.sound`. No new axiom or admitted proof.
- `bash scripts/check-build.sh`: FAIL only at checker-self-tests. The
  audit-pool self-test expects the claims process to stay running, but it
  exits on the two MODULE ORDER findings. All earlier checks pass, including
  the rebuild cone, headers, expose, layers, transparency, and GLY.
- `CheckProofEqns`: PASS; 749 proof modules, 1033 exports, 0 unaccepted.
- `check-layers`: PASS; 72 existing findings, 0 new.
- `check-gly-rules`: PASS; 20 rules, 0 failing findings; FaultX route has
  0 violations. No allow or baseline change.
- `bash scripts/precheck.sh .`: PASS; main and target base are 88c616d.
- `NEG=0 bash scripts/check-fgsa-claims.sh`: FAIL at the fixed Statements
  ORDER, before the compiled audit. Both exact imports are listed above.
- `NEG=0 bash scripts/check-fgsa-manifest.sh`: PASS; 1200 entries in 52
  modules; hashes match. The manifest has only 36 added lines.
- Seven-validator candidate: builds; its count and endpoint proofs pass.
  The full executable run returned no result after more than 11 minutes
  and was stopped (exit 143). This is not a passing non-vacuity test.
- Frozen Statements/Claims, FGSAClaims, and old WC proofs: no tracked diff.
- `git diff --check`: PASS. No commit, stage, or push was made.

Logs are in `.lake/wcg-*.log`. `wcg-check-build-final.log` contains the
full final gate run. The last import-only checks are in `wcg-imports.log`.

Final import cleanup: `lake build` PASS (4361 jobs). Targeted
`shake-report.sh --fail-on-new` PASS (14 modules, 0 NEW removals).
The remaining checker failure is the Statements ORDER registration.

### Resumed checkpoint: 2026-10-06

- Lead-approved ORDER entry added. No other checker or allowance changed.
- Removed an unused Fintype assumption from the Assembly wrapper. The
  claims build treats this compiler warning as an error.
- Full build, check-build (including checker-self-tests), layers, GLY,
  precheck, NEG=0 claims, and the 21-theorem axiom audit: PASS.
- Axioms: propext, Classical.choice, Quot.sound only.
- Logs: `.lake/wcg-resume-*.log`. Statement commit: `7d6a94f`.
- The same validated Lean tree is used for the component commit.
