# WC corruption growth: completed proofs and remaining integration

Branch: `wc-growth`. Continuation 3. Date: 2026-10-07.

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
There is no finality-liveness conclusion. The closed theorem passes against the installed proof modules.
The public theorem is not yet installed in Assembly.Root.

## Completed proof facts

- `wcg_retainedSeed` constructs the complete continuation WCSeed. Gates,
  nextHeads, and highSources use separate source and continuation indices.
  Signed rows and deterministic reads replay. HEAD receipts, certificate
  origins, and finite facts are rebuilt in rho.
- `wcg_empty_outputDomain` covers the exact public output domain, including
  reads after the horizon. It does not restrict reads to covered times.
- `wcg_empty_stateSafety` proves event-index S compatibility, monotonicity,
  and seed preservation. It maps each retained local prefix to a source
  prefix and preserves local index order.
- `wcg_empty_finalBelow` proves the cross-validator finality bound. Choose
  the least matching source prefix above the cut. Its earlier finality row
  is no later than a retained event already in the continuation prefix.
  The strict target/finality gap puts the service4 deadline before that
  event. Map the other reader from this deadline cut and apply source service4.
  No equality of global indices, empty-suffix FaultQ, or majority is assumed.
- `wcg_empty_inclusion` transfers actual retained proposals and all covered
  output reads. `wcg_growthOfOutputs` proves conditional available growth.
- `wcg_sourceLive` supplies the selected source's full live result.
  `wcg_nonemptyLive` supplies the vote-participation interval and the live
  continuation result. `wcg_emptyLive` discharges all source invariant,
  causality, service, and finalBelow producers for the empty branch.
- The exact public theorem `fgsa_weakContinuationGrowthClaim` passes in
  `.lake/wcg-c3-work/PublicClaimCheck.lean`, against the installed modules.
  It selects one witness with the closed `healing_hTimeClaim`, then joins
  the two continuation branches. It takes only p and G. There is no extra
  seed, invariant, service, inclusion, or H-time premise in the claim.
  Its axiom set is propext, Classical.choice, and Quot.sound.

## Exact remaining items

1. Public integration awaits the lead's import decision below. No
   mathematical fact remains missing for the companion claim. The checked
   theorem and exact unapplied patch are in PUBLIC_JOIN.md and PUBLIC_JOIN.patch.
2. Full bounded-source non-vacuity above one-third remains unproved.
   The short five-validator candidate has source faults 0 and continuation
   faults 2, with 5 < 3*2 and 2 < 3. Delta is 2; horizons are 0 and 1.
   For DeltaF 2 and gap 8, B_HF is 494, as checked in scratch. A bounded
   strong source therefore needs 248 public tick rounds and their deliveries.
   Exact missing facts: a complete 494-endpoint five-validator execution,
   Base₂, authentication including carried objects, linked/CStar data,
   collision freedom, synchrony, proposer recurrence, pending source duties,
   and FinalitySlashableBound for the retained continuation.
   The existing full four-validator witness does not prove these facts
   for five validators. This is more than an endpoint or count adjustment.
   Keep the cheap candidate. No unverified long trace replaces these proofs.

## Pending lead decision: two named root imports

The job rule says: "no new allow-list lines or layer exceptions without
recording them for the lead first (STOP that item)".

The requested change is exactly two additions to `ASSEMBLY_ROOT_IMPORTS`
in `scripts/check-layers.py`:

- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth`
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed`

Assembly.Root would import these modules and add the checked public theorem.
The patch also adds its axiom audit. The request was sent to the lead. There
has been no reply and no rule change. The patch passes `git apply --check
--unidiff-zero`. Do not apply it without the required decision.

## Validation and commit plan

- Full warning-free build: PASS (4366 jobs).
- All 91 component theorem audits: standard axioms only.
- Public theorem against installed modules: PASS; standard axioms only.
- Scoped import check: PASS (483 modules, zero new findings).
- Layers and `bash scripts/precheck.sh .`: PASS.
- Final check-build, separate GLY, and NEG=0 claims gate: PASS.
- CheckProofEqns: zero unaccepted exports. The API manifest has 1200
  complete entries in 52 modules, with matching hashes.
- Short candidate: PASS. Wall time 43.27 s includes the Lean slot wait;
  user CPU time was 2.03 s. It is not the full non-vacuity proof.
- Frozen Statements/Claims, FGSAClaims, original WC proofs, and the API
  manifest are unchanged. No new allow-list line or layer exception was applied.
- Source hashes: `.lake/wcg-c3-final-source-hashes.tsv`. Keep the Lean tree
  unchanged for the separate seed, empty-proof, and assembly commits.
  Each module has its own axiom audit. Use the full completed-tree validation
  for these separate commits, as at the prior checkpoint. Do not push.
- Logs: `.lake/wcg-c3-final-*.log`. Earlier failed checks found two private
  equation exports, an orphan next-module file, and one redundant import.
  All three causes were corrected before this final gate run.

## Proof plan used in continuation 3

1. Map retained ticks in both directions. Transfer the gate guard and HEAD
   path. Replay signed action rows and source/gate getters. Rebuild receipts.
2. Use complete local-list agreement for the empty branch. Map arbitrary
   local prefixes above each cut. Use the least source prefix to preserve
   the strict finality-service timing bound across different global indices.
3. Derive source slashing control and vote participation. Join the closed
   H-time witness with the nonempty and empty branches at the public root.
4. Check the full five-validator source requirement against build time.
   Keep the short candidate and list the full missing regime facts.
