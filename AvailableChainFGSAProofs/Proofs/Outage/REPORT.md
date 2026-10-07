# FG-SA outage continuation under (V)

Status: partial. The companion is stated. Its full proof and Export are open.
Base: 43733fe. Branch: fgsa-outage-v. No commits and no push.
The required claims check is blocked by the new Statements ORDER registration.
That guard item was recorded and left unchanged under the task's hard rule.

## Exact companion

`Claims/OutageContinuation.lean` defines `OutageContinuationClaim p`.
It quantifies over every finite validator type V, codec c, environment E,
run rho, mode fast, times T, b₀, b₁, and row delay ΔF.
Its premise `OutageContinuationPrem` has exactly these fields:

- `pre`: `HealthyPrefix₂ p c E rho b₀ ΔF`, including Base₂ and acceptance relay.
- `sleepy`: the unchanged pre-b₀ sleepy inequality from Outage₂.
- `order`: `0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon`.
- `lag`: `T + (if fast then 4*p.Δ else L p - 3*p.Δ) ≤ b₀`.
- `lengthV`: `b₁ - b₀ + (b₀ - 6*p.Δ) % (4*p.Δ) ≤ L p`.
- `fastPart`: the unchanged pre-b₀ high-participation field from Outage₂.
- `sync`: full-run `PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)`.
- `gst`: `E.t_GST ≤ b₁`.
- `partAfter`: `faulty.card < awakeHonest(t).card` for `b₁ ≤ t ≤ horizon`.

Here `L p = (4*(p.k : Time)-1)*p.Δ`. There is no eta budget and no
participation condition on [b₀,b₁). There is no FinalitySlashableBound.

The conclusion is: for every honest x and block B below
`S_at p c E rho (timeIdx rho T) x`, every honest y and `b₀ ≤ t ≤ horizon`
satisfy all four facts:
`B ⪯ S_at(...,timeIdx rho t,y)`, `B ⪯ stable_y(t)`,
`B ⪯ confirmed_y(t)`, and `B ∥ F_at(...,timeIdx rho t,y)`.
All reads are inclusive.

## Completed proofs

- `ContinuationTiming`: existence of the first restored label; (V) iff
  `r ≤ j+K`; restored HEAD and old-gate bounds; all three boundary identities;
  the zero-endpoint arming premise; source and first-regression relay bounds.
- `ContinuationInduction`: the joint pre-expiry induction with endpoint at
  most expiry; an arming adapter with an independent induction endpoint.
  The old induction and arming proofs are unchanged.
- `ContinuationReceipt`: original acceptance for every source-path vertex;
  full-run path coverage at an inclusive source cutoff; active path coverage
  with compatible F, including a HEAD target strictly below F.
- `ContinuationFrame`: all maximum-height contest carriers extend B;
  every contested filtered block is compatible; compatible high entries and
  taller carriers extend B; receipt gives the justified-height lower bound;
  a contest supplies a stored carrier; the three marker frame cases;
  the scoped-row instantiation at a real event cut.
- `ContinuationGate`: the disjoint-seat denominator count; the terminal
  majority test; compatible-result rejection; the gate theorem for compatible
  honest targets; preservation by advance followed by normalization.

These are 27 intermediate theorems. They do not prove the full companion.
Their axiom audit uses only propext, Classical.choice, and Quot.sound.
No new axiom, sorry, or admit was added. None consumes FinalitySlashableBound.
Whether the remaining assembly needs that bound is not claimed.

## Non-vacuity

`OutageContinuationSleep.lean` reads the 583cee0 fixture design without merging
that commit. Its parameter check proves `¬ OutageLengthV p 17 24` by decide:
`24-17+((17-6) mod 4)=10 > 7`.
The new run restores at 21. It has n=4, a=1, K=2, delta=1, and 168 events.
All honest nodes sleep on [17,21). Condition (V) holds at equality.
All 18 executable audits pass. B is non-genesis at T=10. Both outputs retain
B and F stays compatible through time 30. The two length proofs have no axioms.
The executable audits are not a kernel proof of the entire regime predicate.

## Open items and guards

[OPEN.md](OPEN.md) states the exact missing run facts and guard routes.
The remaining work is the uncontested HEAD producer; first-regression
F history and exact-carrier receipt; run batch adapter; and joint induction
with inclusive output reads. No incomplete theorem is exported.

The API manifest adds only the new declarations. Its existing entries and
exception prose are unchanged. Its check reports 1189 entries in 52 modules,
with complete matching hashes. No manifest allowance is needed for additions.
The frozen FGSAClaims, frozen Statements/Claims files, existing outage claims,
frozen API file, and frozen API hash remain byte-identical.

## Validation

Touched builds pass with `--wfail`. All intermediate theorem axiom checks pass.
The full default build passes after rebuilding stale artifacts from the prior branch.
CheckProofEqns reports zero unaccepted exports and zero Gen exports.
check-layers reports zero new findings. check-gly-rules passes, including F-31.
The required `bash scripts/check-build.sh` passes checks (a) through (i).
Its checker self-test (j) fails because the claims subprocess exits on the
missing ORDER registration. NEG=0 fails on the same two MODULE ORDER findings.
No guard allowance was added to make these checks pass. No commit was made.

Validation logs are in `/tmp/outage-v-final-touched.log`,
`/tmp/outage-v-final-eqns.log`, `/tmp/outage-v-final-gly.log`,
`/tmp/outage-v-final-layers.log`, `/tmp/outage-v-check-build-final.log`,
`/tmp/outage-v-claims-final.log`, and `/tmp/outage-v-manifest-check.log`.
