# FG-SA outage continuation under (V), w2

Status: partial. The full companion claim remains unproved.
Branch: fgsa-outage-v. Base: 43733fe. No push.
The statement still has no FinalitySlashableBound premise.

## Code commits

- 5dd22552 Policy-only: register the OutageContinuation Statements module
- 53d311eb Add the outage continuation statement and initial proofs
- d0949303 Prove continuation HEAD coverage and frame adapters
- b6cded48 Prove outage source and exact carrier receipt adapters
- b280b43a Prove restored gate compatibility and local preservation
- 1eea0534 Prove inclusive continuation reads and audit all helpers

The policy commit changes only the approved ORDER line. The staged-work
commit also adds the missing claims-root and proofs-root imports. These
are additive assembly imports. They change no guard or frozen contract.
Direct imports replace unused broad imports. Typed audit targets retain
proof dependencies. The positive sleep-bound test uses the timing theorem;
the counterexample still uses decide. No new keep allowance was added.

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

## Proofs

The 27 w1 helper theorems remain. W2 adds 26 theorems:

- ContinuationFrame: actual frozen-witness walk coverage; live-root
  compatibility; walk membership; filter-to-HEAD compatibility; contested
  HEADs; marker HEADs; scoped-row HEADs; actual merged-pool batch coverage.
- ContinuationReceipt: exact-carrier receipt; receipt at the regression
  HEAD cut; short-horizon exclusion; earlier gate labels through relay;
  inclusive source cutoff; strict block stamps; frozen membership;
  pre-action source storage; original crossing source extraction;
  full-run compatible HEAD receipts at the actual pre-gate view.
- ContinuationGate: count from actual receipts; gateStep output retention;
  compatible fast writes; compatible live locks; compatible current sources;
  genuine-result ancestry; the assembled restored-gate theorem.
- ContinuationInduction: inclusive S, stable, confirmed, and F reads from
  a local event invariant, including horizon deliveries.

`outageV_restored_gate` needs current F compatibility, compatible scheduled
label-s HEADs, execution, no restart, CStar, root identity, full synchrony,
GST before v_s, and restored participation at v_s. It derives the receipt
and count facts. Honest HEADs may be strict ancestors of B or of F.

All 53 helper axiom checks pass. Their axioms are subsets of propext,
Classical.choice, and Quot.sound. No sorry, admit, or new axiom was added.
The exact theorem names and audit targets are in the
[axiom audit](../../Tests/OutageContinuationAxioms.lean).

No completed theorem uses FinalitySlashableBound. The full claim is open,
so this is not a claim that its remaining assembly needs no such premise.
Old saved results have no compatibility premise. Writes use the current
result. Empty, vetoed, and already-saved gates preserve the output.

## Open facts

- §3: assemble the uncontested frozen height witnesses and covering HEAD
  receipts at the scheduled clocked read. Crossing-source extraction,
  its inclusive cutoff, frozen membership, and merged-pool counts exist.
- §6: prove receiver F compatibility through v_s+Δ at the first regression
  from earlier-label gates. Then carry the exact marker forward and apply
  its frame protection at each later scheduled read.
- §§8–10: build the joint event/label induction. Extend original source
  history on actions and use it on deliveries. Seed from arming and the
  pre-expiry theorem. Supply the S/F invariant to the inclusive read adapter.
- Non-vacuity: a kernel OutageContinuationPrem inhabitant remains open.
  The existing full-sleep run still has 18 executable audits.

[OPEN.md](OPEN.md) gives the exact missing facts and theorem interfaces.
There is no lane Export for the unproved claim. The approved second policy change,
OutageContinuation/Export, and Shared/Claims wiring remain deferred.
No other guard or allow-list change was made.

## Non-vacuity and old reads

The 583cee0 parameters violate (V), by decide. The 168-event full-sleep
run satisfies (V) at equality and keeps B through horizon 30. It is
unchanged from w1. Its audits are not a kernel proof of the full premise.

The final old-read audit passes. It scans 8,747 constants in 469 active
modules. Its six old/finality readers and 185 height-only readers match
the unchanged baseline. No new old read needs a lead ruling.

## Validation

The final source snapshot passes the full --wfail build, layers, GLY
(including F-31), FGSA with negative controls and the old-read audit,
NEG=0 claims, API manifest, and all 53 helper axiom checks.
`bash scripts/check-build.sh` passes checks (a) through (j).
CheckProofEqns has no unaccepted exports and no Gen exports. The claims
unused-import check passes without a new keep allowance. The API manifest
has 1,189 entries in 52 modules, with matching hashes. All 36 checked
frozen source and guard files are byte-identical to 43733fe.

Logs: /tmp/outage-w2-final-build4.log,
/tmp/outage-w2-final-check-build2.log, /tmp/outage-w2-final-fgsa.log,
/tmp/outage-w2-final-claims2.log, /tmp/outage-w2-final-old-reads.log,
/tmp/outage-w2-final-manifest.log, and /tmp/outage-w2-final-shake2.log.
The normal shared throttle was used. No lake update, agent, review process,
throttle bypass, or push was used.
