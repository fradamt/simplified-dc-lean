# Outage continuation under (V)

The companion claim is stated, but its full proof and lane Export are open.
No slashing-bound premise was added. All completed modules compile.

## Guard needs recorded for the lead on 2026-10-07

1. Add `OutageContinuation` immediately after `Regimes` in `ORDER` in
   `scripts/check-fgsa-claims.sh`. This registers the new Statements module.
   Its only Statements imports are `Regimes` and `Reads`, both earlier entries.
   Without this registration, NEG=0 stops with two `MODULE ORDER` findings.
   The full build check's claims-pool self-test stops for the same reason.
   Approval was requested. No guard or allow list was changed.
2. Select an exact lane Export route. The current rules permit
   `Proofs/OutageContinuation/Export.lean` to import `Claims/OutageContinuation`,
   but prohibit that lane from importing the existing Outage proofs.
   A possible route is to allow that Export to import only the new
   `Outage/ContinuationTiming`, `ContinuationInduction`, `ContinuationReceipt`,
   `ContinuationFrame`, and `ContinuationGate` modules, plus the eventual
   joint-induction module. No exception was added. No empty Export was added.
   Claim-to-claim implications must remain in `Proofs/Shared/Claims.lean`.

The normal Lean wrapper ran with approved sandbox escalation. It used its
shared throttle. No throttle bypass was used. The prior lock issue is closed.
The API manifest was regenerated and checked. Its old entries and exception
prose are unchanged. New entries need no frozen-manifest allow lines.

## Exact remaining proof facts

### Paper §3: uncontested HEAD coverage

At an honest label-s HEAD cut, with s at least r+1, prove
`B ⪯ headVote p st s` from all label-(s-1) honest HEADs extending B,
restored participation, scoped source history, compatible F and live locks,
and `controls.contest = false`.
For every child on the live-root-to-B path, produce a member W of the actual
frozen voter set with that child below W and `controls.lo ≤ heightView(W).h`.
An old source at time `e_(s-1)` must be allowed. Prove its event-cut bound
and F compatibility through the receipt cut. `outageV_path_coverage` now
supplies the transport for that inclusive cutoff. The score, raw-denominator,
frozen-membership, and dominated-walk instantiations are still missing.

### Paper §§4–6: HEAD reads and the first regression

`outageV_contested_frame_from_rows` proves compatibility of all filtered
blocks. Connect this to the actual HEAD walk and the compatible live root.
`outageV_marker_frame` proves the three later frame cases for any store subset.
Connect these cases to later HEAD reads.

At the first regressed label s, prove compatibility of each receiver's F
through `v_s + Δ` using only gates with labels below s. If its final F is
below B, apply `outageV_path_coverage` to the carrier from
`outageV_contest_carrier`, using the actual source cut at v_s.
Recover the same admitted FG carrier, with its justified-entry identity,
at every receiver before `v_(s+1)`. The transport and active-path lemmas now
exist. The run-specific F-history and exact-carrier identity adapters do not.
If the relay deadline is beyond the horizon, exclude the next HEAD and gate
that would consume the marker. Do not assume receipt beyond the horizon.

### Paper §7: the restored batch at an actual gate

Instantiate `outageV_gate_of_compatible_batch` at `actView (clockPre ...)`.
Its remaining inputs are exactly `hH`, `hraw`, `hfault`, `hpart`, `hclean`,
and `htargets`: all awake honest seats are late; clean support is late;
the late complement has at most a seats; a is below the honest-seat count;
honest clean seats do not equivocate; their resolved targets are compatible
with B. Derive these from the run, the restored HEAD history, and receipts.
`outageV_active_path_of_coverage` now permits targets strictly below F.
The existing `fgsa_gate_batch_premises` cannot be used unchanged: it requires
HEAD coverage of B and F. The new local count needs only compatibility.

### Paper §§8–10: event induction and public reads

Use the passed current result to extend honest source history and lock-write
compatibility. Use original emission indices and the retained-finalization
carrier from `PersistenceHistory` to extend F compatibility on delivery.
Old saved results may conflict with B; do not assume all saved results are
compatible. They affect renewal, but each write uses the current passed result.

Build the joint event/label induction with these fields: S covers B; F and
live locks are compatible with B; honest source history is compatible;
restored HEADs cover B until the first regression and are compatible later;
the first-regression marker has its deadline and receiver receipt facts.
Seed it with `outageV_arming_prem` and `outageV_armed_to_expiry`.
Derive the inclusive public reads, including deliveries at the horizon,
and prove `OutageContinuationClaim` without an extra continuation premise.

## Non-vacuity scope

The 583cee0 parameters violate (V), by a kernel `decide` proof.
The new 168-event run satisfies (V) at equality and has full honest sleep
on [17,21). Its 18 executable audits pass through horizon 30.
The audits include the run premises, relay, and both outputs. A single kernel
inhabitant of `OutageContinuationPrem` has not been constructed.
