# Open hypotheses of C8 ARM-healthy and C10 slow P1

`pcsa_armHealthy_of_claims` (C8, ARM-healthy) and `pcsa_slowP1_of_claims`
(C10, slow P1) in `Proofs/Assembly/Outage.lean` take these records as OPEN
hypotheses:

- `CleanCutChainItems` (`CutChain`, `Outage/CleanBridge.lean`), for C8 and C10.
- `CleanSlowItems` (`Statements/OutageItems.lean`), for C10.
  `pcsa_cleanSlowItems_of` gives it from `CleanCutItems` (`CutFacts`,
  `Outage/CutFacts.lean`).

The open fields are the HEAD facts at the pending labels: `CutChain.heads`
(a HEAD of label `i` with `v_i ≤ b₀` extends every honest result of `i − 1`)
and `CutFacts.pastCut` (the same with `e_{i−1} ≤ b₀`). They cover the
boundary case `v_r ≤ b₀ < d_{r−1}` of pcsa34-r4.3 §5.5 step 2. A
counterexample run refutes both as stated: the HEAD of label 2 of honest
node 3 at `t = 18` does not extend the result of label 1 of honest node 0
at `t = 20` (cuts 12 and 18). The run meets the C8 and C10 premises, and both
conclusions hold in it (vacuously), so only the proof step fails. The former
claims `CleanHeadsAbovePendingClaim` and `CleanHeadsPastCutClaim` are removed.

`CleanDisseminationPendingClaim` (M3, `Claims/Clean.lean`) is unverified.

A repair with a weaker cone claim is in review (tip-stability
`spec/drafts/pending/pending-cone-repair.md`). It lands on a separate branch.
