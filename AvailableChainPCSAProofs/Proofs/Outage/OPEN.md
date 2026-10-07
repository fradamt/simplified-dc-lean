# Open hypotheses of C8 ARM-healthy and C10 slow P1

`pcsa_armHealthy_of_claims` (C8, ARM-healthy) and `pcsa_slowP1_of_claims`
(C10, slow P1) in `Proofs/Assembly/Outage.lean` take these records as OPEN
hypotheses:

- `CleanCutChainItems` (`CutChain`, `Outage/CleanBridge.lean`), for C8 and C10.
- `CleanSlowItems` (`Statements/OutageItems.lean`), for C10.
  `pcsa_cleanSlowItems_of` gives it from `CleanCutItems` (`CutFacts`,
  `Outage/CutFacts.lean`).

The HEAD facts at the pending labels are in cone form (tip-stability
`spec/drafts/pending/pending-cone-repair.md`, with its review fixes):

- `CutChain.cone`: for `0 < i` with `e_{i−1} ≤ b₀`, a block below every
  honest HEAD of label `i − 1` is below every honest HEAD of label `i`.
- `CutFacts.bridge` (clean-gate successor): for `d_j ≤ b₀`, every honest
  HEAD of label `j + 1` extends the honest result of label `j`.

They replace the former fields `CutChain.heads` (a HEAD of label `i` with
`v_i ≤ b₀` extends every honest result of `i − 1`) and `CutFacts.pastCut`
(the same with `e_{i−1} ≤ b₀`). A counterexample run refutes the former
fields in the boundary case `v_r ≤ b₀ < d_{r−1}` of pcsa34-r4.3 §5.5 step 2:
the HEAD of label 2 of honest node 3 at `t = 18` does not extend the result
of label 1 of honest node 0 at `t = 20` (cuts 12 and 18). The run does not
refute the cone or the bridge. The clean lane owns their proofs.

The other fields of `CutChain` are `nonempty`, `chain` and `dis` (the
statements of `CleanResultsNonemptyClaim`, `CleanResultsChainPendingClaim` and
`CleanDisseminationPendingClaim`); `CutFacts` adds `same` (CI (i)) and `rows`
(`LeaseBelowRecordClaim`). `CleanDisseminationPendingClaim` (M3) is
unverified. C8 uses `dis` at the label after the PC slot.
