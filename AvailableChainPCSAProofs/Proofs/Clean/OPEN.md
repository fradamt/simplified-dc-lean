# Clean lane W2a

Base: `ee51f4f`. Stage 1 only. No claim statement was changed.

Proved support:

- `AckStore`: decoded ack admission under the slot, root, and seat-cap checks;
  ack-pool preservation through every delivery and clock step.
- `AckRun`: ack-pool preservation between event indices without restarts;
  the after-ticks PC set at the freeze equals the strict pre-time PC set.
- `Shared/CleanPC`: CL4 count facts for the same label and later labels;
  strict score dominance from the Generic quorum inequality.
- `StepGate`: compatible PCs allow prefix lock writes; compatible live locks
  let the guard pass; compatible PC admission deletes no lock; a passed gate
  writes `GridCO.advance S X` to S.

These are exported by `Clean/Export`. They are not proofs of the open claims.

## OPEN facts

- C6 (`CleanInvariantClaim`): CL1–CL4 still need run-level count inputs.
  For each gate and next-label walk, prove forward and backward receipt
  membership, unchanged resolution of each common seat, and retained path
  membership. Then prove equal proposal/voter views and walk inputs at an
  honest slot. The label-zero case and the Vote/Ack/PC record steps are open.
  `StepGate` has only the store consequences of chain compatibility; it does
  not establish that compatibility from the previous `CleanInvariantAt`.
- C6 root clause: `roots` also requires compatibility with **every** honest
  HEAD of the previous label. CL4 only gives compatibility with results.
  A possible obstruction is n = 5, a = 1 at a faulty proposal: four HEAD
  seats on X (three honest), one honest HEAD on conflicting Y, then an honest
  ack quorum for X. A next-label root on X would conflict with Y. This is a
  count scenario, not a proved run counterexample. Establish why the model
  excludes it, or resolve the statement with the lead before proving C6.
- C3 (`PCDisseminationClaim`): prove that each honest handled ack before the
  freeze passes the receiver's slot and resolved-root checks and cannot hit
  the two-root seat cap. Include the carried-object handler cases. Prove that
  the target body is held and resolves to the same slot-s block, that
  first-per-seat selection keeps a quorum, and that a receipt has already
  assembled and installed the PC before the freeze. The freeze clock does
  not call `collectPCs`. Thus the old Shared `hKeep` premise also needs a
  reachable-store saturation fact: every collectable target is already held
  in the strict pre-freeze store. Preservation of an already-held PC is done.
- C5 (`AvailableMonotoneClaim`): prove S monotonicity, preservation of held
  PCs in stage 1, and prefix order of selected PC targets over time. Supply
  compatibility of the later target with the later S to Generic PCFloorMono.
- `CleanDisseminationClaim`: lift the N score gap through receipt and the
  next-label walk to HEAD coverage; lift the honest batch to result coverage.
- `PCSACleanSafetyClaim`: establish S/PC compatibility across nodes and times,
  plus the two monotonicity facts needed for C5, over the whole cut.
- `PCSACleanInclusionClaim`: prove equal honest HEADs at the proposal label,
  result = proposal at every honest gate, and persistence of its prefix in S
  and in the available output through the cut. The gate write fact is done.
- C9 (`StrongIncludedClaim`): needs Formation to produce the proposal's PC by
  the freeze, then prefix monotonicity of later selected PCs. Leave this to
  the Formation writer. Formation itself was not changed.

Do not fill these gaps by adding premises to any claim or by exporting a
conditional theorem as an unconditional claim.
