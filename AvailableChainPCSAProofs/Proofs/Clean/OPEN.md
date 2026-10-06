# Clean lane W2a

Base: `92a4673`, on `31fa4d7`. Stage 1 only.
The only claim change is the approved r4.3a correction to `CleanInvariantAt.roots`.
It now requires compatibility with honest results, not arbitrary honest HEADs.

## Concrete blocker: C3 is false at slot zero

`AvailableChainPCSAProofs/Tests/ZeroSlot.lean` proves `refutes_C3`:
`¬ PCDisseminationClaim p`. This is a full run counterexample. It proves
`Clean₂`, `FaultsBelowQA`, and `StageOneFrame`, not only store behavior.
The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

Take one honest node, one seat, no faults, Δ = 1, and cut = horizon = 3.
The run has these six events, in order:

1. Tick at 0. The slot-zero proposer emits nothing.
2. Tick at 1. The node emits its slot-zero HEAD on genesis.
3. Deliver that HEAD at 1.
4. Tick at 2. The node emits its slot-zero ack on genesis.
5. Deliver that ack at 2.
6. Tick at 3. The ack pool has the ack. The PC set is empty.

The emitted ack quorum has size 1 = q_A. Delivery is strict: 1 < 2 and
2 < 3. The only label with e_j ≤ 3 is j = 0; its honest participation is
1 > 0. There are no proposal bodies, rows, restarts, or root collisions.
The proof checks schedule, delivery, signatures, committees, and frame.

`ackFor` permits this N target. `PC.wellFormed` requires `0 < slot` and a
non-genesis target. Thus the C3 conclusion cannot hold. A decision is
needed: restrict C3 to positive slots, or change the model's zero-slot
behavior. Neither change is authorized here. No such change was made.
Work stopped at this concrete blocker, as the continuation rule permits.

Formation has `slotPos`, so this counterexample does not refute its C3
store interfaces or Formation itself.

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
- C6 N-target helper: `StepPC.pcsa_clean_N_root` proves that the next
  root is below, and compatible with, the N target from the source bounds
  in r4.3a step (d). The run induction must still prove: the selected PC
  has slot ≤ i; earlier PCs are below the N target; same-slot PCs target
  it; live locks are below it. This helper is exported by `Clean/Export`.
- C3 (`PCDisseminationClaim`): **false**, as proved above. For the positive-slot
  repair, still prove that each honest handled ack before the
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

## Formation interfaces

- `hAckPoolMono`: discharged by `pcsa_ackPool_stateBefore_mono`, with
  `FormationPrem.base.noRestart`; the honest-node binder is unused.
- `hAckAdmit`: open. Need admission of every handled honest ack, including
  carried receipt, under the slot, resolved-root, and seat-cap checks.
- `hPCCollect`: open. Need resolution to the exact `N.erase` and preservation
  of the seat quorum by `firstPerSeat`, then assembly from that pool.
- `hFreezeKeep`: open. `pcsa_pcs_after_freeze` proves preservation of held
  PCs. The exact interface also needs saturation before the tick:
  `(collectPCs st).pcs ⊆ st.pcs` for the reachable pre-freeze store.

No open claim was exported as an unconditional theorem. AckStore now uses
constructor cases to avoid all 19 foreign match equation exports introduced
by the previous partial commit. The base W1 modules are unchanged.
