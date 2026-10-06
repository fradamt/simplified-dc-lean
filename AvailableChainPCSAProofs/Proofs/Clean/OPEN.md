# Clean lane W2a

Base: `92a4673`, on `31fa4d7`. Stage 1 only.
Claim changes: the approved r4.3a correction to `CleanInvariantAt.roots`
and the approved `0 < s` premise of `PCDisseminationClaim`.
It now requires compatibility with honest results, not arbitrary honest HEADs.

## Resolved statement defect: C3 at slot zero

`AvailableChainPCSAProofs/Tests/ZeroSlot.lean` proves `refutes_unrestricted_C3`:
`¬ UnrestrictedPCDisseminationClaim p` (the former statement). This is a full run counterexample. It proves
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
non-genesis target. The lead approved `0 < s` for C3. The test now preserves
the former statement and proves `positive_slot_excludes` for this witness.
Positive-slot C3 is still open; this test does not refute it.

Other slot statements were checked. No further statement change is needed:
- Formation already requires `FormationPrem.slotPos`.
- CleanDissemination requires prefix coverage, not a PC at slot zero.
  The genesis target is below every block.
- StrongIncluded requires an emitted honest proposal. The slot-zero
  proposal duty emits nothing.
- PCSnapshotStamp is equality of sets, including empty sets at slot zero.

Proved support:

- `Collect`: seat selection preserves all input seats without repeats; a pooled
  quorum assembles and collects the exact resolved target. Collection leaves
  a saturated store; collection of a saturated store changes nothing.
  `Saturation` proves this at every event state and discharges hFreezeKeep.
  Run-level target receipt still needs a proof.

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

CI read-step support is exported:
- `StepVote`: an honest positive-slot HEAD extends its duty root; a block
  below that root is below the HEAD. A slot-zero honest HEAD is genesis.
- `StepAck`: an honest ack's full target is held, has the exact slot, and
  passes holdsN in the duty state. Its block is in the collision scope.
These do not yet provide the joint CI record or the composing induction.

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
- C3 (`PCDisseminationClaim`), restricted to positive slots: admission of
  each handled honest ack is proved by `pcsa_honest_ack_admitted`, including
  the carried-object handler cases. Still prove that the target body is held
  before the freeze. `TargetCollect` proves exact lookup once it is held.
  `Collect` proves first-per-seat quorum preservation and exact assembly.
  `Saturation` proves every collectable target is already held in each
  reachable store. `pcsa_collectPCs_after_freeze` closes the Shared hKeep
  and Formation hFreezeKeep interfaces.
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
- `hAckAdmit`: the exact interface is `pcsa_formation_ack_admit`; its
  base theorem is `pcsa_honest_ack_admitted`. Use
  `FormationPrem.base` and the lower receipt-time bound. The theorem proves
  admission of direct and carried honest acks. The upper bound is unused.
- `hPCCollect`: `pcsa_formation_collect_of_held_body` proves the exact
  interface from one remaining fact:
  `∀ y ∈ rho.honest, N.erase ∈ (stateBeforeTime E rho (freezeTime s) y).st.base.blocks`.
  Proposal slot equality, exact root lookup, quorum preservation, and
  assembly are proved. The target-body receipt fact is still open.
- `hFreezeKeep`: the exact interface is `pcsa_formation_freeze_keep`; its
  base theorem is `pcsa_collectPCs_after_freeze`, using
  `FormationPrem.base.valid.toScheduleWellFormed`, `base.noRestart`,
  `base.delta`, and `freezeTime s < gateTime s ≤ horizon`.
- `BodyPersistence`: FG and base bodies persist through every delivery and
  clock. Exact bodies persist between run indices without restarts. Exported.
- `TreeReceipt`: reachable stores have identical base and erased FG body domains.
  The stage-1 full tree retains every stored FG block. These facts are exported.
- `BodyAdmission`: a body with valid rows for its immutable parent cannot
  be excluded in stage 1. A fresh, dependency-ready, well-formed body
  passes admission once the receiver slot is large enough. The run receipt
  proof must establish that these conditions hold on the actual delivery.

No open claim was exported as an unconditional theorem. AckStore now uses
constructor cases to avoid all 19 foreign match equation exports introduced
by the previous partial commit. The base W1 modules are unchanged.
