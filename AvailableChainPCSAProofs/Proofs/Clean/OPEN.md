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
Positive-slot C3 is now proved; this test does not refute it.

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
  Exact run-level receipt is proved by `BodyReceipt`.

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
  membership. `CommonResolution` now proves equality for one signed HEAD
  resolved at two indexed honest post-clock reads. `HeadPersistence` proves
  exact pooled HEAD preservation through each step and between indices.
  `HeadStamps` keeps the full receipt-stamp prefix between indices and
  keeps an existing first stamp lookup unchanged.
  `HeadReceipt` proves stamp keys, first lookup, exact receipt-time
  preservation, direct/carried stamp origin, and acceptance before a public
  cutoff. `HeadTransport` proves actual handler admission as an exact HEAD
  or a capped seat, and transports both outcomes into later late
  denominators with strict stamps. Cross-node relay membership and body
  stamp transport are still needed for both denominators.
  Then prove equal proposal/voter views and walk inputs at an
  honest slot. The label-zero case and the Vote/Ack/PC record steps are open.
  `StepGate` has only the store consequences of chain compatibility; it does
  not establish that compatibility from the previous `CleanInvariantAt`.
- C6 N-target helper: `StepPC.pcsa_clean_N_root` proves that the next
  root is below, and compatible with, the N target from the source bounds
  in r4.3a step (d). The run induction must still prove: the selected PC
  has slot ≤ i; earlier PCs are below the N target; same-slot PCs target
  it; live locks are below it. This helper is exported by `Clean/Export`.
- C3 (`PCDisseminationClaim`): proved for positive slots and exported as
  `pcsa_pcDissemination`. `BodyReceipt` proves an earlier accepting body
  origin, immutable-parent row validity, exact relay before its deadline,
  and exact body membership at every honest node before the freeze.
  Ack admission, pool transport, exact lookup, quorum assembly, and freeze
  preservation discharge all C3 store premises. The claim needs no extra
  premise. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
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
- `hPCCollect`: discharged by `pcsa_formation_collect`. `HonestBody`
  proves immutable-parent row validity at the emitted proposal, then exact
  admission and preservation at every honest receiver before the freeze.
  `pcsa_formation_body_before_freeze` supplies the full named proposal body.
  No extra hypothesis remains in this interface.
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

## Continuation 4 plan (2026-10-06)

Validated and committed `bd73be1`. Main is `88c616d`; keep this branch base.
No rebase. C3 and the four Formation store interfaces are complete.

C6 receipt steps, with a commit after each completed module:
1. Preserve the exact HEAD receipt stamps through clocks and deliveries.
   Prove that stored HEADs have stamp entries. Use these facts to keep the
   first receipt time when the pool grows.
2. Prove HEAD stamp origin at a direct or accepted proposal-carried handler.
   Convert a stamp below a public cutoff into acceptance before that cutoff.
3. Relay each early HEAD before the late deadline. A receiver retains the
   exact HEAD or two distinct HEADs of its seat. Transport both cap witnesses
   back to the source denominator. Prove exact body receipt and stamp bounds
   for the resolved support HEADs with `BodyReceipt`.
4. Apply CL1–CL4 to these actual counts and `CommonResolution`. Then prove
   the Vote/Ack/Gate/PC record steps and compose the label induction.

### Pending-label targets after C6 (M1–M4)

The outage writer owns the claim statements on `pcsa-w3-outage`.
Do not prove these targets now. The following supply map is planned; a
module or lemma marked planned is not yet available.

- M1, results non-empty for `earlyTime j ≤ b₀`: the planned gate result
  existence lemma in StepGate uses the honest early HEAD batch,
  `Clean₂.labels`, receipt transport, and the majority walk from genesis.
  Apply it to the pending label with delivery only through `b₀`.
- M2, CI HEAD/result chain at pending labels: StepVote's
  `pcsa_honestHead_extends_root` and the planned CL2 run transport supply
  HEAD extension. The planned StepGate batch lemma supplies result extension
  and compatibility. These facts need `earlyTime j ≤ b₀`, even if the gate
  is after the cut; `CleanInvariantClaim` alone has the stronger gate bound.
- M3, `CleanDisseminationPendingClaim`: StepPC's `pcsa_clean_N_root`,
  `CommonResolution`, `HeadPersistence`, and the planned N-score receipt
  transport supply next-label HEAD coverage. The planned StepGate batch
  lemma supplies result coverage. Keep the pending delivery boundary.
- M4, store items through `b₀`: the planned event induction for CI supplies
  PC chain/result compatibility, lock origin/keep/write, and S origin/order
  through the cut. `BodyPersistence` and `HeadPersistence` supply exact
  pool preservation. Do not derive the whole cut from a CI bound
  `t < voteTime (j + 1)` without a separate pending-store argument.

### Receipt continuation after `a3f0e4f`

`HeadReceipt` closes step 2 for HEAD timestamps. The six public facts are
`pcsa_head_stamp_keys`, `pcsa_head_stamp_lookup`,
`pcsa_head_stamp_stateBefore_eq`, `pcsa_process_head_stamp_origin`,
`pcsa_head_stamp_source`, and `pcsa_head_accepted_before`.
The last fact uses a public cutoff and the existing schedule/clock laws.

The next admission step is checked in scratch: a direct or proposal-carried
HEAD handled from the slot start to its gate leaves either the exact HEAD
or equivocation evidence. Lift this outcome to the later indexed state,
and retain both cap witnesses with their strict late stamps. For a faulty
HEAD accepted before the vote duty, derive that its acceptance is at or
after its slot start from the actual admission guard. Do not assume that
all early support HEADs were emitted honestly at the vote duty.

Then prove the body stamp bound for early resolved HEADs. `BodyReceipt`
already provides exact body relay and preservation; its earlier body
origin alone does not identify the first receipt stamp's time.

Ownership check for HeadReceipt: the first compiled version generated six
foreign `admitBlock` matcher exports. Use explicit Boolean constructor
cases for the key invariant and a native parent-match hypothesis for stamp
origin. This removes all six exports. The explicit equation check passes with
zero unaccepted exports. Owner modules and the baseline are unchanged.

### Local denominator transport (2026-10-07)

`HeadTransport` supplies `pcsa_handled_head_late_or_cap`: a direct or
accepted proposal-carried HEAD handled within its receipt window enters
the later late denominator, or both copies of its capped seat do.
`pcsa_head_before_cut_mem_late` and `pcsa_cap_before_cut_mem_late` retain
the exact copies with their first stamps. `pcsa_head_receipt_window`
derives the admissible store slots from the actual delivery event.
All eight facts are exported. They do not establish cross-node delivery.

Next for C6: derive the slot-start lower bound for an actual accepting
HEAD handler, including faulty HEADs accepted before the vote duty.
Use `pcsa_head_accepted_before`, strict relay, and the local denominator
transport to prove forward and backward count membership. Prove the
corresponding body stamp bound and exact resolution after body relay.
Then supply retained paths, proposal/voter view equality, CL1–CL4 run
inputs, and the four record steps. No run-level claim is closed by these
local transport facts alone.
