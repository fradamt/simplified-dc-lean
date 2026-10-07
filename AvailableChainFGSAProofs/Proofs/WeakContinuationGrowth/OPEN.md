# WC corruption growth: remaining open items

Root integration and its import policy are applied. Assembly.Root exports
`fgsa_weakContinuationGrowthClaim` and imports both growth Assembly modules.
The API manifest includes the additive declarations. The two named Root
import exceptions and the Statements-order exception are applied.
The frozen FGSAClaims field and the original WC interface are unchanged.

## Remaining non-vacuity fields (w5)

`Tests/WeakContinuationGrowthNonVacuity.lean` adds a closed partial pair.
It adapts the W1 duty-engine generator to five validators. The source has
248 tick rounds and horizon 247 = GST + B_HF, with Delta = DeltaF = 1
and gap 4. The continuation retains validators 0, 1, and 2. It has
horizon 248 and actual suffix ticks at time 248. Faults rise from 0 to 2.
The test proves 5 < 3*2 and 2*2 < 5.

Closed proofs cover both schedules, the nonzero bounded endpoint,
retained local agreement, the full seat map, linked and fresh committees,
no restarts, proposer recurrence, source participation, the source fault
cap, the liveness bound, and continuation participation.

The full conjunction of StrongRecoverySearchPrefix₂ and
CleanGrowthContinuation₂ remains open. `MissingFields` gives the exact
remaining obligations for this concrete pair:

- `sourceValid`: closed in w6 by `nvGrowth_source_valid`. The W1 proof is
  parameterized by the positive validator count. Generic replay, dependency,
  origin, carriage, and wire lemmas certify the real five-validator prefix.
  A checked opaque certificate retains all execution-validity fields.
- `sourceRoots`: closed in w6 by `nvGrowth_source_roots`. The generic
  W1 final-store table covers delivered and held full named proposals,
  including their ancestors. The opaque certificate retains this proof.
- `sourceSync`: closed in w6 by `nvGrowth_source_sync`. Generic W1
  receipt proofs supply both family synchrony clauses. The HEAD/proposal
  and row delays are one. The opaque certificate retains this proof.
- `continuationValid`: continuation Base₂.valid. ScheduleWellFormed is
  proved; the same delivery and signature fields remain open.
- `continuationRoots`: continuation Base₂.idealization.
- `continuationSync`: CleanGrowthContinuation₂.sync.
- `pending`: closed in w6 by `nvGrowth_pending`. The generic duty-free-round
  lemmas prove that time 247 has no emissions or deliveries. Both original
  source guards and family deadlines remain in the theorem.
- `accountable`: CleanGrowthContinuation₂.accountable,
  FinalitySlashableBound on the whole continuation.

`nvGrowth_complete_of_missing` constructs both full records from exactly these
fields. It does not prove that MissingFields is inhabited. Do not report
this test as a full non-vacuity proof. The earlier horizon-0 executable
candidate remains available as a short engine check.

## Reuse path (w6)

`GrowthGenerator` is in the existing non-vacuity test. TEST-USE forbids a
new import from one Tests module to another. The generic proofs therefore
stay in that file. No import policy or audit baseline is changed.

The W1 generator now has checked prefix proofs for every positive validator
count: `nvGen_prefix_execution`, `nvGen_prefix_roots`, `nvGen_prefix_sync`, and
`nvGen_prefix_accountable`. The source uses its fresh-only delivery generator.
The slot digest, five seats, endpoints, fault counts, and suffix remain.
Only source execution validity is added to the opaque certificate so far.
The other generic results do not yet close the remaining concrete fields.

Exact transfer work remains:

- Source roots and family synchrony must be retained by the certificate.
- Continuation validity needs full-state replay at retained delivery indices,
  including each carried honest signature's earlier retained emission.
- Continuation roots need coverage of all delivered bodies and retained
  stored bodies by the reference run's full named scope.
- Continuation synchrony needs retained receipt indices and the original
  post-acceptance receiver guard, with the same family deadline.
- Whole-run accountability needs every continuation FinalityBlock to be a
  reference FinalityBlock. The full reference generator has zero faults.
  Its slashing bound can then cover the two-fault continuation. A two-fault
  one-third bound is not used.
