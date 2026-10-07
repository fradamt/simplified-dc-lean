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

- `sourceValid`: source Base₂.valid. ScheduleWellFormed is proved;
  DeliveryWellFormed (wire, deps, fresh) and UnforgeableSignatures
  (unforgeable and carried) remain open.
- `sourceRoots`: source Base₂.idealization, NamedRootCollisionFree.
- `sourceSync`: source Recovery₂.sync, family PartialSynchronyBy.
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
