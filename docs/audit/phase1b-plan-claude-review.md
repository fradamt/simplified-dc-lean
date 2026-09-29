# Plan 1b review (Claude), 2026-09-29

Subject: `available-chain/docs/plans/2026-09-29-phase1b-instances.md` at
commit `0d8d995` (main). This review is read-only. The Astra audit runs
separately.

**Verdict: PASS WITH FIXES.** There are no BLOCKING findings. There are 3
MAJOR and 13 MINOR findings. The three premises that the survey changed are
correct, with one exception: finding 4 (L*) is false. Risk R1 is not a real
risk. Every caller that relays a HEAD of a faulty seat already has an
"`∨ equivocates`" outcome. But the WindowMargin lemma set in Task 1 Step 5
cannot discharge those callers. As written, the plan makes the implementer
stop at R1 for a case that has a known fix.

Lean check (scratch worktree, now removed): the plan's Grid CO `excludes`
(Task 1 Step 1, verbatim) is inert under `process`. It uses only `propext`,
`Classical.choice` and `Quot.sound`. The L* refusal in M3 is reproduced:
`process` leaves the state unchanged, and `processed = false` stays.
Command: `lake env lean ReviewCheck.lean` on cloned oleans of `0d8d995`. It
gave no errors, and a control `example` with a false statement failed as
expected.

## 1. Premise checks

```text
┌───┬───────────────────────────────────────┬──────────┬──────────────────────────────────────────┐
│ # │ Premise                               │ Result   │ Evidence                                 │
├───┼───────────────────────────────────────┼──────────┼──────────────────────────────────────────┤
│ 1 │ No contract change: regimes have no   │ CORRECT  │ git diff 1a3f73a^1..1a3f73a removes      │
│   │ acceptedRelay; relay is handler-call  │ (1 minor │ acceptedRelay from Sleepy, Outage,       │
│   │ with exemption since 588d666          │ imprec.) │ Recovery (Generic/Regimes.lean) and      │
│   │                                       │          │ StrongArmed; eec0f94 removes it from     │
│   │                                       │          │ QuorumRecoveryRegime. 588d666 has 4      │
│   │                                       │          │ `P.excludes` premises in Conditions.     │
│   │                                       │          │ Today Conditions.lean:104-151. See m1.   │
│ 1b│ Lock treats ADDED lines as            │ CORRECT  │ CatalogLock.lean diff: `breaking` only   │
│   │ non-breaking                          │          │ for REMOVED/CHANGED; --check exits 0     │
│   │                                       │          │ with "additions only"; --write needs     │
│   │                                       │          │ --allow-changes only when breaking.      │
│ 2 │ SA-PC has no permanent refusal at     │ CORRECT  │ SAPC Handlers.lean: receiveHead refuses  │
│   │ the processed level                   │          │ only a future label (:12); base refusals │
│   │                                       │          │ act on `base` (:16); PC refused only     │
│   │                                       │          │ before pcEnvelopeReady, whose parts are  │
│   │                                       │          │ wire (pcWellFormed), deps (pcPaths) or   │
│   │                                       │          │ time; after ready, witnesses are         │
│   │                                       │          │ archived, so pcValid holds. Proposal     │
│   │                                       │          │ refusals of GridCO.admitProposal are     │
│   │                                       │          │ time, deps, wire or already-processed.   │
│ 3 │ Grid CO/SA: two permanent HEAD        │ CORRECT  │ Protocol.lean:300-309. Proposals have no │
│   │ refusals; excludes exact, disjoint    │          │ permanent refusal (processed is          │
│   │ from processed                        │          │ block-level). See m5, m13.               │
│ 4 │ L*: one permanent refusal (third      │ FALSE    │ M3.                                      │
│   │ equivocation)                         │          │                                          │
│ 5 │ Eligible and run extension to 1c      │ SAFE     │ Section 3 below.                         │
└───┴───────────────────────────────────────┴──────────┴──────────────────────────────────────────┘
```

**Is `excludes` "permanent refusal" as the framework defines it?** The model
docstring (`AvailableChainModel/Generic/Run.lean:83-85`) says: "the node
rejects it now and in every later state". `HooksSound`
(`AvailableChainFramework/Hooks.lean:31-50`) checks only soundness:
`excludes_inert` and `excludes_stable`. Completeness ("covers every
permanent refusal") is design text only (§2 E4). RelayFeasible in plan 1c
will be its first consumer. The Grid CO definition is sound. `admitVote` is
the only way for a HEAD to enter `votes`: the direct delivery and the fold
over carried raw HEADs both use it (`Protocol.lean:311-325`), and
`clock_votes` shows that `clock` does not change `votes`. The old-label test
stays true because `now` is monotone on a valid run. The equivocation test
stays true because `votes` only grows. So an excluded HEAD is never accepted
later. The definition is also complete for every object that can be
accepted. The other HEAD refusals are a future label (temporary) and
`o ∈ votes` (already processed).

## 2. Findings

### MAJOR

**M1. Task 1 Step 5 and R1 (plan:212-222, :375-378): the WindowMargin
lemma set cannot discharge two callers.** `head_not_excluded_before` needs
`heq` (the seat does not equivocate). Two callers relay a label-`r` HEAD of
an arbitrary seat, so they cannot supply `heq`:

- `CrossView.lean:84`, inside `synchronous_accepted_head_before`
  (`:58-85`), through `synchronous_receipt_before`;
- `ProposalViewRelay.lean:91`, inside `stored_head_before_ready_proposal`
  (`:67-99`), through `handled_before_proposal_of_ready`.

Both conclusions already have the "`∨ equivocates`" outcome, so a proof
exists. Let the reader exclude the HEAD at a time `X` with
`X ≤ cutoff ≤ gateTime r < proposalTime (r+2)`. Then the old-label test is
false, so the reader already holds two label-`r` HEADs of seat `i`, stored
before `X`. For CrossView, their stamps are `< X ≤ cut`, so they are in
`stampedVotes (stateBeforeTime read) r cut`. Use
`stored_vote_stamp_before_cut` and `equivocates_mono`. For
ProposalViewRelay, `votesAt` is monotone up to `proposalTime (r+1)`.

Fix: add a WindowMargin lemma, for example `head_excluded_before_equivocates`
(`excludes st ⟨.seat r i, .head x⟩ = true`, with `st` the reader's state
before `u ≤ proposalTime (r+2)`, implies `equivocates (votesAt st r) i`).
Also add an explicit case split in the two callers before the call to
`accepted_head_receipt_before`. Change R1 from "stop and rule" to "known
discharge". I searched all callers of the 5 lemmas and found no caller that
relays a faulty HEAD without the "`∨ equivocates`" outcome. The only honest
caller (`ClockBounds.lean:176`) uses `honest_not_equivocating_at_event`
(`Votes.lean:375`).

**M2. Task 1 Step 4 (plan:204-211): "exactly the deadline that the lemma
passes to `hnet.relay`" is not one time.** Two lemmas choose the branch
inside the proof, from a disjunction premise. The branch after GST uses
`max t E.t_GST + E.Δ`, and the healthy branch uses `t + E.Δ`. The two
lemmas are `synchronous_receipt_before` (`CrossView.lean:28-36`) and
`handled_before_proposal_of_ready` (`Proposals.lean:114-122`). One premise
at one deadline cannot serve both branches. Also,
`handled_before_proposal_of_ready` has no `ExecutionValid` or
`ScheduleWellFormed` premise (`ProposalRelayReady`, `Windows.lean:138-141`).
Thus it cannot move non-exclusion back from its cutoff to the deadline with
`excludes_stable`.

Fix: use the premise
`∀ u, u ≤ <cutoff> → (gridCO p).excludes (stateBeforeTime u reader) o = false`.
The cutoff is `cut` or `proposalTime s`. This form needs no stability
argument, the deadline is at most the cutoff in both branches, and M1's
case split discharges it at the callers.

**M3. Finding 4 (plan:50) and Task 2 Step 1 (plan:236): L* has a second
permanent refusal, for proposals.** For a proposal, L* `processed` is wire
membership `o ∈ st.proposals` (`LStar/Model/Protocol.lean:314-315`).
`admitProposal` refuses when `b ∈ st.blocks` (`:283`). A faulty proposer
can sign two well-formed wires with the same block and different raw lists.
An honest reader that stored the block from the first wire refuses the
second wire for good, and never processes it. Such a run is valid:
`DeliveryWellFormed` is met, and the faulty key signs freely. The Lean check
confirms both facts. The plan's L* `excludes` is "equivocation, false
otherwise", so it misses this refusal. This violates design §2 E4 ("must
report through `excludes`"). `HooksSound` still holds, and L* has no claim
proofs, so no proved result is wrong. But finding 4 is false, and a 1c
RelayFeasible for L* would fail.

Fix: add the clause `o ∉ st.proposals ∧ b ∈ st.blocks` for a proposal wire,
and an `excludes_proposal_iff` test in Task 2 Step 2. Grid CO and SA-PC do
not have this refusal, because their `processed` for a proposal is
`blockKnown` (block-level).

### MINOR

- **m1** (plan:47). `AcceptedObjectRelay` also has two uses outside the
  SA-PC adapters, and neither is a regime field:
  `healthyPrefix_acceptedRelay` (`GridCO/Proofs/HealthyPrefix.lean:93-95`,
  which moves to the Kit) and Counter (`Registry/CounterRun.lean:470`). The
  conclusion "no contract change" stays correct.
- **m2** (plan:131, :150). The Kit namespace is `AvailableChain.Framework.Kit`
  (`Kit/Core.lean:7`), not `AvailableChain.Kit`. The two
  `block_preceq_trans` statements are different: the Kit version uses
  `Block.Preceq` (`Core.lean:13-14`), and the Map version uses
  `Block.preceq … = true` (`Map.lean:25-28`). The "keep both" rule may
  apply.
- **m3** (plan:128). `CheckFrameworkAxioms.lean` imports only Framework and
  Registry (`:1-2`). No module imports `AvailableChainEngineV2`, so adding it
  to `libraries` alone leaves it unchecked, and no error shows this. Add
  `import AvailableChainKit` and `import AvailableChainEngineV2`.
- **m4** (plan:149). The moved files now import Grid CO modules
  transitively (`EngineClock`, `RunPrefix` and `ProtectionInduction` import
  `GridCO.Proofs.Execution`, which imports `History`). An importer that
  changes to the Kit path can lose these transitive imports. Allow the
  implementer to add a Grid CO import, with no proof change.
- **m5** (plan:203). With the new `!processed` conjunct, `excludes_stable`
  must keep `o ∉ votes`. That needs the old-label test at every later
  state, which holds only because `now` does not decrease on a valid run.
  `stateBefore_stable` (`GridCOHooks.lean:52-57`) needs the property to hold
  after every `clock st t`, for any `t`. So it cannot prove this. State in
  the plan that the proof needs a variant indexed by the run (the clock step
  gets `now` monotonicity from `ScheduleWellFormed`). This is not a stop
  condition.
- **m6** (plan:203). `engineClockx` is not necessary after the change,
  because `engineClock` (`GridCO/Proofs/ClockBounds.lean:48`) is already
  `ClockLaws (gridCO p)`. Delete `engineClockx`; do not move it.
- **m7** (plan:158). The callers are only in Grid CO: `ClockBounds:176`,
  `CrossView:54`, `CrossView:84`, `ProposalDelivery:186`,
  `ProposalViewRelay:31` and `ProposalViewRelay:91`. SA and SA-PC have no
  caller. Only 3 statements get the premise: `synchronous_head_handled_early`,
  `synchronous_receipt_before` and `handled_before_proposal_of_ready`.
  `synchronous_proposal_delivered` and `synchronous_block_path_at_gate`
  relay a proposal, with `hp` in scope, so their statements do not change.
  None of the 5 lemmas is in `catalog.lock`, `REGISTRY.md`, `Tests/Axioms`
  or the FG-SA branch. Thus the premise weakens no locked or cataloged
  statement.
- **m8** (plan:262-272). `candidateOfAc43` is a locked definition with no
  consumer in 1b. Finding 5 gives the opposite rule for `Eligible`. The risk
  is small, because `Candidate` (`Catalog/Core.lean:103`) is already locked.
  Defer it to 1c, or state the exception.
- **m9** (plan:65-96, Shared sites with I9).
  - (a) The table does not list the `propose` sites: Grid CO
    `Protocol.lean:287-292` (it needs `mkBlock`), SA-PC `Choice.lean`, and
    L* `:253-259`. Grid CO `propose` is also an FG-SA constraint site, so
    I9 and the FG-SA branch conflict at that site.
  - (b) In the minimal variant of r196 (`root-nonce.md`), `rootOK` is in
    `wellFormed` and in admission. A proposal with a bad root is then
    outside `ExecutionValid` (`DeliveryWellFormed.wire`,
    `Conditions.lean:55-57`), so admission never refuses a valid delivery
    for its root. Thus I9 adds no permanent refusal, and neither `excludes`
    nor SA-PC's `rfl` (`ReceiptRelay.lean:265,275`) needs a change. The
    table rows "may add bad-root proposals" must give this condition: the
    admission check is the same local check as the wire check.
- **m10** (plan:63, :105). The FG-SA branch also imports
  `AvailableChainSA.Model.Protocol` and `AvailableChainKitFG.Correspondence`.
  This is true at the tip `e22cada` and in the worktree at `e3d34eb`. The
  plan moves neither, and the branch uses no changed name. I checked
  `gridCO`, `excludes`, `Engine.*`, the 5 relay lemmas, and the Kit
  `block_preceq_trans`. Its own `AvailableChain.FGSA.block_preceq_trans`
  does not collide. Add these imports to the list for completeness. The
  constraint holds.
- **m11**. Tasks 1–3 put the same names (`processed_stable`, `deps_stable`,
  `excludes_*`, `excludes`) in the namespaces `GridCO`, `SAPC` and `LStar`.
  A Registry `Instances/*` file that opens two of these namespaces gets
  ambiguous identifiers. Qualify the names.
- **m12** (plan:344-345). The label `profile-holds` is correct:
  `Profile.holdsAt` (`Profile.lean:34-35`) has no `inhabited` part, and the
  kind is never shown as `cert`. The row status is `LEAN`, like a
  certificate. Give the MATRIX legend this text: "holds: the claim
  propositions at one constant; no inhabitation; can be vacuous; not a
  certificate and not a `Candidate`". `sapc_holds_shared` has the type head
  `Exists`, so it gives no row. This agrees with the plan's count of six or
  seven rows.
- **m13** (plan:190-196). `excludes_head_iff` and "exactly the permanent
  refusals" are exact only for objects that pass the wire check. Ill-formed
  objects are also refused for good (for example, a head payload with
  `.none` auth), but `DeliveryWellFormed.wire` keeps them out of valid runs.
  Give this scope in the docstring.

## 3. Eligible deferral (premise 3)

The deferral is safe. In 1b, no statement needs `Eligible`. No task makes a
`Cert` or a `ProfileCert`. The `holdsAt` theorems do not claim inhabitation.
`Candidate` is not made for a protocol. The E4 `excludes` definitions are in
the protocol libraries, which the lock does not cover
(`CatalogLock.lean:55-70`). Thus plan 1c can correct them, for example L*
(M3), with no lock change. The Framework does not import the Kit, so
`Eligible` has no hidden consumer. One condition: 1c RelayFeasible needs
exact `excludes`. Close M3 before 1c uses L* at all.

## 4. Other checks

- Lock scope: Framework modules do not use `Kit/Core` or `V2Sketch`, and no
  lock line names them. The move in Task 0 therefore gives no REMOVED line.
  Task 4's `Catalog/Relations.lean` is under a locked prefix, so every
  declaration in it, helpers included, gets an ADDED line. This is expected.
  "`--check` exits 0" does not prove "lock unchanged", because additions
  also exit 0. For Tasks 0–3 and 5, the checkpoint must require an empty
  report.
- Task 3 `handles_carries` (R3): true for both branches. The PC branch
  handles `c.witnesses`, and carries uses the same list
  (`SAPC Handlers.lean:88-99`). The stop rule does not apply.
- Task 5: `gridLeasePolicy` is the default instance (`Protocol.lean:18`).
  `SA.Params` has `Δ` and `deltaPos`. The contract theorems have no extra
  premises, so the `holdsAt` theorems follow from `ac43_iff` and
  `strong1_iff`.
- A real `excludes` makes the regimes contain more runs: late faulty HEADs
  no longer need a handler call. With the same text, the contract theorems
  then state more. This is an instance change, not a contract change.
