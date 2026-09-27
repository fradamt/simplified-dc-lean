# SA-PC status

_2026-09-27. Round 7. Base contract frozen at Draft 4.3._

The additive companion statements and executable SA-PC model are in place.
The library proves receipt, authentication, certificate, rank, timed-save,
assembly-completeness, relay, frozen/merged view, F4 transfer, actual
proposal delivery, admitted HEAD targets, conditional PC service, timely-N
transfer with compatible finite roots, and same-label N/genuine compatibility.
It does **not** yet prove the
requested base or strong bundles. Neither
`sapcContract_from_engine` nor `sapcStrong_from_engine` exists yet.

## Sources and scope

The source directory is
`/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/`:
`sa-pc.md` §2 supplies the rules and §§4–6 supply the paper proofs;
`sapc-redteam.md` supplies the source-based lease argument and boundary
clarifications; `pc-spec.md` supplies the objects, receipt rules, and
companion shapes; `slow-arming.md` supplies SA.

The base clean and outage statements have no added fault cap. Only the
strong fields explicitly require the cap. The base Recovery regime
derives it from the selected constants. The companion is documented in
`CONTRACT.md`, “Strong companion (additive)”. Round 3 applies the
one-time authorized Draft 4.3 change below. No later contract change
is made.

## Constants and statements

`Statements/Contract.lean` declares `SAPCContract` and `SAPCStrong`.
Fast P1 is now a field of `SAPCContract`, with the requested constants:

- `τ = (n+1)/2`, `f = (n−1)/3`, `q = (2n+2)/3`, integer division.
- `θ = 1/2`, `θrec = 2/3`, `recoveryFull = true`.
- `D_c = D_s = D_f = strongDelay = 6Δ`.
- `L = (4k−1)Δ`, `A_slow = 4(k−1)Δ`, `A_fast = 4Δ`.
- `Π = min(η,L)`, `ρ = 2L + G + 8Δ`.

`StrongInterface` extends `Interface`. `StrongConstants` holds the fault
cap and delay. `StrongArmedRegime` requires healthy genesis delivery and
accepted relay, the cap, `h_t>a` before `b₀`, and `T+Δ≤b₀`. It has no
η-sleepy, budget, certificate-possession, or post-`b₀` field.
`StrongClaims` states clean safety, full-participation inclusion,
unbounded armed persistence, and recovered safety and inclusion.
It does not impose an order between strong and S.

## Model and reuse

`AvailableChainSAPC/Model/` contains five modules:

- `Objects`: signed HEAD data with the original ack, PCs, wire objects,
  raw archive and stamps, immutable-save fields, PC rank state, and the
  base projection. `State.base` is the existing `GridCO.State`.
- `Certificates`: raw exact-target N, distinct-seat PC assembly, admitted
  paths, rank with old-on-tie selection, one-label cap evidence, timely
  saves, and the head-extension ack predicate.
- `Handlers`: non-future raw admission without an age limit; ordinary
  two-target admission through `GridCO.admitVote`; block admission through
  `GridCO.admitProposal`; carried original signatures; PC completion after
  HEAD and path receipt; and structural/actual-handler delivery hooks.
- `Choice`: live cap test, frozen/carried PC selection for HEADs, live PC
  selection for proposals, active path domain, F4 floor, mandatory finite
  root, and original signatures recovered from the archive for proposals.
- `Protocol`: the separate S and prefix-lease PC guards, shared clock
  phases, and the `sapc` inhabitant of the fixed `ProtocolSpec`.

The ordinary base cache contains internal target-only keys. It does not
forge or emit new signatures. Complete payloads stay in the archive and
proposal store; outgoing views select original archived signatures.
Ack-only variants therefore neither equivocate nor consume another base
copy slot. Old raw evidence can complete a PC without replaying a base
vote or a past save.

The model calls shared views, GHOST, eligibility, release, expiry, raw
confirmation, admission levels, and obligation writes. `gateWithPC none`
calls `SA.gate` directly. The model is unchanged in round 2. The shared
schedule proofs now also apply to an arbitrary `ProtocolSpec`; their Grid CO and SA theorem names
and types are retained. Two existing shared lemmas are now public:
`fold_heads_mem_or_equivocates` and `stamp_eq_of_prefix`.
There is no claim that the entire active protocol is a plain-SA run.

## Draft 4.3 applied in round 3

The main `Constants` record now has `fastArmingLag`, with validity bounds
`0 ≤ fastArmingLag ≤ armingLag`. `AvailableChain.stableResilientFast`
uses `FastOutageRegime`: the fast lag replaces the general lag, with
`(n+1)/2` honest awake seats required at every `0 ≤ t < b₀`. The other
outage fields, budget, and persistence conclusion are retained.

SA and SA-PC use `4Δ`. SA's existing `fastP1_from_engine` now takes
this main regime and supplies the new bundle field. Grid CO uses its
general lag and derives fast P1 from general P1. L* uses its general lag
and has a conditional `fastP1_of_general`; its general claims remain
pending. Redundant extra-claim statements and fast constants copies are
removed. The witness `fastOutage` satisfies the fast regime with a fault
and a sleeper; `fastOutage_not_general` proves that its protected read
does not satisfy the general lag test.

The principle is documented in `CONTRACT.md`: tradeoffs go into
constants, not claims; every design must be able to meet every claim
trivially with some constant. The base contract is now frozen at 4.3.
The additive strong companion and SA-PC model rules are unchanged.

## Proved through round 2

- `Proofs/Basic`: all constant validity facts, unconditional nesting,
  quorum/cap inequalities, and the capped recovery support inequality.
- `Proofs/Projection`: exact SA gate projection when disabled or with no
  PC; exact disabled choice and HEAD target; ack-independent base keys;
  no base write on PC installation; retained equal-rank PCs; independence
  of frozen/carried selection from live PC installation; sound ack
  extension; save latching; and mandatory-root coverage.
- `Proofs/Archive`: assembly preserves source fields; receipts retain the
  archive and add only direct or carried inputs; clocks retain it.
- `Proofs/Authentication`: generic engine seat-duty payload uniqueness;
  archived-signature origins at `Run.readAt`; honest archived HEADs were
  emitted and have equal complete payloads at the same seat and label.
- `Proofs/Cap`: archive equivocation counts are bounded by the actual
  fault count at every `Run.readAt`, without synchrony; the capped switch
  is false at every such read; evidence and the switch are monotone under
  receipts and unchanged by the clock.
- `Proofs/GateSources`: raw history is saved despite either veto; the S
  veto does not suppress the loop; the finite veto blocks all lease
  writes; every new exact row has a raw-result prefix, its own admission
  test and PC guard, the passing whole-tip finite guard, and the exact
  gate-plus-lifetime deadline. This reuses `GridCO.writeKeys_row_origin`.
- `Proofs/RecoveryPremise`: the unchanged Recovery regime with the
  selected constants implies `FaultBound (sapc p) (pcFaultCap p) rho`.

Round 2 adds 108 public SA-PC theorems in these interfaces:

- `Proofs/ReceiptState`: PC gates and clocks retain receipt data; receipts
  retain paths; every non-future complete HEAD enters the raw archive;
  member loops preserve these facts. `fold_invariant` applies local
  invariants to actual engine folds.
- `Proofs/Authentication` and `Proofs/Cap`: authentic complete HEADs at
  event inputs, strict-time inputs, and reads; equality of honest HEADs
  across readers; the exact duty-time lower bound; and cap-test soundness
  at all these inputs. No synchrony premise is used.
- `Proofs/Handling`: each raw HEAD call projects exactly to the existing
  `GridCO.admitVote`. Actual direct, proposal, and envelope member calls
  archive the original signature. In the base window they leave the base
  key or two-target equivocation evidence, using the shared SA proof.
  This covers ack variants and third copies at the handler level.
- `Proofs/Acceptance`: each archived signature has a first accepted call,
  including carried signatures; later inputs retain it. Both accepted
  relay premises transfer it to a strict read before the relevant
  deadline. Structural containment alone is not used as acceptance.
- `Proofs/CertificateValidity`: every installed PC is valid in the local
  archive and admitted paths at event inputs, strict-time inputs, and
  reads. Direct ready envelopes archive all witnesses, including those
  of a lower-ranked PC. Later equivocation cannot invalidate a PC.
- `Proofs/FrozenCertificates`: receipts retain the frozen list; a clock
  retains it or appends its current PC. Frozen PCs remain valid. Every
  PC selected for a HEAD is valid, whether frozen or proposal-carried.
  This does not identify a selected PC with a later live PC.
- `Proofs/Quorum`: q-seat sets have an honest witness when `q>a`; two
  such sets intersect honestly under the cap. Raw N targets and PC
  targets are unique at the same label across authentic readers under
  the cap. An installed PC cannot precede its honest ack duty. These
  are same-label facts, not safety across different target slots.
- `Proofs/Rank`: a stored certificate is retained or replaced at a
  strictly higher slot. This holds across public reads without a cap.
  Rank retention alone is not strong prefix preservation.
- `Proofs/Paths`: each stored non-genesis block has an accepted proposal
  source. It is in the unchanged contract root scope. The shared
  `RootInjectiveBelow` premise follows at event and strict-time inputs.
- `Proofs/HeadStamps`: every archived HEAD has a stamp; stamp lists grow
  by append; the first stamp is unchanged at later inputs and reads.
  This does not yet supply the clock and cutoff bounds for timely N.

The source lemma deliberately does not assert that a lease is below S.
The local execution-M gate regression obtains a live X lease while S=Y
conflicts with X. It uses a constructed gate input, not a proved
`ExecutionValid` execution. It is not a contract counterexample.

## Proved in round 3

- Shared `GridCO/Proofs/EngineClock` abstracts the existing clock-order
  proofs over a clock accessor and its three laws. Grid CO keeps its
  previous theorem names and types as wrappers. The module also proves
  local invariant lifting, chronological clock-field origins, and
  append-only field retention. The engine model is unchanged.
- `Proofs/ClockBounds`: the PC gate retains the clock; every clock sets
  its time; every receipt retains it. Local clocks are monotone under
  the valid schedule and bounded by the next event. Required public
  ticks give a lower bound at delivery, including for sleeping readers.
  A HEAD handled in its early window enters the raw archive.
- `Proofs/ReceiptTimes`: all raw HEAD stamps are at most the local
  clock. A signature handled before an early cutoff retains its first
  stamp below that cutoff at every later strict input.
- `Proofs/Handling.process_base_invariant` lifts shared receipt
  invariants through all direct and carried calls. `Proofs/Paths`
  uses it to prove admitted ancestor closure and increasing parent
  slots. Every stored block has a complete admitted path. This uses
  the shared admission proofs, not a separate SA-PC admission model.
- `Proofs/Timely`: saves, including empty saves, have exact prior early
  tick origins and are immutable at later inputs. No save exists before
  its own scheduled early tick. A successful save has an honest exact
  preparation when `q>a`. Under the cap, saved targets at different
  readers agree. A qualifying candidate is saved at its scheduled tick
  under the cap; this is conditional on the local candidate test, not
  a proof of receipt or quorum completeness by that time.
- Every emitted ack names the preceding label and an actual successful
  save at a strictly earlier event index. Its emitted HEAD extends the
  saved target. Every PC in an authentic archive has an honest exact
  preparation source when `q>a`, obtained through its honest ack source.
- `Proofs/FreezeOrigins`: each frozen row, including an empty row,
  names the live PC at its own freeze tick. Frozen lists grow by append;
  later live receipts and clocks retain an existing nonempty selection.
  This does not identify a boundary HEAD's selection with a later PC.

These are intermediate proofs. They do not prove a joint clean
invariant, timely-N transfer, sound strong arming, or recovery.

## Proved in round 4

No model rule, base contract definition, or companion statement changed.
This round continues the receipt and projection work required by step 3.

- `Proofs/BaseReceipts` lifts the shared SA base-stamp invariants through
  SA-PC handlers. Base receipt lists grow by append. Every stored base
  vote and block has a first stamp, and all stamps are bounded by the
  local clock. A tip accepted before a cutoff has its complete admitted
  path before that cutoff; later receipts and clocks retain that fact.
- `Proofs/BaseArchive` proves that every cached base key has an original
  complete signature in the archive. Honest base keys cannot equivocate.
  Early honest handler calls therefore store the exact base key, with
  a stamp before the early cutoff. Outgoing original-signature views
  project to the same base-key lists, in order, and preserve the declared
  support subset. This does not prove the full proposal-merge interface.
- `Proofs/TimelyDelivery` connects a delivered exact-target seat quorum
  and an accepted target path to the local N test. Under the cap, that N
  is saved at the actual early tick. A synchronous-emission corollary
  derives the required HEAD calls from `PartialSynchrony`. It still
  requires the exact honest preparation quorum and accepted path.
- `Proofs/Assembly` proves that first-per-seat selection retains all
  seats and uses only original signatures. A sufficient usable ack
  quorum always assembles a valid PC. The archive scan considers every
  complete candidate. At every reachable state, valid local PC evidence
  implies a stored certificate of at least that target rank. This is a
  rank statement; it does not prove target compatibility.
- `Proofs/CertificateRelay` uses the first accepted calls for HEADs and
  proposal paths. A PC present at a healthy honest read T is valid at
  every honest reader strictly before T+Δ, with a stored PC of at least
  its rank. The post-GST version uses `max(T,GST)+Δ` and the horizon test.
  Sleeping readers are included. The same source argument relays a
  detected `capBroken` proof by those deadlines, including old-label
  and unresolved evidence. No gossip tick or cap is needed for relay.
- `Proofs/AckDelivery` proves PC completion strictly before the genuine
  gate from a delivered ack quorum and admitted paths. The synchronous
  version uses the contract broadcast premise. The deadline is the
  existing 6Δ gate. Exact preparations, covering HEAD choices, and path
  delivery for an honest proposal remain separate obligations.
- `Proofs/ActiveCounts` proves that each detected equivocation in a
  same-label base-cache subview has its target evidence in the archive.
  Active mode bounds this detected count by f, even above the actual
  fault cap. The theorem applies to reachable proposer views. Extension
  to frozen and proposal-merged effective views remains pending.

Shared receipt and uniqueness lemmas in `GridCO/Proofs/Stamps`,
`Receipts`, and `Votes` are exposed or factored for reuse. Existing
Grid CO and SA theorem names and types are retained. No engine definition
changed. All seven new modules contain completed proofs and are imported
by the default SA-PC target. No pending declaration is imported.

## Proved in round 5

No model rule, base contract definition, or companion statement changed.
This round proves the next view and score interfaces for step 3.

- `Proofs/BaseViews` proves that ordinary frozen raw keys remain in
  the base cache, retain their label, and contain their saved support
  subset. Each preceding-label key in an admitted proposal has an
  original complete signature in the raw archive. This includes keys
  omitted by the two-target base cache. The full merged HEAD view has
  those archive sources and the correct label at every engine fold.
- `Proofs/DeclaredSupport` derives the declared support subset from
  actual well-formed delivery events. Frozen and carried support remain
  subsets of merged raw views at event and strict-time inputs. Later
  resolution does not promote undeclared proposal members into support.
- `Proofs/ActiveCounts` now bounds detected equivocators in the full
  frozen/proposal merge by f when the live archive test is active.
  The proof uses archive sources directly, with no actual fault cap and
  no false requirement that all carried keys be in the base cache.
- `Proofs/Floor` proves that a score above the detected count has a
  resolved, non-equivocating declared supporter. The supporter is not
  asserted to be honest. An above-f prefix in an active merged view
  belongs to its declared support path in the active duty tree. The
  deepest floor covers every qualifying prefix of the ordinary walk.
  `choice_covers_of_ordinary_floor` proves local F4 transfer for any
  selected PC, provided that the ordinary walk covers the prefix, its
  score exceeds f, and the finite root is compatible with that prefix.
  These are explicit local premises, not new contract premises.
- `Proofs/EffectiveScores` proves that conflicting scores overlap only
  at detected equivocators when declared support is a raw subset.
  Their sum is at most n+e. Therefore a q-score strictly beats every
  conflicting score in active mode, without assuming the actual cap.
  The valid engine supplies the archive and support premises for the
  merged-view corollary. It does not yet supply the q-score by its
  deadline; timely-N transfer still needs that receipt proof.
- `Proofs/FrozenViews` proves exact ordinary freeze origins through the
  generic engine clock-source theorem. Frozen rows grow by append.
  At an honest reader, including a sleeping reader, the saved view
  after its scheduled freeze is the view of that tick's strict input.
  Later PC receipt, saves, release, and gates cannot replace it.

Three existing pure lemmas in `GridCO/Proofs/Map` are now public for
reuse: `fold_deeper_depth`, `fold_deeper_origin`, and
`preceq_of_compatible_depth_le`. Their proofs and types are unchanged.
The five new modules contain completed proofs and are imported by the
SA-PC default target. No new claim inhabitant is asserted.

## Proved in round 6

No model rule, engine definition, base contract definition, or companion
statement changed. This round adds 42 completed public theorems in six
modules. The modules are imported by the default SA-PC target.

- `Proofs/Proposals` identifies the exact proposer action in the generic
  engine, including its clock. An honest SA-PC proposal carries its
  original raw and support signatures and live PC. Positive slots with
  an awake honest proposer have an actual proposal emission. The block
  is non-genesis and has that slot. No common-choice premise is used.
- `Proofs/ProposalDelivery` proves direct proposal acceptance before
  HEAD, both after GST and on a healthy outage prefix. The execution
  supplies the parent, freshness, and authentication guards. Admission
  stores both the original envelope and its base projection before the
  carried-signature loop. The proposal's entire path has first stamps
  before HEAD, and retains that bound at later inputs. Sleeping readers
  are included. None of these results assumes the fault cap.
- `Proofs/HeadTargets` proves that finite lease targets remain stored,
  using their raw-result sources and shared path closure. It does not
  require a lease to be below S. Both active and disabled choices end
  at an admitted block. Active HEADs use the validity of their selected
  frozen/carried PC. A stored block before HEAD has no future slot.
- `Proofs/HeadEmission` defines the actual duty state and complete
  target-and-ack payload. Every awake honest seat emits that payload.
  Its target was stored strictly before HEAD and its slot is at most
  the duty label. Accepted-object relay puts the target path at each
  honest reader before the early deadline, without a separate gossip
  tick or an explicit path-delivery assumption.
- `Proofs/CertificateService` constructs the honest seat quorum from
  the cap. `full_preparations_saved` proves actual saves and their
  retention at later inputs if all honest preparation choices name the
  honest proposal and all those seats are awake. The engine supplies
  their signatures, handler calls, paths, and early ticks.
  `full_preparation_ack_service` then proves a valid PC before the 6Δ
  gate if all next honest HEADs extend that proposal and are awake.
  It also proves that the stored PC has at least the proposal's rank.
  These are conditional service theorems: they do not prove the two
  choice premises, compatibility of a higher PC, or strong inclusion.
- `Proofs/ProposalViews` proves retention of complete and base proposal
  envelopes through clocks and receipts. The actual honest proposal is
  present at each reader's HEAD. Projecting its original signatures gives
  exactly the ordinary SA payload shape. The shared SA merge lemmas then
  put every proposer raw key and declared support key in the effective
  HEAD views. Proposal-source blocks relay separately to resolve that
  support. These are subset results, not equality of cross-reader counts.

All shared SA proof calls use local base states and the proved delivery
interfaces. No SA-PC run is asserted to be a plain-SA run. No shared proof
module needed a change in this round.

## Proved in round 7

No model rule, shared proof module, base contract definition, or companion
statement changed. This round adds 33 completed public theorems in four
new modules and `Proofs/EffectiveScores`. All are default imports.

- `Proofs/RecentArchive` proves the missing archive-to-base direction
  for recent labels. An archived signature has its base key or two-target
  equivocation evidence. The invariant is preserved by every receipt and
  every chronological clock. Old archive entries need no base receipt.
  The strict-input result applies before proposal time `r+2`, including
  the freeze and gate for `r`. It covers third copies, ack variants,
  carried signatures, and the relay case where the reader already has
  the signature. Strict-input clocks and stamps also give exact raw
  freeze and late-pool identities.
- `Proofs/TimelyTransfer` proves that a timely N supplies score at least
  q in every next frozen/merged HEAD view under accepted-object relay.
  It relays the raw preparations and their target path. A dropped third
  copy contributes through the retained equivocation evidence. Saves
  identify the actual strict early input, rather than later receipts.
- `Proofs/EffectiveScores` uses the shared GHOST path-dominance theorem
  to turn q support into ordinary-walk coverage and then F4 coverage.
  It uses the active detected-count bound, not an actual fault cap.
  `active_voter_quorum_covers` needs only compatible finite roots in
  addition to the active quorum; path and ordinary-walk premises are
  derived from the execution.
- `timely_active_head_covers` and `savedTimely_active_head_covers` connect
  those results to the actual HEAD target. The synchronous and healthy
  wrappers derive their relay interface from the contract premises.
  They retain the finite-root compatibility premise. No choice premise
  is assumed in their conclusions.
- `timely_departure_disables_by_gate` proves the mixed-mode implication:
  if a next HEAD with a compatible finite root leaves the timely target,
  it must have `capBroken = true`. Relay makes that evidence common
  strictly before the same-label gate. This does not prove compatible
  finite roots or the joint induction through the mode change.
- `Proofs/MergedReceipts` proves reverse relay from the entire merged
  HEAD raw view to another reader's same-label late pool, with the exact
  base-key-or-equivocation alternative. It includes proposal-carried
  keys. It does not assert equality of proposal and voter views.
- `Proofs/QuorumGenuine` reuses shared `TransferReceipts` on the local
  late pool. A raw exact quorum and a raw genuine result at the same
  label cannot conflict. `timely_compatible_confirmation` supplies the
  quorum receipts and target path by relay from the strict early input.
  It has no active-mode or fault-cap premise and applies before either
  gate guard. It does not compare targets at different labels.

These results close the timely-N receipt and score gap from round 6.
The finite-root invariant, forward genuine-support transfer, honest
proposal choice, and the requested bundle proofs are still pending.

## Exact remaining work

Resume at work-order step 3 after the receipt/projection bridges below.
Steps 3–6 are pending; the statements above are not bundle proofs.

1. Complete cross-reader proposal-merge comparison for participants,
   equivocators, and declared support. Local frozen/merged archive
   sources, label preservation, declared-support subsets, and the
   active detected-count bound are now proved. Exact ordinary freeze
   origins are also proved. Actual honest proposal acceptance, path
   delivery, envelope retention, and proposer raw/support inclusion in
   the merged view are now proved. The capped full-participation service
   theorem derives preparation and ack quorums from exact/covering
   choices. Prove those choices from the joint clean or recovered
   invariant; prove the reverse view comparison needed for common
   participant, equivocation, and support counts. Reverse relay from
   the full merged HEAD view to the source gate late pool is now proved;
   forward genuine-support transfer and the common honest-proposal
   view comparison are still pending. The two-target cache
   can omit a carried raw key, so do not assume raw-set equality from
   archive relay alone. No whole-run SA projection exists.
2. Supply finite-root compatibility for timely-N transfer from the joint
   clean invariant. Delivery of q raw preparations and their paths,
   the two-copy alternative, quorum score, ordinary-walk coverage, and
   active F4 coverage are now proved. A compatible-root departure gives
   common disablement before the gate. Same-label N/genuine compatibility
   is also proved. Cross-label compatibility and mixed-mode clean
   induction remain pending, as do the SA run/suffix interfaces. Do not
   call every F4 supporter honest outside the cap. Retain the joint
   invariant at each mode change; disablement does not create a new genesis.
3. Prove the joint clean induction, safety, monotonicity, and `6Δ` base
   inclusion. Only constants and nesting are currently proved base fields.
   Prove general and fast P1, including the pending healthy HEAD and the
   first prefix lease when the raw descendant is PC-vetoed. Reuse SA
   source, transfer, and lease-map proofs after proving these interfaces.
4. Prove sound strong arming and the boundary HEAD with an older freeze;
   exclude the first departure without a duration budget. Prove full
   clean PC inclusion, strong safety, and late-reveal protection. The cap
   theorem alone proves none of these strong fields.
5. Prove F4 transfer for synchronous fast sources and full slow windows,
   permanent accessible support, expiry of all unsupported sources, and
   fresh-PC record repair within `2L+G+8Δ`. Reuse SA's source-support
   recovery interface. Its `SynchronousLabel` has a proposal-time boundary;
   do not substitute the paper's first synchronous HEAD without a proof.
   Deriving the cap is not a recovery proof.
6. Assemble `sapcContract_from_engine`, SA-PC `fastP1_from_engine`, and
   `sapcStrong_from_engine`; audit their axioms.

No contract issue has been established through round 7. No requested claim
has a checked counterexample. Do not weaken a premise or conclusion to
close a gap. No incomplete Lean declaration is left in a default module;
there are no placeholder proofs or pending imports.

## Validation

The 18 kernel-checked Boolean regressions cover old and future HEADs,
ack variants, the two-target cache, per-label unresolved cap evidence,
invalid witnesses, PC retention after equivocation/disablement, late path
completion, first stamps, timely saves and actual-head acks, frozen/carried
selection and rank ties, the repaired prefix loop, the finite guard, F4
and mandatory leases, expiry, equality release, carried cap evidence, and
a complete proposal/preparation/ack/gate replay from the initial state.

`Tests/Axioms.lean` now audits 429 entries: 396 SA-PC theorems and
33 shared theorems. Round 7 adds 33 SA-PC audits.

Targeted checks pass for all four new modules and `EffectiveScores`.
The final full `lake build --wfail` passes all 3,452 jobs with no warnings.
It includes `gridContract_from_engine`,
`saContract_from_engine`, SA `fastP1_from_engine`, the unchanged smoke
tests, and all public-theorem audits. Every audited SA-PC theorem uses
at most `propext`, `Classical.choice`, and `Quot.sound`.
`git diff --check` passes.

Round 7 checked the Lean processes before validation. Builds use the
installed throttle with its required lock access. No throttle setting
was changed.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No `lake update` or Git commit was made. `state.md` and `log.md` were not
changed. The temporary build log was removed. No session scratch file
remains.
