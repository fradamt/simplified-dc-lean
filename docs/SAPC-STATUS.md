# SA-PC status

_2026-09-27. Round 13. Base contract frozen at Draft 4.3._

The additive companion statements and executable SA-PC model are in place.
The library proves receipt, authentication, certificate, rank, timed-save,
assembly-completeness, relay, frozen/merged view, F4 transfer, actual
proposal delivery, admitted HEAD targets, conditional PC service, timely-N
transfer with compatible finite roots, genuine-support transfer to actual HEADs,
and same-label compatibility of raw genuine results and N/genuine results.
Round 9 defines the joint clean invariant, proves its initial state,
freeze step, all Sleepy delivery steps, capped proposal steps, and conditional reductions
of safety, monotonicity, and `6Δ` inclusion. No new unconditional contract
claim is proved. It does **not** yet prove the requested base or strong bundles. Neither
`sapcContract_from_engine` nor `sapcStrong_from_engine` exists yet.

Round 11 replaces the arbitrary path argument with the run-determined
`cleanRunPath`. The new `JointCleanInvariant` includes ordered genuine
history and actual HEAD continuation. The old predicate is now
`CleanPathFacts`; the rejected event obligation remains only as a checked
historical test. The test also proves that the new path excludes the
losing sibling and includes the actual next timely save.

The shared SA/Grid CO label induction is extracted and reused by both
instances. Round 13 proves `clean_run_invariant_capped` from Sleepy and
`a≤f`, for every event prefix. It includes early/gate source comparison,
ordered genuine history, and the final incomplete HEAD. Local reverse
receipts remove the following-gate horizon premise. The helper
`clean_safety_capped_from_engine` proves safety and monotonicity of both
base outputs under this cap, with no assumed invariant.

This does not discharge a base contract field: those fields must hold
for all `a<h`. First-use disablement, uncapped and mixed-mode preservation,
and common exact honest proposal choices remain open. The `6Δ` inclusion
reductions still need those choices, even under the cap. Neither requested
bundle is proved. No contract or executable rule changed in this round.

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

## Proved in round 8

No model rule, shared proof module, base contract definition, or companion
statement changed. This round adds 25 completed public theorems in three
modules. All three modules are default imports.

- `Proofs/EarlyReceipts` proves that new base stamps use the receipt
  clock and name stored receipts. A stamp below a public cutoff implies
  that the receipt was present at the strict cutoff input. This applies
  to carried signatures, target blocks, and sleeping readers. It does
  not infer an early receipt from later archive membership alone.
- `Proofs/GenuineTransfer` constructs the shared SA `TransferReceipts`
  interface for actual SA-PC gate and next-HEAD states. Early signatures
  and paths reach the freeze. If the two-target cache omits a key, it
  retains equivocation evidence. Reverse relay of the full merged view
  excludes that alternative for a surviving genuine supporter. Thus each
  such supporter is in the actual declared support view and has no
  conflicting copy in the merged raw view. The proof has no fault-cap
  or active-mode premise and includes proposal-carried keys.
- Genuine prefixes have complete paths in the ordinary frozen domain.
  The shared SA walk proof gives ordinary coverage from a compatible
  finite root. The actual SA-PC HEAD covers the prefix if either its
  genuine support exceeds f (any selected PC), or the selected PC is
  compatible with the prefix (no minimum F4 score). Both conclusions
  still require finite-root compatibility. These are local transfer
  interfaces, not proofs that a contract regime supplies the roots.
- `sameLabel_from_engine` proves compatibility of raw genuine results
  at the same healthy label. Both source majorities transfer into one
  actual merged view. Conflicting results would each strictly dominate
  the other. This applies before both gate guards and in mixed modes.
- `Proofs/TransferRegimes` derives the forward and reverse relay
  premises from the fixed contract conditions. Synchronous wrappers
  require GST no later than the early cutoff and a horizon through the
  gate. Healthy wrappers require the healthy prefix through that gate.
  They do not handle a pending gate after outage onset.

This closes the forward genuine-support transfer gap from round 7.
Common honest-proposal view comparison, the joint clean induction,
pending outage transfer, strong claims, and recovery remain open.
No complete contract inhabitant is asserted.

## Round 9: joint invariant and event steps

`Statements/CleanInvariant.lean` defines `JointCleanInvariant` as one
predicate on a run prefix and a common path. It contains ancestry closure,
comparability, honest admitted-path witnesses, actual HEAD continuation
of genuine results, finite lease sources, saved genuine results, S and G,
honest timely-N sources for valid PCs, capped timely/PC path membership,
the false mode flag under the cap, and signature authentication.

Outside the cap, PC path membership is required at its actual authority
uses: gate, HEAD, and proposal ticks. It is not required merely because
an archive holds a valid PC while the local mode is still active. The
paper's failed-N argument disables authority before its first effect;
it does not require storage and disablement to occur at the same instant.
The definition retains historical finite records across mode changes.
It does not assert that every live lease is below S.

Completed proofs:

- `CleanSteps` proves finite-path preservation by every delivery kind,
  expiry, freeze, release, and all clock phases. At a gate it requires
  the raw result to be on the path. It proves that S does not retreat
  under that premise. New lease targets use `gateWithPC_row_origin`.
- `gateWithPC_eq_sa_of_path` proves equality with the complete SA gate
  when the raw result and active PC are on the path. This includes every
  prefix guard and the lease loop. `gate_clean_includes` proves that
  the raw result enters S without any lease-admission premise.
- `CleanConsequences` proves the full invariant at genesis and derives
  finite-root membership, event-by-event record order, record order
  between any two event prefixes, and both output safety statements
  **from the joint invariant**. It does not derive that invariant from
  Sleepy.
- `CleanDelivery` proves that the whole joint invariant survives delivery
  of **any object under plain Sleepy, without the cap**. `q > a` supplies
  an honest ack. Its exact saved value gives an actual timely save
  strictly before the current input, without quorum uniqueness. Under
  the cap that save is also on the path. Outside the cap, delivery stores
  evidence and does not exercise authority. This covers HEADs, carried
  proposal evidence, direct PC envelopes, late assembly, and sleeping
  readers. `jointClean_delivery_of_sleepy` uses the fixed regime directly.
- `CleanTicks` proves the full freeze step without a cap. It proves the
  full proposal tick under the cap, including its live-PC authority.
  Its general between-duty step requires the new proposal authority
  clause when the tick is a proposal time. It does not prove common
  exact HEADs for an emitted proposal.
- `CleanInclusion` proves the actual gate write from the joint invariant
  and reduces both `6Δ` inclusion fields to honest raw proposal service.
  It handles the remainder of the deadline's event prefix by the proved
  record order. The raw proposal-service premise is still unproved.

`Pending/CleanInduction.lean` states the remaining steps as Lean
propositions, with exactly the Sleepy regime and no cap. It is not
imported by a default target. It has no placeholder proof or axiom.
The remaining obligations cover early, HEAD/release, gate, and proposal
ticks and raw honest-proposal service. All three delivery kinds are proved. Early tick
`r+1` and gate `r` are one actual clock call; they are not separate
state changes. The same applies to HEAD and release.

No checked counterexample to a step or contract claim was established.
The open steps below are proof gaps, not claims of false statements.

## Round 10: checked failure of the early-cutoff obligation

`Tests/CleanInvariantCounterexample.lean` constructs a complete run of
`sapc p` from the engine initial state. It proves `ExecutionValid`, the
exact `SleepyRegime`, `FaultBound`, the full round-9 invariant before the
cutoff, and the impossibility of extending its path after that event.
The module is a default import. The checks use kernel reduction; they
use no `native_decide`, placeholder proof, or project axiom.

The parameters are Δ=1, n=4, k=2, η=0, f=1, q=3. Nodes 0, 1, and 2 are
honest and always awake. Node 3 is faulty and is the proposer at every
slot. Thus h=3>a=1 and a≤f. The horizon is 6. The run has all public
ticks at times 0 through 6 and all required self-deliveries.

- At time 1, all three honest HEADs name genesis. Every honest node
  receives them at time 1.
- At time 4, the faulty slot-1 proposer supplies two genesis children:
  X with root 2 and Y with root 1. Every honest node receives both.
- At time 5, all honest HEADs choose X, using the ordinary root tie
  rule. Every honest node receives all three X HEADs at time 5.
- Prefix 42 is immediately before node 0's time-6 tick. The full
  `JointCleanInvariant` holds with `path B := B=genesis ∨ B=Y`.
  The records still equal genesis, finite rows and genuine history are
  empty, no successful N or valid PC exists yet, and Y is accessible
  in an actual honest state. HEAD and proposal PC authorities are empty.
- Event 42 is the actual early tick for label 1, together with gate 0.
  At prefix 43, node 0 has saved `N(1,X)`. The capped `timely` field
  requires X on the next path. Any extension of the old path also
  contains Y. Since X and Y conflict, no such clean path exists.

`before_cutoff` proves the entire input invariant, not only its finite
state fields. `next_save` proves the event and save. `no_extension`
refutes exactly the existential path extension used by `JointEventStep`.
The witness's `sleepy` theorem checks root injectivity, the complete
schedule, wire/dependency/freshness checks, signature provenance,
broadcast, accepted-object relay, and participation. The blocks have
distinct roots. All required deliveries have delay zero, strictly below Δ.

`Pending/CleanInductionCounterexample.lean` then proves
`cleanEventObligations_false`, the negation of the existing
`CleanEventObligations p env`. This module stays outside default imports
because it refers to the pending statement module. It is checked
separately. The pending definitions are unchanged.

The exact defect is the universal quantification over every path that
satisfies the round-9 invariant. `accessible` permits stored proposals;
it does not require that a path member has a genuine or timely source.
The other fields do not restrict extra path members before those sources
exist. This run therefore satisfies the invariant on the losing branch.
It does not show that a suitable path cannot be chosen for the run.

No workaround, weakened premise, protocol change, or contract change is
applied. Preservation as stated cannot be completed. HEAD/release, gate,
uncapped proposal authority, and proposal service remain pending. The
conditional safety, monotonicity, and 6Δ inclusion reductions remain
valid, but this induction cannot discharge their premises as written.
No new unconditional contract claim is asserted.

## Round 11: run sources and shared genuine-history induction

No contract or model rule changes. The proof state is no longer a free
path that can choose a stored losing branch.

- `Statements/CleanInvariant` renames the round-9 predicate to
  `CleanPathFacts`. The new `cleanRunPath p rho index` is genesis plus
  ancestors of actual raw gate results, capped honest timely saves, and
  PC targets used at active gate, HEAD, or proposal duties. It contains
  no source from mere block storage and no uncapped N storage source.
  `JointCleanInvariant p E rho index` has no path argument. It combines
  facts about this set with `OrderedGenuine`; its continuation clause
  refers to actual honest HEAD ticks. Comparability is still a proof
  obligation, not a property built into the path definition.
- Shared `Proofs/HistoryInduction` extracts `GenuineExtends`,
  `GenuineContinues`, and `genuine_history_induction` from the proved
  Grid CO/SA label induction. The existing `clean_genuine_history`
  theorem now uses this common proof. Its statement is unchanged.
  No whole-run SA projection is assumed.
- `RunCleanPath` proves source retention, ancestry closure, the genesis
  path, and inclusion in any old conditional path. Deliveries add no
  path source, including receipts that complete a PC or prove capBroken.
  It proves the new invariant initially and after every Sleepy delivery.
  `RunCleanTicks` reuses the existing local clock proofs for freezes,
  between-duty ticks, and capped proposal ticks. The latter uses the
  installed PC's earlier honest timely save as a canonical source.
- `GenuineHistory` proves unconditional source-closure membership for
  both records, saved raw results, and finite targets. Every reachable
  finite row has an earlier raw gate source at the same reader. A row
  at HEAD r+1 has source label strictly below r, even though gate r is
  still pending. Ordered genuine history therefore supplies finite-root
  compatibility for genuine transfer. There is no lease-below-S premise.
  `clean_genuine_history_of_steps` uses the common induction. Disabled
  transfer uses SA directly; only active transfer needs PC compatibility.
- `Preservation` proves the actual receipt/count bridge for SA-PC:
  honest early base keys survive the late filter; the raw denominator
  is at most the awake honest count plus the faulty count; actual honest
  HEADs and paths reach the strict early input. `preserve_from_heads`
  then invokes the shared SA confirmation theorem.
  `sleepy_preserve_from_heads` derives delivery and counts from the
  unchanged regime. `clean_genuine_history_of_pc` discharges the batch
  step and leaves only active selected-PC compatibility as its input.
- `CleanService` proves that successful N saves and valid PCs inherit
  any prefix covered by the actual honest HEADs at their preparation
  label. The proof extracts an emitted honest exact HEAD. It has no cap
  premise beyond q exceeding the actual fault count. Exact honest HEADs
  at the proposal label give the exact raw gate result by shared slot
  order. Both 6Δ inclusion reductions now need common exact proposal
  HEADs and the corrected invariant, rather than an unproved raw-service
  premise. The safety reduction also consumes the corrected invariant.
- The existing counterexample remains as documentation of the rejected
  free-path statement. Three new kernel-checked tests prove that the
  canonical path at prefix 42 is exactly genesis, excludes Y, and
  includes the actual saved X at prefix 43. The old refutation now names
  `Pending.Rejected.CleanEventObligations`, not the new definition.

The new pending definitions are `CleanEventObligations`,
`CleanPCTransferObligation`, and `CleanProposalChoicesObligation` in
`Pending/CleanInduction`. The old definitions are in
`Pending/RejectedCleanInduction`. None is imported by a default target.
These are proof obligations, not new premises of the contract.

The round-10 counterexample does not refute the new statement. This
round does not prove all its event steps. In particular, source-set
membership alone does not prove comparability, PC first-use authority,
or exact proposal choices. No unconditional clean contract field is
claimed from the conditional reductions.

## Round 12: capped PC sources and HEAD transfer

No contract, protocol rule, or invariant field changes.

- `CleanPCPath` proves that every valid PC at an event input has its
  target on `cleanRunPath` under the cap and execution validity. This
  includes live PCs, frozen PCs selected by a HEAD, and carried PCs.
  It needs neither Sleepy nor an assumed clean invariant. The source is
  the earlier honest timely save supplied by an original ack.
- Under the cap, the canonical path has exactly two source kinds: raw
  honest gate results and honest timely saves, with ancestry closure.
  Gate, HEAD, and proposal PC authority adds no extra branch. A capped
  HEAD/release tick therefore leaves this source set unchanged.
- A selected PC at HEAD `r+1` has target label strictly below `r`.
  This uses `q>a` and the strict input cutoff, so it also holds without
  the cap under plain Sleepy. A current-label PC cannot control that HEAD.
- `RunCleanHeads` derives the finite-root premise from actual rows on
  the input path. Timely-N transfer to the next HEAD now uses the joint
  invariant and the cap, with no extra finite-root assumption. This
  theorem permits a final HEAD with no later gate in the run.
- `CleanTicks` factors its existing proof into a clock step with no
  early save or gate. `RunCleanHeads` uses this step to prove the full
  capped HEAD/release event preservation when the following gate is
  within the horizon. It derives genuine continuation by the existing
  SA batch-preservation and genuine-transfer proofs. The old freeze,
  between-duty, and proposal proofs keep their statements.
- `RunCleanTransfer` derives continued coverage of a timely save through
  earlier HEADs from one current invariant. Its first step uses quorum
  transfer; subsequent steps reuse SA preservation and genuine transfer.
  Finite and PC roots come from the current path's earlier state fields.
  No new timely-continuation field is assumed.
- `selectedPC_prefix_pending_genuine` proves more than compatibility:
  under the cap and the joint invariant at HEAD `r+1`, the selected PC
  target is a prefix of every honest pending raw result at label `r`.
  Its proof uses the strict PC label bound and timely continuation.
  It does not assume that the pending gate is already a path source.
  The gate deadline must be within the horizon.
- `clean_genuine_history_capped_of_head_invariants` supplies this PC
  input to the existing shared SA/Grid CO induction. It still requires
  the chronological invariants at the relevant HEAD inputs. This is an
  explicit proof dependency, not an unconditional clean-history theorem.

The remaining chronological step must add the new timely save and the
preceding raw gate result at the same early/gate tick. It must prove
comparability of these sources, continuation of the new raw result at
the already executed next HEAD, and ordered history. The current
source-membership results alone do not prove any of those three facts.

The full capped HEAD step still has a horizon boundary: its backward
relay uses `gateTime s ≤ horizon` for HEAD `s+1`. A last incomplete
label needs a proof from the available honest batch, or another proved
argument that does not extend the run. No run extension is assumed.
The separate timely-N transfer theorem does not have this restriction.

Above the cap, a stored timely target need not enter the canonical path.
First-use disablement and the mixed-mode steps remain pending. No cap
has been added to a base contract claim. Common proposal choices and
all unconditional clean-field conclusions remain pending. No new checked
counterexample or contract issue was found in this round.

## Round 13: complete capped chronological induction

No contract, protocol rule, or invariant field changes.

- `MergedReceipts` defines the exact reverse receipt condition
  `BackReceipts`. `local_back_receipts` proves it from the reader's own
  archive and the two-copy cache alternative. It includes carried raw
  keys. It needs no future gate tick, relay deadline, or run extension.
- `GenuineTransfer` factors five existing proofs through that receipt
  condition. Their old relay-based theorem statements remain available.
  `synchronous_local_genuine_head_covers` uses the same proof for the
  reader's own pending raw result. Its only relay deadline is the freeze.
  It needs no cap, but retains finite-root and selected-PC compatibility.
- `RunCleanHeads` now proves capped HEAD/release preservation with no
  following-gate horizon premise. `RunCleanTransfer` removes that premise
  from timely continuation and selected-PC/pending-result comparison.
- `RunCleanFacts` proves source accessibility from actual capped raw
  gates and timely saves. It reconstructs all receipt and source fields
  from a comparable source path and genuine continuation. It then proves
  `JointCleanInvariant.restrict_capped`: an earlier prefix has its own
  canonical path and full invariant. It does not reuse the later path.
- `RunCleanGates` uses those earlier HEAD invariants in the shared
  genuine-history induction. It compares raw/raw, timely/timely, and
  raw/timely sources. Equal-label timely saves use quorum uniqueness;
  equal-label raw/timely pairs use preparation relay. Other label pairs
  use actual HEAD continuation. This proves the whole capped early/gate
  step, including the new save, preceding raw gate result, ordered
  history, and continuation through the HEAD already executed.
- `RunCleanCapped` proves every capped event step and then
  `clean_run_invariant_capped` by event induction. The derived
  `clean_safety_capped_from_engine` proves cross-reader safety and local
  monotonicity of both base outputs from Sleepy and the cap alone.
  It has no assumed invariant, path order, or HEAD-coverage premise.

The cap in this helper is explicit. It is not added to any base contract
claim. This closes the capped chronological branch; it does not prove
uncapped clean safety or common proposal choices. No new counterexample
or contract issue was found. Strong claims, both P1 fields, recovery,
and both requested bundle inhabitants remain pending.

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
   the full merged HEAD view to the source gate late pool and forward
   genuine-support transfer are now proved. The common honest-proposal
   view comparison is still pending. The two-target cache
   can omit a carried raw key, so do not assume raw-set equality from
   archive relay alone. No whole-run SA projection exists.
2. Supply finite-root compatibility for timely-N transfer from the joint
   clean invariant. Delivery of q raw preparations and their paths,
   the two-copy alternative, quorum score, ordinary-walk coverage, and
   active F4 coverage are now proved. A compatible-root departure gives
   common disablement before the gate. Same-label N/genuine and
   genuine/genuine compatibility are now proved. Genuine HEAD transfer
   works with compatible finite and selected-PC roots, or with a
   compatible finite root and source support above f. The capped joint
   induction now supplies these root premises and cross-label order.
   Derive them without the cap and through mixed-mode steps. The SA
   run/suffix interfaces remain pending. Do not
   call every F4 supporter honest outside the cap. Retain the joint
   invariant at each mode change; disablement does not create a new genesis.
3. Complete the new run-determined clean induction. The round-10
   free-path defect is removed and retained as a regression. Actual
   batch preservation and finite-root compatibility from genuine
   history are now proved. Capped selected-PC compatibility with the
   pending genuine result is proved from the input invariant, through
   timely continuation. The entire capped event induction is now proved,
   including early/gate preservation and the final incomplete HEAD.
   Complete first-use disablement above the cap and mixed-mode event
   steps. For an authoritative uncapped PC, prove that its timely source
   transferred, or that a departing HEAD made disablement common before
   the first possible gate effect. Retain the genuine-history and lease
   source facts through this mode change. Complete uncapped proposal
   authority and common exact honest proposal HEAD choices. Exact raw
   service from those choices is proved. Then apply the uncapped safety,
   monotonicity, and 6Δ inclusion reductions. The capped safety helper
   does not fill those base fields. Only constants and nesting are
   currently unconditional base fields.
   Prove general and fast P1, including the pending healthy HEAD and the
   first prefix lease when the raw descendant is PC-vetoed. Reuse SA
   source, transfer, and lease-map proofs after proving these interfaces.
4. Prove sound strong arming and the boundary HEAD with an older freeze;
   exclude the first departure without a duration budget. Prove full
   clean PC inclusion, strong safety, and late-reveal protection. The cap
   theorem alone proves none of these strong fields.
5. Use the proved genuine F4 transfer after showing finite-root
   compatibility: release opposing leases for fast sources, and exclude
   recent conflicting writes and expire older ones for full slow windows.
   Derive above-f genuine support from the full honest batch. Prove
   permanent accessible support, expiry of all unsupported sources, and
   fresh-PC record repair within `2L+G+8Δ`. Reuse SA's source-support
   recovery interface. Its `SynchronousLabel` has a proposal-time boundary;
   do not substitute the paper's first synchronous HEAD without a proof.
   Deriving the cap is not a recovery proof.
6. Assemble `sapcContract_from_engine`, SA-PC `fastP1_from_engine`, and
   `sapcStrong_from_engine`; audit their axioms.

No contract issue has been established through round 13. No requested
contract claim has a checked counterexample. The round-9 universal
event-preservation obligation has the checked counterexample above. Do not weaken a premise or conclusion to
close a gap. No incomplete Lean declaration is left in a default module;
there are no placeholder proofs or pending imports.

## Validation through round 9

The 18 kernel-checked Boolean regressions cover old and future HEADs,
ack variants, the two-target cache, per-label unresolved cap evidence,
invalid witnesses, PC retention after equivocation/disablement, late path
completion, first stamps, timely saves and actual-head acks, frozen/carried
selection and rank ties, the repaired prefix loop, the finite guard, F4
and mandatory leases, expiry, equality release, carried cap evidence, and
a complete proposal/preparation/ack/gate replay from the initial state.

`Tests/Axioms.lean` now audits 491 entries: 458 SA-PC theorems and
33 shared theorems. Round 9 adds 37 public-theorem audits.

Targeted checks pass for all new proof modules. The separate pending
statement module also passes (963 jobs). The final `lake build --wfail`
passes all 3,461 jobs with no warnings. Default targets include
`gridContract_from_engine`, `saContract_from_engine`, SA
`fastP1_from_engine`, the unchanged smoke tests, and all public-theorem
audits. Every audited theorem uses at most `propext`, `Classical.choice`,
and `Quot.sound`. `git diff --check` passes.

Round 9 checked the Lean processes before validation. Builds use the
installed throttle with its required lock access. No throttle setting
was changed.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No `lake update` or Git commit was made. `state.md` and `log.md` were not
changed. The temporary validation logs were removed. No session scratch
file remains.

## Round 10 validation

The targeted `lake build --wfail` passes for the default counterexample
module and `Pending/CleanInductionCounterexample` (965 jobs). The latter
prints the axioms of `cleanEventObligations_false`.

The final `lake build --wfail` passes all 3,462 jobs with no warnings.
The default audit now has 497 entries, including all six new public
witness theorems. These six and the separate refutation use only
`propext`, `Classical.choice`, and `Quot.sound`. The default targets still
build `gridContract_from_engine`, `saContract_from_engine`, and SA
`fastP1_from_engine`. `git diff --check` passes.

No `sorry`, `admit`, project axiom, or `native_decide` is introduced.
No contract, protocol rule, or invariant definition is changed. No Git
commit or `lake update` is made. `state.md` and `log.md` are unchanged.
No session scratch file was created or remains. Validation used the
installed Lean throttle; process CPU/time checks were made.


## Round 11 validation

All five new SA-PC proof modules and shared `HistoryInduction` pass
targeted checks. The default audit has 535 entries. It includes every
new public theorem, the extracted shared induction, the refactored
shared `clean_genuine_history`, and the three canonical-path regression
results. All dependencies are limited to `propext`, `Classical.choice`,
and `Quot.sound`; the extracted induction uses only `propext`.

The final `lake build --wfail` passes all 3,468 jobs with no warnings.
The full build retains `gridContract_from_engine`,
`saContract_from_engine`, and SA `fastP1_from_engine`. No base contract,
companion contract, or executable rule changed. `git diff --check`
passes. The corrected pending statement and historical refutation are
also checked separately, outside the default targets.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Validation used the installed Lean throttle; CPU and
elapsed-time checks were made. Session build logs were kept inside the
repository and removed after validation.

## Round 12 validation

The three new proof modules and the shared clock-step refactor pass
`lake build --wfail`. The separate pending statement and historical
refutation modules also pass. The default audit has 554 entries,
including all 19 new public theorems. Their dependencies are limited to
`propext`, `Classical.choice`, and `Quot.sound`.

The final full `lake build --wfail` passes all 3,471 jobs with no
warnings. The default targets retain `gridContract_from_engine`,
`saContract_from_engine`, and SA `fastP1_from_engine`. The existing smoke
checks and canonical-path counterexample checks pass. `git diff --check`
passes.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract definition, protocol rule, or invariant field was changed.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Lean process checks used elapsed time and CPU use; the
installed throttle was retained. Session validation logs were kept
inside the repository and removed after validation.

## Round 13 validation

Targeted `lake build --wfail` checks pass for the receipt refactor,
HEAD and timely transfer changes, and all three new proof modules.
The separate pending statements and historical refutation also pass
(993 jobs). No pending module is imported by a default target.

The final full `lake build --wfail` passes all 3,474 jobs with no
warnings. Default targets retain `gridContract_from_engine`,
`saContract_from_engine`, SA `fastP1_from_engine`, smoke checks, and
canonical-path counterexample checks. The default audit has 573 entries,
including all 19 new public theorems and the strengthened existing
HEAD/transfer theorems. Their dependencies are limited to `propext`,
`Classical.choice`, and `Quot.sound`. `git diff --check` passes.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract, protocol rule, or invariant field changed. No Git commit
or `lake update` was made. `state.md` and `log.md` were not changed.
Lean process checks used elapsed time and CPU use. The first sandboxed
build could not acquire the installed throttle lock; it was stopped and
validation used the same throttle with lock access. No throttle setting
was changed. All session scratch logs were inside the repository and
were removed after validation.
