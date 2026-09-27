# SA-PC status

_2026-09-27. Round 3. Base contract frozen at Draft 4.3._

The additive companion statements and executable SA-PC model are in place.
The library proves receipt, authentication, certificate, rank, and timed
save facts. It does **not** yet prove the requested base or strong bundles. Neither
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

## Exact remaining work

Resume at work-order step 3 after the receipt/projection bridges below.
Steps 3–6 are pending; the statements above are not bundle proofs.

1. Complete the timed receipt interfaces for the ordinary base cache:
   base vote/block stamp bounds, path receipt before cutoffs, and their
   retention. Raw HEAD clock and stamp bounds, admitted path closure and
   slot order, and exact timely-save and freeze origins are now proved.
   Connect the local timely-candidate test to delivered quorum batches;
   prove PC assembly completeness by a deadline. Lift local base handler
   correspondence to frozen/merged participant, equivocator, and declared
   support sets. No whole-run SA projection is proved.
2. Prove timely-N transfer and the active path domain and effective-view
   comparison with declared support. Saved-N honest preparation sources
   and honest ack origins are now proved. Outside the cap, use the active
   bound on detected equivocators; do not call every F4 supporter honest.
   Extend the local disabled projections to the needed run/suffix
   interfaces, retaining the joint invariant at a mode change.
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

No contract issue has been established through round 3. No requested claim
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

`Tests/Axioms.lean` audits 205 public SA-PC theorems, including the
smoke theorem, plus 18 shared theorems (223 entries). The L* conditional
fast-P1 lemma and the two new regime witness theorems also have axiom
audits. All checked entries use at most `propext`, `Classical.choice`, and
`Quot.sound`.

Targeted builds pass for the changed contract, SA and Grid CO bundles,
L* conditional fast P1, witnesses, and all new SA-PC proof modules.
`lake build AvailableChainSAPC --wfail` passes all 963 jobs.
`lake build --wfail` passes all 3,430 jobs with no warnings. This includes
`gridContract_from_engine`, `saContract_from_engine`, SA
`fastP1_from_engine`, the smoke tests, and the expanded audits.
`git diff --check` passes.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No `lake update` or Git commit was made. `state.md` and `log.md` were not
changed. The sandbox build could not acquire the external Lean throttle
lock. Its processes were stopped; builds then used the existing throttle
with lock access. Build-output scratch files were removed.
