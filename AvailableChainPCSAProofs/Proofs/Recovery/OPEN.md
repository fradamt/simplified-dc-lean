# Open inputs of the Recovery lane (C11)

`pcsa_fastRecoveredClaim` and `pcsa_longBreakRecoveredClaim`
(`Recovery/Export.lean`) are conditional: each takes a producer of
`RecoverySuffixInputs` (`Recovery/Suffix.lean`). No unconditional C11 is
claimed. Status of the inputs:

- First slot (`firstSlot`: a `FormationPrem` at `s₁` with the corrected F4
  clause `RecoveryRootReachable`):
  - F3, the common view at `v_{s₁}`: CLOSED by `recovery_commonView`
    (`Recovery/View.lean`, from the Shared `pcsa_commonView_of_delivery`).
  - Short break: CLOSED by `pcsa_recovery_firstSlot_short`
    (`Assembly/Recovery.lean`). It supplies `FormationPrem` and the separate
    `RecoveryRootReachable` predicate from `ShortBreakPrem`.
  - Long break: OPEN. The surviving-lock and proposer-root proof remains.
    `recovery_genesis_root_reachable` gives F4 with the genesis anchor.
- Formation with corrected F4 (`formation`: every honest node holds the
  stamped PC of `N.erase` before `z_{s₁}`): OPEN, Formation lane. The clause
  is a separate argument until `FormationPrem` carries it.
- Persistence (`persistence`, ARM at `s₁` with `j₀ = s₁ + 1`): CLOSED by
  `recovery_persistence_of_run` (`Assembly/Recovery.lean`), from the
  unconditional C8 `pcsa_armPersistence`.
- Clean-anchor inputs: `recovery_cleanSaved_of_ci` and
  `recovery_cleanSaved_of_ci_pc` (`Assembly/Recovery.lean`) take CI at the
  anchor `cA` and the anchor gate result or stamped PC. The short-break
  producers are now CLOSED: `pcsa_recovery_cleanSaved_from_anchor` bounds
  saved results from `Clean₂` at the anchor freeze; and
  `pcsa_recovery_anchor_from_shortBreak` supplies the honest proposal,
  common stamp, ARM, and its conclusion. Both are in `Assembly/Recovery.lean`.
  `ShortBreakPrem.anchorPos` (`0 < cA`) leaves the genesis-anchor case to
  `LongBreakRecoveredClaim`.
- CI restart (`ciRestart`: the restarted chain invariant from `d_{s₁}`):
  OPEN, Clean lane.

Block admission under RECOVERY at a slot `s > 0` with `t_GST + Δ ≤ t_s` and
`d_s` in the run is CLOSED:

- (B1) `recovery_installed_target_body`: the target of a PC held by an
  honest node before `z_{s-1}` is stored at every honest node before `t_s`.
- (B2) `pcsa_honest_proposal_from_vote` (proposal wire and valid PC target)
  and `pcsa_honest_proposal_body_from_vote` (the body `N.erase`), at every
  honest read in `[v_s, d_s]`.

## Long-break lock history progress

`Recovery/LockRank.lean` proves `recovery_live_lock_rank_compatible` from
store reachability. Every held PC at or above a live lock's rank has a
compatible target.

`Recovery/LockHistory.lean` proves `recovery_lock_write_witness` from a
stored row and the schedule. It derives an actual fresh gate, the current
result, the preceding saved window, the checked write rank, and an
uninterrupted interval of that exact row and rank. It proves the deadline
equality `row.2.2 = SA.gateTime p.toParams s + pcsaL p`.
`recovery_live_lock_last_write` derives this witness at the actual post-clock
read index.

The witness also exposes every saved result in the full k-window. The exact
row and rank remain present at every event state after the selected gate.
`recovery_lock_no_later_successful_renewal` excludes every later successful
renewal in this interval. It uses the actual fresh-gate and slow-write tests.
The witness is not a claim premise. It does not prove surviving HEAD coverage or either long-slot F4.

Step 2 is implemented as the lane-neutral `RecoveryLockTransport` structure
and the Assembly constructor `pcsa_recovery_lock_transport`. The constructor
has seven named OPEN parameters. Existing Clean exports require a healthy
prefix, so none supplies the required recovery statement on this branch.
`OPEN_sameLabel` includes label `g`, also when `t_g < GST ≤ v_g`.
The other fields are `OPEN_earlyForward`, `OPEN_voterBackward`,
`OPEN_pcReceipt`, `OPEN_honestVoterInputs`, `OPEN_honestProposerInputs`, and
`OPEN_rootResolution`. The structure and the constructor state each field in
full. They do not assume lock coverage, root compatibility, or walk dominance.

Step 3 is proved. `Recovery/LockOverlap.lean` proves:

- A live write after the mix has a window wholly at labels at least `g`.
- Two coexisting live deadlines force their saved windows to overlap.
- A live lock at `v_(j+1)` has a write label in the pending write's window.
- The same-label transport field excludes conflicting window prefixes.
- All live locks at the first HEAD are compatible with the pending target.
- All live locks after the write are compatible while its deadline is live.
- Post-mix live locks at different honest nodes are compatible.
- A conflicting PC at or above the saved rank blocks the write when relayed
  from `v_(j+1)` before `d_j`. At later reads it cannot coexist with the
  exact row if the receipt deadline is inside the surviving interval.

`Recovery/LockRank.lean` also proves the stored-row rank invariant and
extracts an active, early-stamped PC witness of a nonempty gate rank.
`Recovery/LockStamp.lean` now derives the held key before `e_j` from the
actual stamp history. `recovery_gate_rank_disseminated` relays the same rank
before `z_j`. `Recovery/LockView.lean` retains that PC in each later frozen
view and proves `recovery_voter_rank_bound`. The selected view's key is held
before `v_r`, including when a proposal carries it.
`recovery_write_voter_compatible` and `recovery_survivor_voter_compatible`
close K without an assumed rank lower bound. The survival theorem retains
the exact receipt-index bounds for `v_r + Δ = e_r`. It does not assert
receipt before an arbitrary faulty-slot HEAD.

Steps 4–6 remain to be proved. No `LockFollow`, `ProposalPaths`, or
`LongFirstSlot` module, long-slot export kernel, or
`pcsa_recovery_firstSlot_long` wrapper has been added. The continuation
stops at a checked commit boundary to stay within the session budget.
This is partial work. No counterexample or false-statement blocker was found.

## Continuation transport statements

The exact OPEN parameter names in `Assembly/Recovery.lean` are `OPEN_`
followed by each field name below. The intended supplier premises are
`Recovery₂ p c E rho G ΔF`, `StageOneFrame p c E rho`, and
`E.t_GST ≤ SA.voteTime p.toParams g`. There is no `GST ≤ t_g` premise.
No existing Clean export on this branch supplies these statements from
those recovery premises. The Assembly constructor takes them explicitly.

```lean
structure RecoveryLockTransport (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (g : Slot) : Prop where
  sameLabel : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ X Y,
      gateResultAt p c E rho x r = some (some X) →
      gateResultAt p c E rho y r = some (some Y) → Block.Compatible X Y
  earlyForward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ GridCO.earlyVotes p.toParams.engine (actView src.st) r,
      ∀ i, GridCO.headSeat? o = some i → ∀ H,
        GridCO.resolvedHead? (actView src.st) o = some H →
        ((o ∈ headSupport p dst.st (r + 1) ∧
          GridCO.resolvedHead? dst.st.base o = some H ∧
          GridCO.stampVote dst.st.base o < SA.freezeTime p.toParams r) ∨
          GridCO.equivocates (headVotes p dst.st (r + 1)) i = true) ∧
        H ∈ dst.st.base.blocks ∧
        GridCO.stampBlock dst.st.base H < SA.freezeTime p.toParams r ∧
        (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1))))
  voterBackward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ headVotes p dst.st (r + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ GridCO.lateVotes p.toParams.engine (actView src.st) r ∨
        GridCO.equivocates (GridCO.lateVotes p.toParams.engine (actView src.st) r) i = true
  pcReceipt : ∀ t, E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target ∧
      pc.target ∈ (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st.base.blocks
  honestVoterInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ headSupport p dst.st (r + 1) ∧
      o ∈ headVotes p dst.st (r + 1) ∧
      GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
        (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1))))
  honestProposerInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ proposerSupport dst.st (r + 1) ∧
      o ∈ proposerVotes dst.st (r + 1) ∧
      GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st (fullTree p dst.st))
  rootResolution : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ a b : Nat, ∀ X Y,
    X ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks →
    Y ∈ (V2.D.Run.stateBefore E rho b y).st.base.blocks →
    X.root = Y.root → X = Y
```

## Continuation signature locations

The full proved signatures are in the source declarations:

- `recovery_lock_no_later_successful_renewal` in `LockHistory.lean`.
  It takes the exact deadline and uninterrupted interval from
  `recovery_lock_write_witness`. It rules out every later successful
  fresh-gate slow-write branch before the read.
- `RecoveryLockTransport` above and `pcsa_recovery_lock_transport` in
  `Assembly/Recovery.lean`. The latter constructs only the transport value.
- `recovery_postmix_lock_window`, `recovery_postmix_live_locks_compatible`,
  `recovery_window_next_vote_locks_compatible`, and
  `recovery_window_later_locks_compatible` in `LockOverlap.lean`.
- `recovery_survivor_received_pc_compatible`,
  `recovery_survivor_relay_pc_compatible`, and
  `recovery_write_relay_pc_compatible` in `LockOverlap.lean`.
  These K kernels retain an explicit PC rank lower bound.

The requested final firstSlot signature remains unproved and absent:

```lean
∃ N : NamedProposal p.n,
  FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
```

## Proved checkpoint signatures

The source namespace is `AvailableChain.PCSA.Run`. The usual implicit
parameters are `{p : Params} {In V : Type} [DecidableEq V]`,
`{c : AppCodec In}`, and `{m : FGMode}`.

```lean
theorem recovery_lock_no_later_successful_renewal (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (i j : Nat) (x : V) (s : Slot) (row : Block × Nat × Time)
    (hj : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (hd : row.2.2 = SA.gateTime p.toParams s + pcsaL p)
    (hsurv : ∀ q, j < q → q ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho q x).st.base.obligations)
    (k : Nat) (r : Slot) (hjk : j < k) (hki : k < i)
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams r))) :
    let pre := clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams r)
    ¬ (GridCO.savedGenuine pre.base r = none ∧
      ∃ C, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) r = some C ∧
        (pre.base.obligations.any (fun q => pre.base.now < q.2.2 &&
          !Block.compatible q.1 C)) = false ∧
        row.1 ∈ (actView pre).blocks ∧ row.1 ≠ .genesis ∧
        Block.Preceq row.1 C ∧ leaseWriteOK pre.pcs (gateRank p pre r) row.1 = true ∧
        SA.Root.slowEligible p.toParams
          (actView (gateFrom p (eraseFG pre.fg.F) pre.pcs (gateRank p pre r) pre r))
          r row.1 = true)
```

```lean
theorem recovery_postmix_lock_window (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) (B : Block) (hB : LiveLease nd.st B)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ t) :
    ∃ a s, g ≤ s + 1 - p.k ∧ SA.gateTime p.toParams s ≤ t ∧
      t < SA.gateTime p.toParams s + pcsaL p ∧
      ∀ r, s + 1 - p.k ≤ r → r ≤ s → ∃ D,
        GridCO.savedGenuine (V2.D.Run.stateBefore E rho a x).st.base r = some (some D) ∧
        Block.Preceq B D
```

```lean
theorem recovery_survivor_relay_pc_compatible (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (g : Slot) (transport : RecoveryLockTransport p c E rho g)
    (i j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (row : Block × Nat × Time)
    (hsurv : ∀ a, j < a → a ≤ i →
      row ∈ (V2.D.Run.stateBefore E rho a x).st.base.obligations ∧
      leaseRank (V2.D.Run.stateBefore E rho a x).st row.1 =
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1)
    (t : Time) (ht : E.t_GST ≤ t) (horizon : t + p.Δ ≤ rho.horizon)
    (hlo : j < V2.D.Run.idxBefore rho (t + p.Δ))
    (hhi : V2.D.Run.idxBefore rho (t + p.Δ) ≤ i)
    (pc : PC p.n) (hpc : pc ∈ (V2.D.Run.stateBeforeTime E rho t y).st.pcs)
    (hrank : rankAtLeast pc
      (leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) = true) :
    Block.Compatible pc.target row.1
```

## Checked continuation report (2026-10-08)

Code commits:

- `a8304cb6`: step 1, no later successful renewal.
- `86fde434`: step 2, transport interface and named OPEN suppliers.
- `a14fced9`: step 3 overlap proofs and rank-conditional K kernels.
- `b8debb9d`: remove the foreign rank equation export. No signature change.

```text
┌──────┬─────────┬──────────────────────────────────────────────────────────┐
│ Step │ Status  │ Result or exact remaining work                           │
├──────┼─────────┼──────────────────────────────────────────────────────────┤
│ 1    │ PROVED  │ Explicit no-later-successful-renewal corollary.          │
│ 2    │ PROVED  │ Interface only. Seven lane suppliers remain OPEN.        │
│ 3    │ STOPPED │ Rank dissemination and selected-view rank bound missing. │
│ 4    │ STOPPED │ Not started. Step 3 is incomplete.                       │
│ 5    │ STOPPED │ Not started. Step 3 is incomplete.                       │
│ 6    │ STOPPED │ Not started. The long firstSlot wrapper is absent.       │
└──────┴─────────┴──────────────────────────────────────────────────────────┘
```

This is a budget checkpoint. No counterexample or false statement was found.
The next proof must connect the gate-rank witness's early stamp to a PC held
before `e_j`. Then apply PC receipt before `z_j` and derive the rank lower
bound in later frozen views. This completes the missing part of K before F′.

Validation of the code at `b8debb9d`:

- Default `lake build --wfail`: PASS, 4,589 jobs.
- `LC_ALL=C bash scripts/check-build.sh`: PASS, including all self-tests.
- Layers: PASS, zero new findings. Layer self-test: PASS, 37 controls.
- GLY and F-13 under `LC_ALL=C`: PASS.
- `NEG=0 check-fgsa-claims.sh`: PASS.
- `NEG=0 check-pcsa-manifest.sh`: PASS, 421 entries in 21 modules; hashes match.
- Normal proof coverage: PASS, 5,901 declarations across 13 audits.
- All 25 new public names have explicit axiom audits. Only standard axioms occur.
- New declaration names have no collision on the six requested refs.
- Main precheck: expected ancestry refusal, main `b698238`, target `b8debb9d`.
  Fixed ref `222cf06a` is also not an ancestor. No main merge or push.

The first full check found `rankAtLeast.eq_1` exported from `LockOverlap`.
Commit `b8debb9d` uses `rankAtLeast_def` instead. The full rerun has zero
unaccepted equation exports. No checker, policy, or model change was made.
The five shared lock theorem signatures remain unchanged. No file named
`Recovery/RestartSeed.lean` was created. All tracked edits are within the
allowed file list. This report commit changes only this Markdown file.

## Continuation 2 coordination

The intended label-`g` majority supplier is `pcsa_gate_majority_of_label`
in `Clean/HonestBatch.lean` on `pcsa-ci-win-2`. Its floor is `T₀ ≤ v_s`.
Use it for the boundary `t_g < GST ≤ v_g` behind `OPEN_sameLabel`.
That branch has not been merged. The seven Assembly transport parameters
remain OPEN on this branch. Their exact statements above are unchanged.

Formation is adding `FormationPrem.proposerRootReachable`. Step 6 must set
`proposerRootReachable := hroot` from the same proof as the separate
`RecoveryRootReachable` conjunct. This branch still has the old structure.
No Formation or Claims file is changed here.
