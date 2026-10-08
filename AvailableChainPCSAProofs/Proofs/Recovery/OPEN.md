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

Step 3 is partial. `Recovery/LockOverlap.lean` proves:

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
K is not complete. The rank witness still needs dissemination before `z_j`.
Each later selected voter view still needs the resulting rank lower bound.
The relay kernels take that lower bound explicitly; they do not prove it.

Steps 4–6 were not started. No `LockFollow`, `ProposalPaths`, or
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
