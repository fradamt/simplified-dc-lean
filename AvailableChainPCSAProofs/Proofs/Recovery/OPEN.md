# Open inputs of the Recovery lane (C11)

`pcsa_fastRecoveredClaim` and `pcsa_longBreakRecoveredClaim`
(`Recovery/Export.lean`) are conditional: each takes a producer of
`RecoverySuffixInputs` (`Recovery/Suffix.lean`). No unconditional C11 is
claimed. Status of the inputs:

- First slot (`firstSlot`: a `FormationPrem` at `s₁` with the corrected F4
  clause `RecoveryRootReachable`):
  - F3, the common view at `v_{s₁}`: CLOSED by `recovery_commonView`
    (`Recovery/View.lean`, from the Shared `pcsa_commonView_of_delivery`).
  - The prefix formation fields of `FormationPrem`: OPEN.
  - The corrected F4 clause at the proposer: OPEN.
    `recovery_root_reachable` reduces it to the two-read lock bound;
    `recovery_genesis_root_reachable` gives it with the genesis anchor.
- Formation with corrected F4 (`formation`: every honest node holds the
  stamped PC of `N.erase` before `z_{s₁}`): OPEN, Formation lane. The clause
  is a separate argument until `FormationPrem` carries it.
- Persistence (`persistence`, ARM at `s₁` with `j₀ = s₁ + 1`): CLOSED by
  `recovery_persistence_of_run` (`Assembly/Recovery.lean`), from the
  unconditional C8 `pcsa_armPersistence`.
- Clean-anchor inputs: `recovery_cleanSaved_of_ci` and
  `recovery_cleanSaved_of_ci_pc` (`Assembly/Recovery.lean`) take CI at the
  anchor `cA` and the anchor gate result or stamped PC. Producing these from
  `ShortBreakPrem` is OPEN. `ShortBreakPrem.anchorPos` (`0 < cA`) leaves the
  genesis-anchor case to `LongBreakRecoveredClaim`.
- CI restart (`ciRestart`: the restarted chain invariant from `d_{s₁}`):
  OPEN, Clean lane.

Block admission under RECOVERY at a slot `s > 0` with `t_GST + Δ ≤ t_s` and
`d_s` in the run is CLOSED:

- (B1) `recovery_installed_target_body`: the target of a PC held by an
  honest node before `z_{s-1}` is stored at every honest node before `t_s`.
- (B2) `pcsa_honest_proposal_from_vote` (proposal wire and valid PC target)
  and `pcsa_honest_proposal_body_from_vote` (the body `N.erase`), at every
  honest read in `[v_s, d_s]`.
