# FG5c stage-3 semantic ledger

Authority: FG5 lead rulings 1, 2, 4, 6, and 7 (2026-10-02), plan section 3.5,
and spec fgsa-protocol.tex at 59bb0dda. This candidate implements the approved
window fold and R6W. The full build and local proof guards pass. Landing remains
blocked by the audit data gate and the real-main precheck; this is not a landing approval.

1. **Reachable and epochs.** `admitBlock` now uses `Window.on_block p p.K_W`.
   The concrete protocol, epochs, and run claims therefore describe W execution.
   Evidence: `fg_on_block_accepts`, `admitBlock_accepted_eq`, `fg_step_cases`,
   and the admission tests in `AvailableChainFGSA/Tests/WindowAdmission.lean`.
2. **CStoreInv.fg and Inv0.** Their generic store invariant now uses W finality.
   Evidence: `fgStoreSafety` uses `Window.windowStoreSafety`; the initial and
   step proofs use the restated FG3 invariant. The structure gains no field.
3. **RFrame.** Its step and row-selection clauses use the W updater and R6W.
   Every row is tested against the same pre-fold parent. Evidence:
   `rowsValidForParent_iff`, `Window.rowValidW_fold`, `mem_proposalRowsFor_iff`,
   and the common-parent admission test.
4. **RCert, RQCOrigin, finality observations, and accountability.** Finality
   fields in `RCert` (conjuncts 3 and 4), `certified`, `RQCOrigin`, `RXing`,
   `FGFinalizedAt`, cap/lag, crossing premises, and composition carrier
   premises read `finalityView`. Height-only clauses keep their text.
   Evidence: `fgCertificateLaws` uses `Window.windowCertificateLaws`;
   `fgsa_rCert` uses those laws; source proofs use `Window.window_final_birth`
   followed by the birth's target certificate. No complete-fold equality is used.
5. **Client h_F.** `fgInputs` reads `Window.headFields`; the shared
   `createRowOnce` action remains. Evidence: `fgInputs_headFields`,
   `emitted_finality_pair_of_headFields`, and the window head-field test.
6. **Stale-row validity and exclusion.** `parentFoldState` is the W parent;
   admission and selection use `Window.rowValidW`. Useful stale rows can pass.
   R6W alone does not imply HeightMatch. Evidence: the replacement
   `validForParent_currentHeightMatch` excludes the stale arm using the current
   height bound; admission tests cover useful, unmatched, future, and wrong-entry rows.

The latest-only finality bit interface is retired by ruling 4.
`row_bit_persist` now covers only target and progress over H. The Run
`fgsa_rowBitPersist` form is equivalent to its earlier height-only form by Boolean
cases and the height bridge. The decoded-row form also supplies batch coverage.
`rowValidFor_finality_persist`, `rowValidFor_finality_irrel`,
`rowValidFor_progress_first`, `validForParent_heightMatch`, and
`finalityView_eq_simplex` are removed. None is in the frozen API file.
The old `rowValidFor` definition, its `rowValidFor_iff` and `rowValidFor_fold`
proofs, and `fgStoreInvariant_on_block` also leave active use. The window
validity proofs and store-safety instance supply the replacement interfaces.
The removal of the Claims guard tuple entry is recorded in
`scripts/guard-lists-allow.txt`; all removed check-fgsa.sh expectations must be
listed in the writer report, since guard-lists does not check them.

Ruling 7 defers the height-only Claims text to J6. Unchanged manifest hashes
do not establish unchanged meaning: controls and store readers can hide a
changed public definition from the generated/private dependency hash.

"the unproven regime Props (FinalitySet, Recurrence, Regimes) now nominally describe W runs with old bounds: not re-validated until stage 4"
