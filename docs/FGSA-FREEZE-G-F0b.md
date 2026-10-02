# FG-SA G-F0b freeze record (W model)

Candidate content: fgsa-s46e (S4.6 + S4.6b + S4.6c + TDel / review fixes + S4.7 pre-freeze round), reviewed at
845d13e; the S4.7 fix round adds 0848d69 and this record (037ea95); B21 follows. The S4.8 freeze commit
replaces docs/FGSA-API-frozen.md with docs/FGSA-API.md at that head (scripts/fgsa-freeze.sh), resets
scripts/fgsa-manifest-allow.txt to its header line, and checks the new freeze with
`NEG=0 bash scripts/check-fgsa-manifest.sh`.

## Reviews

S4.7 freeze review, brief codex/jobs/s47-freeze-review.md (sha256 fee6aeb3b0f4), two models:
- Opus: FREEZE WITH FIXES, 0 blockers (TS/codex/reports/s47-freeze-review-opus-full.md).
- Astra: FREEZE WITH FIXES, 0 blockers (TS/codex/reports/s47-freeze-review-astra-full.md).
Combined lead ruling: TS/codex/reports/f07w-rulings.md, "S4.7 FREEZE REVIEW — combined ruling" (2026-10-02 20:41).
Both reviews found the genesis growth gap; CleanGrowthClaim + AwakeProposerRecurrenceFrom + the aggregate field
`cleanGrowth` close it (0848d69). The TDel ancestor question is closed (Astra checked in Lean).

## Ruled exceptions to the review-brief wording

The brief's literal checks "byte-identical to G-F0a" and "no ΔF dependency in any safety statement" do not hold
literally on this migrated surface. These are the exact, ruled exceptions:

1. FGSASafetyInterfaces (AvailableChainFGSAClaims/FGSAClaims.lean) is NOT byte-identical to G-F0a: its five
   explicit run binders changed from V2.Run to V2.D.Run (06 Duty port, 3d48ca8), and one comment changed. The
   hash moves have allow lines and semantic-ledger rows (Astra F4; Opus F7). FGSASafetyClaims keeps its G-F0a
   field list.
2. "No ΔF dependency in any safety statement": the G1/G2 finality-safety claims and the G-F0a structural safety
   claims have no row-delay, κ, recurrence or timeout premise. The exceptions are the Clean safety claims
   CleanSafetyClaim, CleanCutClaim, CleanHistoryClaim and CleanPrefixTruncationClaim (and CleanCutZeroClaim):
   they quantify `{ΔF : Time}` through their Clean regime packages (CleanPrem / CleanCutPrem / CleanPrefixPrem:
   "FG-SA rows have their own delivery bound", user 2026-10-01). Their conclusions hold for every row delay; ΔF
   only describes the healthy prefix (Astra §5 check 6 and :412).
3. DC table: Recovery₂.gap has the STRENGTH of DC SingleProposerRecurrence (from GST, over windows that end within
   the horizon) in the ROLE of DC RecoveryRegime.recurrence (DC: MultiProposerRecurrence). INTENTIONAL: it follows
   blueprint 21 ProposalGap; it is not strengthened (Astra F5; Opus S4.6c F5). The clean case uses
   AwakeProposerRecurrenceFrom (SingleProposerRecurrence role + the INTENTIONAL awake condition).

4. Exact-row service (Centaur Astra finality-route audit, TS/codex/reports/centaur/fgsa-s5-b1-core.md §8, M2):
   TRowsSelect and TRowsSync state exact-row service. The modeled proposer carries every valid held non-ancestor row
   (full inclusion, Model/Frame.lean proposalRows), so the exact-row disjunction is the modeled policy. The blueprint
   also permits an optional effect-preserving selection (22:323, 22:695; 01:83–86); that selection is not modeled,
   and paper T-ROWS must not be used to inhabit this stronger exact-row contract. No statement change.

## Post-review statement change (ruling B21)

After both reviews, the H-PHASE Opus review (F3) found that PhaseInterval, AttemptValid and RPhase required a
frontier of at least 2, but H.10 runs attempts at m = 1 (21:1467–1468, 2570–2571); the rise 1 → 2 then had no
contract route. Lead ruling B21 (evidence TS/codex/reports/m1-check-opus-full.md): relax to 1 ≤ m in PhaseInterval
(ChannelProps), RPhase clauses 1, 2, 3, 5 and RPhase_def, and AttemptValid (1 ≤ k.frontier). The premises become
weaker; each statement stays true at m = 1 (the frontier-1 frame is top J with J = genesis; 21:286, 1236). The gap
frame keeps R.j + 2 ≤ m (21:1191–1203). No G-F0a frozen name moves.

## Gates

- aaeb71c and 037ea95: FULL gates stopped before completion (superseded by later pre-freeze heads; lead).
- Final head (this record + S4.7 fixes + B21): FULL gate (record in the S4.8 commit message).
