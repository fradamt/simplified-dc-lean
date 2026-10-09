# port-w16c — WP16 Y / WP12d / wfix2 data refresh

Data tip: `acca54f9670dccd67f03c72992a4cb1119ff896b`. Earlier groups: `33ac5fec`, `2862a33a`.
Branch: `port-w16c`. Source base: `988177e222b441e9ee08d51f8dfd39c80b0d395d`.
Required precheck base: `318074ba`. Date: 2026-10-09.

The required precheck, freeze bytes/history/packages, both source checks,
old-read audit/controls, and P13 pass. The three requested FG-SA libraries pass.
The complete audit build, expected-name gate, and coverage gate do not pass.
They find a new Y reset-proof failure in the WP13v Inhabit fixture.
The shallow and deep checks also require protected data edits outside current approval.
No complete port acceptance pass is claimed.

## Data changes

The FGSA-to-Run import exception is removed. Both generated policies match.
The stored facade no longer imports the two absent Spec paths. The Run facade
already imports their replacements. The ownership registrations use Run/Proofs/Spec.
The old coverage inventory has zero rows for either moved module; its 48 other
stored Spec rows remain. All 59 moved public theorem owners are measured separately.
Simulation has 50 public theorems and Transfer has nine. Fifty-five headers match;
the four retained-clock replacements have complete old/new statements and source reviews.
Two expected names have their retained-clock replacements.

The ledger records all six source commits: b0b493d8, 3c64a7e2, 9ef4bc76,
7ab64f69, c00e3236, and 29dfcf26. It has 60 source-file events and complete
statement comparisons. Explicit replacement pairs cover the five renamed restore
helpers, four Spec results, and the private timing fixture. The same-name
restore_rec and ancestorDeadlines_restore changes are also recorded.
Source review and WP16 data review remain separate. The existing named production
consumer conclusions and all claim source bytes remain unchanged.

All 118 FG-SA P13 suppliers were measured. The 177 changed map rows have measured
paths to changed Y source dependencies. The P13 check passes for FG-SA and PC-SA.
All 36 OPEN items and all PARTIAL statuses remain. The aggregate has one binder,
zero proposition binders, and fingerprint `f0d9a772701a8a1a` at all three locations.
The aggregate and six restart-permitting claims compile from Params alone.
The 59 moved Spec theorems and 15 other changed public helpers resolve.
Their transitive axioms are only propext, Classical.choice, and Quot.sound.
The private timing fixture has the same standard axiom set in the full build log.

Of 2,578 expected names, 2,214 resolve from current unblocked modules.
The other 364 depend on Inhabit modules that cannot build on this source base.
The 1,782 changed unblocked evidence rows have measured dependency causes.
The full expected gate remains an input failure; no expected row is removed.

Coverage has 6,681 rows in 14 fixed audits. Five restore-name rows have exact
replacements verified by the current Run build and supplemental oracle.
The other 6,676 rows keep their bytes. Complete generation and the normal check
stop at the missing Inhabit object. The previous 35-export failure remains assigned
to port-weq; this run cannot reach or recount those exports. No equation baseline edit.

Old reads pass: 10,203 constants in 520 active modules, six old/finality readers,
and 244 height-only readers. All controls pass. The baseline retains its bytes.
WCProposalPivot stays height-only; no scope reclassification is made.

The API generator measures 1,243 entries in 57 modules. Only Reachable changes hash,
and Reachable.reset is added. All other generated rows and historical prose remain.
The shallow check now stops only at the old protected Reachable pin.
Frame passes: 43 entries, five exact exceptions, no frame data edit.
Deep measures 1,243 roots and 3,665 nodes. Relative to the accepted pre-Y digests,
897 roots change: 886 existing exceptions need new digests and 11 need new entries.
Each old/new root digest has a measured current path to fgsa or Reachable.
No prior node digest is inferred from equal source text. The exact handoff is
`claude-files/port-w16c-deep-handoff.json`; WP00c owns the exception file.

The S0 history covers both changed frozen paths. Reachable changes at b0b493d8,
with actual parent b8f60fd1 and measured hashes. The API data changes at 2862a33a,
with actual parent 33ac5fec and measured hashes. The final pin is 2862a33a:
122 paths, 20 differences, 46 history records, and 22 packages. No S0 manifest edit.
ARCHITECTURE E6 now describes retained last tick and record, no added tick/duty,
and all six restart-permitting claims. Z, AA, and AB remain explicit later obligations.

## Before / after

```text
┌──────────────────────┬─────────────────────────────┬───────────────────────────┐
│ Check                │ Before                      │ After                     │
├──────────────────────┼─────────────────────────────┼───────────────────────────┤
│ precheck             │ PASS                        │ PASS                      │
│ freeze               │ FAIL: Invariants            │ PASS: 122 paths; 20 diffs │
│ store source         │ PASS                        │ PASS                      │
│ run source           │ PASS                        │ PASS                      │
│ three libraries      │ 143: stopped blocked build  │ PASS: 3899 jobs           │
│ audit roots          │ Not run                     │ FAIL: Inhabit reset       │
│ policy module        │ Not run                     │ PASS: 2 jobs              │
│ expected names       │ Old paths / two stale names │ INPUT ERROR: 364 blocked  │
│ unblocked names      │ Not measured                │ PASS: 2214 / 2578         │
│ supplement           │ Not measured                │ PASS: 74; moved 59        │
│ old reads / controls │ Same baseline               │ PASS: 10203 / 520 modules │
│ coverage             │ Five stale audit names      │ INPUT ERROR: Inhabit      │
│ coverage generation  │ 6681 rows                   │ INPUT ERROR: Inhabit      │
│ P13                  │ FAIL: 177 mismatches        │ PASS; 36 OPEN retained    │
│ six witnesses        │ Not run                     │ PASS: Params alone        │
│ API generation       │ 1242 entries                │ PASS: 1243; prose kept    │
│ shallow              │ Changed / missing reset     │ FAIL: protected old pin   │
│ deep                 │ Pre-Y exception data        │ FAIL: 897 exact deltas    │
│ frame                │ Same fixed data             │ PASS: 43; 5 exceptions    │
│ finality coverage    │ PASS                        │ PASS                      │
│ ownership            │ PASS                        │ PASS: 746 paths           │
│ Inhabit candidate    │ Six reset goals fail        │ PASS; patch not applied   │
│ freeze history       │ 44 records; pre-Y pin       │ PASS: 46 exact records    │
│ freeze packages      │ 20 packages                 │ PASS: 22 packages         │
└──────────────────────┴─────────────────────────────┴───────────────────────────┘
```

All commands and exits are in `final_refresh` and the port-w16c check rows in
`docs/FGSA-PORT-CHANGES.json`. Evidence is in `.lake/port-w16c/`.
The exact required commands were run:

```sh
bash /Users/francesco/.claude/jobs/22f59f85/tmp/precheck.sh \
  /Users/francesco/.claude/jobs/22f59f85/tmp/wt-pcsa-formation 318074ba
python3 -B scripts/check-fg-finality-freeze.py --check
python3 -B scripts/check-fg-finality-freeze.py --history
python3 -B scripts/check-fg-finality-freeze.py --packages
SOURCE_ONLY=1 bash scripts/check-fgsa.sh
SOURCE_ONLY=1 bash scripts/check-fgsa-run.sh
LEAN_SLOTS=2 lake env lean --run scripts/CheckFGSAOldReads.lean --controls
LEAN_SLOTS=2 python3 -B scripts/check-proof-coverage.py
LEAN_SLOTS=2 python3 -B scripts/check-proof-coverage.py --write
LEAN_SLOTS=2 python3 -B scripts/check-fgsa-blueprint.py --check
```

## Build evidence

```sh
LEAN_SLOTS=2 lake build --wfail \
  AvailableChainFGSAProofs AvailableChainFGSARun AvailableChainFGSA
# exit 0; 3899 jobs; build-final.log
LEAN_SLOTS=2 lake build --wfail $(cat .lake/port-w16c/audit-targets.txt)
# exit 1; 4158 jobs; audits-build.log; only failed module: Inhabit WeakContinuationW1
LEAN_SLOTS=2 lake build --wfail AvailableChainCheckSupport.ImportPolicy
# exit 0; 2 jobs; policy-build.log
```

The first sandbox build reported the stale facade imports and waited for shared
slot locks. Only its verified waiting processes and sleep children were stopped;
exit 143. The corrected build used the normal shared two-slot wrapper.
No throttle bypass, other-writer process kill, lake update, push, rebase, agent,
or review process was used.

## Blockers and cross-WP work

WP13v: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:106:17` has an unsolved
reset rowPool goal. The other first errors are 106:42, 107:12, 1184:17, 1184:42,
and 1185:12. The two restart proofs need initialAt in their simplification lists.
`claude-files/port-w16c-inhabit-fix.patch` is ready. Its complete local candidate
compiles with warnings as errors, exit 0. It changes no statement and is unapplied.
An ownership exception was requested; no answer has arrived.

Protected shallow data: `claude-files/port-w16c-shallow-pin.patch` changes only
Reachable's existing pin from b8ebe90e84f54451 to measured 6dbbc505d29881d3.
Automatic approval review rejected the mutation because AGENTS.md protects allow lists.
The pin patch is unapplied. Approval was requested; no answer has arrived.
An incorrect pin could accept an unintended statement change; this patch is exact.

WP00c: apply/review the 897 measured deep exceptions from the handoff.
The frozen deep/frame files, all SHA pins, and both exception maps retain their bytes.
No broad allowance or checker change was made.

port-weq: the 35 foreign equation exports remain pending. They were not accepted,
removed from the baseline, or remeasured through the blocked current coverage input.
After its merge and the Inhabit repair, run the short complete coverage refresh.

WP12: full independent source state, handlers, duties, matched-cut equivalence,
and claim transfer remain post-landing work under Z. All six restart-permitting
claims need correspondence; NoRestart transfer cannot cover them. Keep AA's
unlock/lock-relation delta and AB's positivity requirement. The spec session must
update the obsolete restart notes after landing.

Not run: default whole-repository build, full compiled FG/FGSA gates and negative
controls, FULL/MERGE, NUC FULL, complete PC-SA baseline refresh, new review,
or final joint WP15/WP16 acceptance. The Inhabit and protected-data blockers prevent
completion of the requested final refresh. Every applied edit stays in the authorized
WP16 data/facade scope, plus the requested ownership-registration edit.

## Files

- AvailableChainFGSA.lean
- docs/ARCHITECTURE.md
- docs/FG-FINALITY-SAFETY-S0-inherited.json
- docs/FGSA-API.md
- docs/FGSA-BLUEPRINT-LEAN.json
- docs/FGSA-PORT-CHANGES.json
- docs/FGSA-PORT-OWNERS.json
- docs/FGSA-PRODUCER-MAP-stage4.md
- docs/FGSA-SEMANTIC-LEDGER-stage4.md
- scripts/AvailableChainCheckSupport/ImportPolicy.lean
- scripts/fgsa-claims-expected.txt
- scripts/import-policy.json
- scripts/import-policy.sh
- scripts/proof-audit-coverage.txt

- docs/FGSA-PORT-FINAL-REPORT.md (this report)

Claude-Session: https://claude.ai/code/session_01QreJ9BuHuNn5MNfMUXRdLN
