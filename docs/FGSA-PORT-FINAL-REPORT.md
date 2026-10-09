# port-w16b — FG-SA checker data and attribution, second pass

Data tip: `6e53b413`. Earlier data commits: `02f5ac9a`, `45db161d`.
Branch: `port-w16b`. Source base: `e961df941261be5f421a03ae80635d1806a516e9`.
Original attribution base: `c6b442c9`. Required precheck base: `318074ba`.
Date: 2026-10-09. This report records the pre-Y/pre-WP12d source base.

The freeze check passes. The required precheck does not pass: Spec.Simulation still
imports Engine Duty.Schedule. Item 2 awaits the WP12d source merge. Complete coverage
also fails on 35 unaccepted source equation exports. That source repair is outside
WP16 ownership. No checker or proof-equation baseline was changed to accept them.

The authorized data work on this base is committed. Items 1, 3, 4 and 6 are done.
Item 5 is measured for this base. Its Y and WP12d parts remain pending.

## Files

- docs/ARCHITECTURE.md
- docs/FG-FINALITY-SAFETY-S0-inherited.json
- docs/FGSA-BLUEPRINT-LEAN.json
- docs/FGSA-PORT-CHANGES.json
- docs/FGSA-PRODUCER-MAP-stage4.md
- docs/FGSA-SEMANTIC-LEDGER-stage4.md
- scripts/baselines/fgsa-old-reads.txt
- scripts/fgsa-claims-expected.txt
- scripts/guard-lists-allow.txt
- scripts/proof-audit-coverage.txt
- docs/FGSA-PORT-FINAL-REPORT.md (this report)

No proof module or claim source was edited. No claim premise, conclusion, bound or
read scope changed in this job. The 11-line guard edit is exactly the approved patch.
All other edited paths belong to WP16. Local evidence and notes remain excluded from Git.

## Attribution repairs and measurements

Fourteen change commits are corrected. Six ScoreRun statement changes, including
fgsa_scoreRun_raw_subset and scoreRun_carried_support, now cite `3e53d37b`.
Seven earlier canonical additions now cite `1a4b2db1`; they do not inherit approval
from the later guarded-helper review. wc_treeFrameAncestry cites `d57ce9b7`, with
reviewed snapshot `64210bd3`. Prior review snapshots remain explicit historical data.

Every recorded source statement is complete. Top-level let assignments are retained;
structure records stop before section commands. The missing S2 record for
outageV_covering_head_receipts compares `876ecff1` with its actual parent.
WP16 documentation records no longer cite the SWITCH review.

All 69 source-review rows listed in rev-port-w16-astra are closed. Later explicit
reviews cover the merged WP08, WP10, WP12b/c and WP13v2 source changes. The ledger
records 49 source-file change events since c6b442c9, including unchanged-header proof
changes. Its 301 source-contract records do not infer a kernel fingerprint from text.
There are 253 rows with pending review status, including the new WP16 data records.
Each gives an exact reason. A source review does not certify a later data edit.

All 2,578 expected names resolve: 2,527 existing names and 51 new partial Spec helpers.
The first measurement found those 51 absent in stale Spec objects. Building the FGSA
facade rebuilt Simulation and Transfer; the new names then passed. The other 33
coverage-only names were also measured. Transitive axioms are standard throughout.
The 142 existing expected/audit attribution rows now have current compiled evidence.

The coverage generator measured 6,681 rows in 14 audits. Its only semantic inventory
change is the added healing_domain_filter_F row. All 6,680 prior rows remain. The
addition cites helper change `041b6360`, its WP09b review, and audit registration
`fd5a2613` with its WP13v2 review. Original row order and unrelated bytes are preserved.
Generation is data evidence; the normal coverage check still fails on source exports.

The complete old-read audit scans 10,188 constants in 519 active modules. Six missing
height rows are added and five stale height rows are removed. Every change has source
and measured classification evidence. The six old/finality allow rows stay fixed;
there are 244 height rows. All controls pass. WCProposalPivot stays height-only.

P13 has 176 refreshed supplier rows. Both removed phase-order references use the
approved _of_crossing replacement. The entries stay PARTIAL and the RXing scope is
explicit. Every changed fingerprint has a measured path to changed source dependencies,
with owning source paths, change commits and compiled node hashes. The 118 distinct
FGSA suppliers were measured. fgsaClaims has fingerprint `681bb87fc2d918fa`, one binder,
and zero proposition binders at all three map locations. All 36 OPEN items remain.
The normal P13 check passes, including the unchanged PC-SA map.

Independent direct witnesses compile for FGSAClaims and all six restart-permitting
claims from Params alone. The claim source diff against e961df94 is empty.
The witnesses and supplier audits use only propext, Classical.choice and Quot.sound.

The documented API generator was run. All 1,242 generated entry rows match. Historical
exception prose was retained, so docs/FGSA-API.md has no final byte change. Shallow,
deep and frame checks pass with the existing 897 deep and five frame exceptions.
All fixed manifests, SHA files and exception maps retain their bytes.

The exact S0 history now has 44 records and 20 packages. The byte pin is `45db161d`:
122 paths, 19 recorded differences. This includes the new Tests/Axioms bytes, approved
guard edit and measured old-read edit. Actual parents and before/after hashes pass.
Ruling Y's Reachable freeze record is pending its source merge; no value was guessed.

## Before/after checks

```text
┌────────────────────────────┬──────────────────────────┬─────────────────────────────┐
│ Check                      │ Before                   │ After                       │
├────────────────────────────┼──────────────────────────┼─────────────────────────────┤
│ Required precheck          │ FAIL: 11 guard records   │ FAIL: pending Spec boundary │
│ Guard-list check           │ FAIL: 11 removals        │ PASS: exact approved edit   │
│ Freeze bytes               │ FAIL: Tests/Axioms       │ PASS: 122 paths, 19 diffs   │
│ Freeze history / packages  │ Missing current history  │ PASS: 44 records / 20       │
│ FGSA source check          │ FAIL: Engine import      │ FAIL: same import, line 5   │
│ Proofs / Run build         │ Not run on this base     │ PASS: 3,856 jobs            │
│ FGSA facade build          │ Spec objects stale       │ PASS: 3,276 jobs            │
│ Fixed audit targets build  │ Coverage inputs missing  │ PASS: 4,152 jobs            │
│ Extra checker roots build  │ 3 KitFG objects missing  │ PASS: 3,137 jobs            │
│ Complete expected names    │ 51 names missing         │ PASS: all 2,578 names       │
│ Coverage inventory write   │ 6,680 rows               │ PASS: 6,681 rows, 14 audits │
│ Normal complete coverage   │ Missing object input     │ FAIL: 35 source exports     │
│ Old reads and controls     │ 6 missing / 5 stale      │ PASS; pivot stays height    │
│ P13 map                    │ FAIL: 176 errors         │ PASS; OPEN items retained   │
│ Aggregate / six witnesses  │ Not run                  │ PASS: Params alone          │
│ Shallow / API generation   │ First-pass rows          │ PASS: all 1,242 rows match  │
│ Deep / frame               │ PASS: 897 / 5 exceptions │ PASS; fixed data unchanged  │
│ Finality source coverage   │ PASS                     │ PASS: 24 modules, 221 decls │
│ Run / Claims source checks │ PASS                     │ PASS                        │
│ Ownership / whitespace     │ PASS                     │ PASS                        │
└────────────────────────────┴──────────────────────────┴─────────────────────────────┘
```

The exact commands and exits are in the ledger's 23 port-w16b check records.
Evidence is in `.lake/port-w16b/`. The required commands were run:

```sh
bash /Users/francesco/.claude/jobs/22f59f85/tmp/precheck.sh \
  /Users/francesco/.claude/jobs/22f59f85/tmp/wt-pcsa-formation 318074ba
# exit 1: pending WP12d source boundary; every prior precheck stage passes
python3 -B scripts/check-fg-finality-freeze.py --check
# exit 0
SOURCE_ONLY=1 bash scripts/check-fgsa.sh
# exit 1: Engine Duty.Schedule import at Spec/Simulation.lean:5
LEAN_SLOTS=2 lake env lean --run scripts/CheckFGSAOldReads.lean --controls
# exit 0, including the repeat after the Spec object rebuild
LEAN_SLOTS=2 python3 -B scripts/check-proof-coverage.py
# exit 1: 35 unaccepted source equation exports; first audit stops the run
LEAN_SLOTS=2 python3 -B scripts/check-proof-coverage.py --write
# exit 0: full 14-audit inventory; one exact added row retained
LEAN_SLOTS=2 python3 -B scripts/check-fgsa-blueprint.py --check
# exit 0
```

## Build evidence

All builds used LEAN_SLOTS=2 and --wfail:

```sh
lake build --wfail AvailableChainFGSAProofs AvailableChainFGSARun
# exit 0; 3,856 jobs; build.log
lake build --wfail AvailableChainFGSA
# exit 0; 3,276 jobs; spec-build.log
lake build --wfail $(cat .lake/port-w16b/audit-targets.txt)
# exit 0; 4,152 jobs; audit-build.log; 14 fixed audit targets
lake build --wfail AvailableChainKitFG.TreeCorrespondence \
  AvailableChainKitFG.TreeFrameGeometry AvailableChainKitFG.TreeTwoChanges
# exit 0; 3,137 jobs; coverage-extra-build.log
```

The first sandbox build could not acquire shared slot locks. Only this job's blocked
processes were stopped. The retry used the normal shared wrapper. No throttle bypass,
other-writer process kill, lake update, push, rebase, agent or review process was used.

## Source failures outside ownership

The precheck's first failure is WP12b/WP12d:
AvailableChainFGSA/Proofs/Spec/Simulation.lean:5 imports
AvailableChainEngineV2.Conditions.Duty.Schedule. The move is pending on this branch.

The normal coverage check scans 1,033 proof modules and finds 1,068 exports, of which
35 are unaccepted. The complete names and owners are in
`second_pass.coverage_source_failures` in the ledger. The first error per module is:

- WP12a — AvailableChainFGSA.Proofs.Spec.Handlers: four exports;
  first: AvailableChain.GridCO.confirmationFrom.eq_1.
- WP12b — AvailableChainFGSA.Proofs.Spec.Simulation: 23 exports;
  first: AvailableChain.FGSA.RowWire.decode?.eq_1.
- WP04b — AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay: one export;
  AvailableChain.FGSA.Run.timeIdx.eq_1.
- WP09b — AvailableChainFGSAProofs.Proofs.Healing.PostResetH2Prime: two exports;
  first: AvailableChain.FGSA.Run.D_at.eq_1.
- WP09b — AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseStep: one export;
  AvailableChain.FGSA.Run.D_at.eq_1.
- WP03b — AvailableChainFGSAProofs.Proofs.Shared.ScoreRun: four exports;
  first: AvailableChain.FGSA.proposalsAt.eq_1.

WP16 stops this source repair item. The fixed equation baseline and checker retain
their bytes. An inventory generation pass does not close the normal coverage gate.

## Pending source merges and cross-WP obligations

The wrst and w12d reports arrived during this job and were read. Their source changes
are not on this branch. The task required their data work to remain pending here.

- Y: wrst commits b0b493d8, 3c64a7e2 and 9ef4bc76. After integration, record the
  exact Durable/restore, retained-clock supplier and Reachable changes. Add the actual
  S0 Reachable parent/hash history, then build and measure all affected data. Keep the
  six restart-permitting claims proved. Its report lists test repairs for the test owner.
- WP12d: 7ab64f69. After integration, remove the broad FGSA-to-Run import exception
  and regenerate both policies. Move facade, audit-owner and coverage registrations
  to Run/Proofs/Spec. Measure the four restart theorem replacements and compare the
  complete moved inventory. Its reported facade/reset and RetainedClock issues need
  verification against the integrated source, not acceptance from report text.
- The 35 equation exports require their source owners. A path move alone does not
  establish that the equation-export check passes.
- Z: landing accepts the proved partial correspondence. Full independent source
  interpretation, matched-cut equivalence and claim transfer remain post-landing work.
- X settles row targets as roots at f54e403a. AA's unlock change at cded72bb and AB's
  n ≥ 1 requirement at af218b78 are explicit ledger notes. The later interpreter must
  ignore locks at genesis or Φ.F and supply positivity where unlock existence needs it.
  The landing's WP12a model still cites f54e403a.

Not run: full FG/FGSA gates, FULL/MERGE, NUC FULL, the final joint WP15/WP16 acceptance
unit, final integrated Y/WP12d checks, complete PC-SA port-baseline refresh, or a new
review. The required normal coverage run stops at its first audit on source exports;
all 14 inventory generation processes ran. No acceptance pass is claimed.

Claude-Session: https://claude.ai/code/session_01QreJ9BuHuNn5MNfMUXRdLN
