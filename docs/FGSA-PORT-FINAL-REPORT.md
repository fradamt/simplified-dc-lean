# port-w16 — FG-SA checker data and attribution, first pass

Data commit: `618886b39638eb8818d1e57f28408d8a28bfaea9`. Name/facade commit: `63b98347`.
Branch: `port-w16`. Source base: `c6b442c98e2c69451f775fdcc924fceadf1058f9`.
Precheck base: `318074ba`. Date: 2026-10-09.

The available data repairs are committed. The required precheck remains red.
Eleven exact guard-list rename records need a scope extension. The unchanged source
check also rejects engine references in WP12b's Spec.Simulation. The final WP15/WP16
unit is pending. This report is TARGET and data evidence.

Files in the two data commits:

- `AvailableChainFGSA.lean`
- `docs/ARCHITECTURE.md`
- `docs/FG-FINALITY-SAFETY-S0-inherited.json`
- `docs/FGSA-PORT-CHANGES.json`
- `docs/FGSA-PRODUCER-MAP-stage4.md`
- `docs/FGSA-SEMANTIC-LEDGER-stage4.md`
- `scripts/AvailableChainCheckSupport/ImportPolicy.lean`
- `scripts/fgsa-claims-expected.txt`
- `scripts/import-policy.json`
- `scripts/import-policy.sh`
- `scripts/proof-audit-coverage.txt`

This report is also stored at `docs/FGSA-PORT-FINAL-REPORT.md`. Local notes and evidence
are excluded from Git. Each data row and source contract is attributed in
`docs/FGSA-PORT-CHANGES.json`; 110 rows lack available review evidence and stay pending.
A null reviewed commit is explicit. It is not an inferred review pass.

The facade now imports Spec.Simulation and Spec.Transfer. The exact Run.Model.Protocol
import is registered in the JSON policy and both generated policy files. No proof family
module was repaired by WP16. The generated ImportPolicy module builds.

Eleven stale expected names were replaced. Nineteen stale coverage names were replaced;
42 active audit commands were added. Nineteen new public proof helpers were also added
to the expected list. All 63 distinct changed names resolve in their compiled owning
modules. Their transitive axiom sets contain only propext, Classical.choice, and Quot.sound.
The complete coverage inventory has 6,680 rows and 14 audits; its full compiled check
remains blocked by an absent export object file.

The attribution ledger also records 54 inherited shallow changes, 897 deep exceptions,
five frame exceptions, 184 source contracts, and six frame source contexts. Source
records include the permitted N/P/Q/R/S/T/V changes and the WP12a spec changes.
The data task changed no theorem statement, claim premise, conclusion, bound, or read scope.
Source contract records do not infer kernel fingerprints from source text.

The documented generator was run with `--scope fgsa --write`. All 1,242 entry rows
in 57 modules were identical to the current checked manifest. Historical exception prose
was preserved. `docs/FGSA-API.md` has no byte change. The frozen API, frame/deep data,
their SHA files, and their exact exception maps retain their original bytes.
The deep check passes with 897 exact exceptions; the frame check passes with five.

Seven new S0 byte changes are recorded with actual commit parents and before/after hashes.
There is one separate core first-pass package. The fixed S0 byte revision is `63b98347`;
later data commits change no S0 path. History verifies 41 changes across 18 differing
paths. Both frozen S0 manifests retain their bytes.

Before/after checks:

```text
┌────────────────────────────┬────────────────────────────┬──────────────────────────────┐
│ Check                      │ Before                     │ After                        │
├────────────────────────────┼────────────────────────────┼──────────────────────────────┤
│ Required precheck          │ FAIL: 2 facade imports     │ FAIL: 11 guard records       │
│ Base / diff check          │ PASS                       │ PASS                         │
│ Guard-list superset        │ PASS                       │ 11 rename records pending    │
│ Import-policy generator    │ PASS                       │ PASS; exact Run import       │
│ Layers / module headers    │ PASS                       │ PASS; 0 new findings         │
│ Expose / transparency      │ PASS                       │ PASS                         │
│ 19 source GLY rules        │ PASS                       │ PASS; F-3/F-13 pass          │
│ FGSA source checks         │ Missing Spec imports       │ WP12b engine refs fail       │
│ Run / claims source checks │ PASS separately            │ PASS separately    │
│ Current shallow API        │ PASS: 1,242 entries        │ PASS; regenerated rows equal │
│ Frame / deep               │ PASS; 5 / 897 exceptions   │ PASS; baselines unchanged    │
│ S0 bytes                   │ FAIL: 7 differences        │ PASS: 122 paths; 18 diffs    │
│ S0 history / packages      │ No core port package       │ PASS: 41 changes; 17         │
│                            │                            │ packages                     │
│ Changed compiled names     │ Not run                    │ PASS: 63 names; 20 modules   │
│ Finality source coverage   │ PASS                       │ PASS: 24 modules; 221 decls  │
│ Complete proof coverage    │ Not run                    │ Blocked: missing export      │
│                            │                            │ olean                        │
│ Old-read audit             │ Missing Outage.Close olean │ Pending complete closure     │
│ P13 blueprint map          │ Not run                    │ Missing Assembly.Outage      │
│                            │                            │ olean                        │
│ WP16 edit ownership        │ Not run                    │ PASS: only 49-path scope     │
└────────────────────────────┴────────────────────────────┴──────────────────────────────┘
```

Baseline S0 failures were these seven paths:

- `AvailableChainFGSAClaims/Claims/Clean.lean`
- `AvailableChainFGSAClaims/Claims/Foundations.lean`
- `AvailableChainFGSAClaims/FGSAClaims.lean`
- `AvailableChainFGSAClaims/Statements/ComposeStmt.lean`
- `AvailableChainFGSAProofs/Tests/Axioms.lean`
- `docs/FGSA-API.md`
- `scripts/fgsa-manifest-allow.txt`

The final required precheck fails at guard-lists, exit 1. Each removed name has its
replacement, reason, and source commit in the ledger. The missing exceptions are for
these old names, all with prefix `AvailableChain.FGSA.Run.`:

- `healing_phase_contest_persist`
- `healing_phase_order`
- `fgsa_domainR_eq_storeFrameView`
- `fgsa_walk_domain_of_witness_view`
- `fgsa_domain_witness_of_mem`
- `fgsa_score_eq_on_clean`
- `fgsa_score_eq_on_recovery`
- `fgsa_rFrameExact`
- `fgsa_rFrame`
- `domainR_eq_storeFrame`
- `frontierSearch_phase_step`

The one-file patch is `claude-files/port-w16-guard-lists.patch`. It passes the unchanged
superset checker when supplied as scratch allow data. It is not applied to the repository:
`scripts/guard-lists-allow.txt` is owned by lean-framework and is outside the 49 WP16 paths.
The scope-extension question is pending. No blanket allowance was added.

The requested commands were run:

```sh
bash /Users/francesco/.claude/jobs/22f59f85/tmp/precheck.sh \
  /Users/francesco/.claude/jobs/22f59f85/tmp/wt-pcsa-formation 318074ba
python3 -B scripts/check-fg-finality-freeze.py --check
```

Final results: precheck exit 1; S0 bytes exit 0. Supplementary source diagnostics run
without a base still enforce the source checks; they stop at the WP12b engine boundary.
They are not a replacement for the required guard-list check.

Build evidence:

```sh
LEAN_SLOTS=2 lake build --wfail AvailableChainFGSA \
  AvailableChainFGSARun AvailableChainFGSAClaims
# exit 0; 3,430 jobs
LEAN_SLOTS=2 lake build --wfail AvailableChainCheckSupport.ImportPolicy
# exit 0; 2 jobs
LEAN_SLOTS=2 lake build --wfail AvailableChainFGSAProofs.Tests.Axioms
# exit 1; 3,743-job graph; four external modules fail
```

Compiled data evidence:

```sh
LEAN_SLOTS=2 lake env lean --run scripts/V2Manifest.lean --scope fgsa --check
# exit 0; 1,242 entries; 57 modules
LEAN_SLOTS=2 lake env lean --run scripts/V2Manifest.lean --scope fgsa --write
# exit 0; generated entry rows equal
LEAN_SLOTS=2 lake env lean --run scripts/V2Manifest.lean --scope fgsa --deep --check
# exit 0; 1,242 roots; 897 exact exceptions
python3 -B scripts/fgsa-deep.py --frame-check
# exit 0; 43 entries; five exact exceptions
LEAN_SLOTS=2 lake env lean --run scripts/CheckBlueprintClaims.lean \
  claude-files/port-w16-names-request.txt
# exit 0; 63 exact names; 20 owners; standard axioms only
python3 -B scripts/check-fg-finality-freeze.py --history
# exit 0; 122 paths; 18 differences; 41 changes
python3 -B scripts/check-fg-finality-freeze.py --packages
# exit 0; 17 packages
```

The first history run found six path-history parent IDs. These were corrected to the
actual commit parents. All before/after byte hashes were correct; the final history check passes.
A sandbox build could not write the shared Lean slot locks. Only this job's blocked
processes were stopped; the build was rerun with normal shared slot access and LEAN_SLOTS=2.
No other writer's process was stopped. No throttle bypass was used.

Next failures outside WP16 source ownership:

- WP12b: `AvailableChainFGSA/Proofs/Spec/Simulation.lean:27` uses Run.fgsa;
  later lines use Run.Node. The existing Q1/Q5 boundary rejects those engine references.
  WP12b must resolve the module boundary. WP16 keeps the required facade imports and checker.
- WP08: `Proofs/OutageContinuation/Export.lean:30:31`: outageV_body still has the
  legacy frame telescope where the caller supplies RFrameExactNext.
- WP15, dependent on WP08: `Proofs/Assembly/Outage.lean:25:30`: legacy/canonical
  frame type mismatch.
- WP15, dependent on WP10: `Proofs/Assembly/WeakContinuationGrowth.lean:689:59`:
  the interface expects RFrameExact while the caller supplies RFrameExactNext.
- WP15, dependent on WP10: `Proofs/Assembly/WeakContinuation.lean:720:61`:
  wc_seededLiveAt still expects the legacy frame.

The last four paths have prefix `AvailableChainFGSAProofs/`. Their first errors and
commands are preserved in `.lake/port-w16/port-w16-coverage-build.log`.

Cross-WP obligations remain explicit in the ledger. WP08 and WP10 own the active ruling-V
migration; WP12b owns the ruling-U simulation and engine-boundary repair; WP15 owns closed
assembly. WP16 must then run the complete old-read and coverage checks and refresh P13
supplier fingerprints and aggregate binder counts with independent hypothesis-free validation.
Existing supplier scopes, names, and unrelated OPEN items are preserved.

The old-read checker exits 1 before scanning. Initially Outage.Close.olean was absent;
after the proof build, OutageContinuation.Export.olean is absent. The known
stale height row is fgsa_walkRun_path_domain; its guarded replacement must be measured by
the full old-read audit before changing that row. WCProposalPivot stays height-only.
The coverage checker exits 2 at a missing OutageContinuation.Export.olean.
The P13 map check exits 2 at a missing Assembly.Outage.olean. No unmeasured P13 value is written.
`fg-expected.txt` needs no change in the unchanged Simplex/KitFG source scope.

Not run: full FG/FGSA gates or negative-control suites, NUC FULL, final joint WP15/WP16 gate,
complete expected-name aggregate auditor, final P13 regeneration, final PC-SA compiled baseline,
and complete source-census reconciliation with the final compiled closure. No push, rebase,
agent, or review process was started. The task edits only WP16 paths; the guard patch stays local.

Evidence is in `.lake/port-w16/`. Current state is in `state.md`; session history is in `log.md`.

Claude-Session: https://claude.ai/code/session_01QreJ9BuHuNn5MNfMUXRdLN
