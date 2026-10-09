# S0-F / 00b — additive final frame surface

Basis: `cd736e868ef710d87c326ebc220297435a3f79b9`; branch `port-s0f00b`.
Plan: port r2 and binding addendum ruling A, 2026-10-09.

The new modules give the reviewed target for SWITCH. All existing declarations
keep their source text. The canonical aggregate remains hypothesis-free and its
fields retain their present types in this package.

```text
┌────────────────────────────┬────────────────────────┬───────┐
│ Next                       │ Canonical              │ Class │
├────────────────────────────┼────────────────────────┼───────┤
│ frameRNext                 │ frameR                 │ B     │
│ frameRNext_def             │ frameR_def             │ B     │
│ domainRNext                │ domainR                │ B     │
│ domainRNext_def            │ domainR_def            │ B     │
│ RFrameExactNext            │ RFrameExact            │ B     │
│ RFrameExactNext_def        │ RFrameExact_def        │ B     │
│ RFrameNext                 │ RFrame                 │ B     │
│ RFrameNext_def             │ RFrame_def             │ B     │
│ FGFoundationNext           │ FGFoundation           │ B     │
│ TStartNext                 │ TStart                 │ B     │
│ TWalkNext                  │ TWalk                  │ B     │
│ SettledPhaseFrameNext      │ SettledPhaseFrame      │ B     │
│ SettledPhaseFrameNext_def  │ SettledPhaseFrame_def  │ B     │
│ TGeomNext                  │ TGeom                  │ B     │
│ OpeningCoveredNext         │ OpeningCovered         │ B     │
│ FrameAtNext                │ FrameAt                │ B     │
│ FrameClaimNext             │ FrameClaim             │ B     │
│ FGFoundationClaimNext      │ FGFoundationClaim      │ B     │
└────────────────────────────┴────────────────────────┴───────┘
```

`FGFoundationNext` has the same seven fields. Only its frame field uses
`RFrameExactNext`. Constructors and projections inherit class B. The new claims
keep the exact canonical binders and premises. `FrameClaimNext` supplies the
future aggregate frame field; `FGFoundationClaimNext` supplies the future safety
interface field. No Claims module imports another Claims module.

The direct service pieces use only reader substitutions. In the exact frame
statements, displayed reader expansions must also use the Next meaning:

- `fjControlsView` becomes `treeFjControlsView` (guarded contest evidence).
- `domainRNext` filters with `Next.controls`.
- The proposal equation selects slot-s proposals retained in `Next.tree`.
- The voter equation uses `Next.tree`, also for its slot-s ancestor witnesses.
- Carried support resolves cumulatively, then tests membership in `Next.tree`.

These substitutions keep conjunction structure, bounds, scopes, and binders.
Metadata and admission clauses stay fixed. They avoid assertions that a Next
reader equals its old executable expansion. No new F-3 premise is introduced.
`FullVoteService`, `TVote`, and `KernelACSideClaim_W` keep their source text.
The canonical Clean statements remain in their claim home; SWITCH changes only
`CleanCutPosClaim`'s foundation antecedent to `FGFoundationNext`. Its existing
conclusion acquires the new controls through the canonical reader switch.
The canonical interface likewise changes its foundation field type directly;
this package supplies that type without copying an unrelated whole aggregate.

SWITCH deep-digest cause record (all B; attributed to the one h+i+j switch):

- `RFrameExact`, `RFrame`, and both `_def` entries: source stays fixed and becomes
  legacy; their canonical run dependency changes at SWITCH.
- `frameR`, `domainR`, and their `_def` entries; `TStart`, `TWalk`, `TGeom`,
  `OpeningCovered`; `SettledPhaseFrame` and `_def`: guarded canonical controls
  and revised head readers replace the old model dependencies.
- `FrameAt`, `FrameClaim`: the final frame conjunction uses the new targets.
- `FGFoundation`, `.mk`, `.frame`: exact frame field becomes `RFrameExactNext`.
- `FGFoundationClaim`: conclusion becomes `FGFoundationNext`.
- `FGSASafetyClaims`, `.mk`, `.frame`: field becomes `FrameClaimNext`.
- `FGSASafetyInterfaces`, `.mk`, `.fgFoundation`: field becomes
  `FGFoundationClaimNext`.
- `CleanCutPosClaim`: foundation antecedent becomes `FGFoundationNext`.
- All run-dependent new FrameNext entries: unchanged shallow declarations still
  reach the canonical `fgsa` duties. Their deep digests change when those duties
  switch. Local reader-only entries need no exception if their closure is fixed.

WP00c must measure exact old/new digests and one dependency path for each changed
entry, including the full constructor/projection closure and other census roots.
This report gives causes in advance. It is not an allow file and contains no
invented digest. A and C-i are not claimed for these complete bare statements.
Clean contest equality needs the Clean invariant; FaultQ alone is insufficient.
Recovery contest equality needs RXing and the local finality carrier. Neither
context requires equal honest finalized roots.

Registration changes are additive: facade imports, axiom commands, expected
names, coverage rows, and one new statement-order node. The owners stay fixed;
the register records this writer's serial registration handoff and report owner.
The census file remains with WP00a. No V2Manifest or deep-checker code is changed.

Validation results are recorded below.

Exact new entries with a SWITCH run-dependency cause (prefix
`AvailableChain.FGSA.Run.`; each needs a measured B exception):

- `FGFoundationClaimNext` -> canonical `fgsa` duty switch.
- `FGFoundationNext` -> canonical `fgsa` duty switch.
- `FGFoundationNext.cumul` -> canonical `fgsa` duty switch.
- `FGFoundationNext.frame` -> canonical `fgsa` duty switch.
- `FGFoundationNext.geo` -> canonical `fgsa` duty switch.
- `FGFoundationNext.mk` -> canonical `fgsa` duty switch.
- `FGFoundationNext.mono` -> canonical `fgsa` duty switch.
- `FGFoundationNext.reconcile` -> canonical `fgsa` duty switch.
- `FGFoundationNext.store` -> canonical `fgsa` duty switch.
- `FGFoundationNext.strat` -> canonical `fgsa` duty switch.
- `FrameAtNext` -> canonical `fgsa` duty switch.
- `FrameClaimNext` -> canonical `fgsa` duty switch.
- `OpeningCoveredNext` -> canonical `fgsa` duty switch.
- `RFrameExactNext` -> canonical `fgsa` duty switch.
- `RFrameExactNext_def` -> canonical `fgsa` duty switch.
- `RFrameNext` -> canonical `fgsa` duty switch.
- `RFrameNext_def` -> canonical `fgsa` duty switch.
- `TGeomNext` -> canonical `fgsa` duty switch.
- `TStartNext` -> canonical `fgsa` duty switch.
- `TWalkNext` -> canonical `fgsa` duty switch.

The other six new entries are the local `frameRNext`, `domainRNext`, and
`SettledPhaseFrameNext` readers and their `_def` equations. Their Next reader
closures are fixed by Stage 0; WP00c must verify that they stay fixed at SWITCH.

Measured shallow data: all 1,215 prior entries keep their kind and hash.
The manifest has 26 new entries in two new modules, for 1,241 entries in 56 modules.
No added entry needs an allow line under the current append-only manifest rule.
The frozen manifest, frozen SHA, and existing allow file are unchanged.

The manifest tool resets its prose header. The prior WC and ROOT-DIGEST exception
records were restored after generation. The resulting manifest diff contains
only the two new module sections and their 26 entries. No checker code changed.

For deep data, each listed structure cause applies to its complete manifest
closure: the structure, constructor, and every existing projection. A projection
whose displayed type is fixed still reaches the changed structure. In particular,
all `FGFoundation` projections (`store`, `cumul`, `mono`, `frame`, `geo`, `strat`,
`reconcile`) inherit the new frame-field cause. The same rule applies to the
`FGSASafetyClaims` and `FGSASafetyInterfaces` projection families.

Validated source and build checks:

- `bash /Users/francesco/.claude/jobs/22f59f85/tmp/precheck.sh` with this worktree
  and base `91735679`: PASS; printed `PRECHECK PASS`.
- `LEAN_SLOTS=2 lake build --wfail` for both new modules,
  `AvailableChainFGSAClaims.Tests.Axioms`, and `AvailableChainFGSAClaims`: PASS.
- Additional FGSA/Run/Claims/Proofs/Inhabit and KitFG roots built with `--wfail`:
  PASS (3,970 jobs). This closes absent inherited object prerequisites.
- `python3 scripts/check-fgsa-port-owners.py`: PASS (745 exact paths; 71 new;
  99 base proof tests).
- F-13 source guard and independent all-library name scan: PASS; 18 unique
  declared short names.
- Text checks: reader-only copies and exact frame copies match the canonical
  text after the recorded reader/expansion substitutions.
- New source, report, expected-name rows, and coverage rows use lines of at most
  100 characters. `git diff --check` passes.
- Local `log.md`, `state.md`, and `AGENTS.md` remain excluded from Git.

Final checks pass:

- `LEAN_SLOTS=2 bash scripts/check-fgsa-manifest.sh`: PASS; all 1,241 hashes
  match; EOF/copy/SHA and controls C1 through C13 pass.
- Compiled Claims axiom/import/used-constant audit and lease audit: PASS
  (`NEG=0 LEAN_SLOTS=2 bash scripts/check-fgsa-claims.sh` reached both rc 0 rows).
- `LEAN_SLOTS=2 lake build --wfail`: PASS for default targets (4,693 jobs).
  PC-SA source is unchanged; its separate prerequisite build also passed.
- `CheckProofEqns --write-coverage` for Claims Axioms: 741 exact rows; every
  prior row stays fixed; exactly 26 added rows in the two FrameNext modules.
- `CheckProofEqns --baseline scripts/baselines/check-proof-eqns.txt` with
  `--coverage` and `--complete-coverage` for Claims Axioms: PASS; 1,031 proof
  modules, 1,033 exports, zero unaccepted exports.
- `shake-report.sh --fail-on-new` for the two new modules: PASS; no suggestions.
- `CheckWeakContinuationW1.lean` with warnings as errors: PASS; only propext,
  Classical.choice, and Quot.sound.

The wider Claims guard was not rerun end to end. Its axiom and lease checks
passed before the missing-object stop; its remaining equation check passed
separately on the refreshed default basis. Compiled Claims negative controls
were not run (`NEG=0`). Full multi-audit proof coverage was not rerun; the Claims
audit was checked completely and every other coverage section stays unchanged.

Not run here: the FULL cross-machine landing gate; WP00c frame/deep baseline
checks and their new controls (these files belong to the next package).
No review, agent, Codex/Claude child process, push, or rebase was started.

Compiled axiom/import/used-constant audit: PASS; 10,974 constants, 8,232 theorems,
5,402 modules in the import closure, and 505 direct library-module imports.
The lease audit also passes. The exact requested precheck passed again after
all registrations and the manifest were updated.

The wider `NEG=0 LEAN_SLOTS=2 bash scripts/check-fgsa-claims.sh` run completed
its required axiom and lease audits, then stopped at equation checking because
an inherited PC-SA object was absent (`Clean.BodyRelayTime.olean`). The PC-SA
prerequisite and default builds then passed. Equation coverage, new-module import
checks, and W1 passed separately on that refreshed basis.
The complete wider script is not reported as passing from this partial run.

Changed files:

- `AvailableChainFGSAClaims/Statements/FrameNext.lean`
- `AvailableChainFGSAClaims/Claims/FrameNext.lean`
- `AvailableChainFGSAClaims.lean`
- `AvailableChainFGSAClaims/Tests/Axioms.lean`
- `docs/FGSA-API.md`
- `docs/FGSA-PORT-OWNERS.json`
- `docs/reports/fgsa-port-s0f00b.md`
- `scripts/check-fgsa-claims.sh`
- `scripts/fgsa-claims-expected.txt`
- `scripts/proof-audit-coverage.txt`

Validation logs: `/tmp/s0f-build.log`, `/tmp/s0f-precheck-final.log`,
`/tmp/s0f-manifest-check.log`, `/tmp/s0f-claims-audit.log`,
`/tmp/s0f-eqns-coverage-check.log`, `/tmp/s0f-shake.log`, and `/tmp/s0f-w1.log`.
