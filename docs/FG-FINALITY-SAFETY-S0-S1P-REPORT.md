# FG finality safety: S0, S1, S1P

S0/S1 commit: `78b736b`. All contracts are PROVISIONAL.
The S1P commit contains independent laws and the recorded lane STOP.
S2 has not started. No push, review, or agent process was started.

S0 records the fixed 2d5b47a input, step-1 API, source and guard hashes,
and the lead acceptance of Opus finding 10. HEAD 88c616d had the same tree.
All frozen FG-SA Statements/Claims, PC-SA claim sources, manifest policy,
pins, allow files, and frozen audits keep their bytes.

S1 adds SafetyReads, SafetyStore, SafetyClient, and SafetyClaims in Compose.
It adds FGSafetyReads, FGSafetyWireLaws, FGSafetyStoreLaws,
FGSafetyOrderLaws, FGSafetyScopeLaws, FGSafetyClientLaws, and
FGSafetyUnitLaws. It adds fourteen read/predicate definitions and their
proved owner equations. There are 76 new public names and
projections. The six planned theorem types check as propositions.
There are no unproved theorems or generic safety proof modules.
The exact S1 guard/inventory diff is in FG-FINALITY-SAFETY-S1-guards.patch.
S1 changes no import-policy.json, check-gly-rules.py, or allow-list line.

For both `.on` and `.idle`, S1P proves:

- All five FGSafetyWireLaws fields. Encoding is injective. Decode/encode,
  authentication, visibility, and exact proposal carriage agree.
- Initial, clock, process, restart, and own-record equations.
- initial_tf and restart_tf, without a Reachable premise.
- Erasure prefix and output equality, the two independent order fields.
- Source membership and own-core equality for the mode-general core read.

The `.on` core read equals the old pcsaCoreReads by a proved owner bridge.
Both seat equivalences are Equiv.refl. Producer signature checks cover
FG-SA and both PC modes. No new premise or cast is needed.
The PC finality view equals FG-SA's window view. The PC certificate record
uses FGSA.fgCertificateLaws, a shared model fact. It uses no FG-SA run claim.
The local lease-deletion fact preserves fg, proposals, and rowPool.

Exact theorem and definition axiom sets are in S1P-axioms.json, under the
full file name FG-FINALITY-SAFETY-S1P-axioms.json. Every set is a subset of
`propext`, `Classical.choice`, and `Quot.sound`. General mode proofs and
explicit `.on`/`.idle` instantiations use the same axiom sets.

The invariant and process_new drafts are in FG-FINALITY-SAFETY-PC-DRAFTS.md.
They start from Reachable and a local ViewRootInj induction. They list the
accepted packed-body/row correspondence and exact named-body obligations.
The named scope uses full PC payloads, including attachments. Emitted tips
need a stored named parent; the emitted-only tip is not placed in Q.
The order citation is pcsa_admitBlock_fg_cases in AcFrame/Store.lean:69–85.
Acceptance tests use the original state. Lease deletion precedes the FG
window update. Reconciliation and collection do not write FG.

STOP: the existing PC LANE rule rejects this required direct import:

```text
AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore
  → AvailableChainPCSAProofs.Proofs.AcFrame.Store
```

The exact required line is:

```text
public import AvailableChainPCSAProofs.Proofs.AcFrame.Store
```

The plan does not list this lane exception. It was not added.
process_F and the complete FGSafetyOrderLaws record are not proved.
The lead must approve the exact edge or arrange a lower helper extraction.
Full PC invariant, insertion metadata, named/emitted-parent scope,
core metadata growth, and client tick_rows remain open. FG-SA stays on its
existing claim path. S1P is partial because of this STOP.

S1P guard changes are exact. The only new Compose adapter pairs are:

```text
AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
  → AvailableChainFGCompose.Statements.SafetyClient
  → AvailableChainFGCompose.Statements.SafetyStore
AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient
  → AvailableChainFGCompose.Statements.SafetyClient
  → AvailableChainFGCompose.Statements.SafetyStore
```

import-policy.json laneUpstream adds only those two named Statements paths.
The claims direct-import guard uses the same COMPOSE_EDGES exact-pair table.
It adds no broad prefix allowance.
The new PC adapters permit direct FG-SA imports only of Proofs.Carrier and
Proofs.StoreLaws. FG-SA run imports and their neighboring paths are rejected.
The AcFrame lane remains rejected. Existing Claims and Run edges stay fixed.
There is no check-gly-rules or F-3/F-13/GEN-FIRST allow-list change.
Checker code in S1P, with reasons:

- scripts/check-layers.py adds the four exact adapter-to-Statements pairs
  listed above. It also restricts the two new PC adapters to the named
  FG-SA Carrier and StoreLaws producers. This prevents FG-SA run dependencies.
- scripts/import-policy.json adds SafetyClient and SafetyStore to
  laneUpstream. check-layers.py still requires the exact importer pairs.
- scripts/check-fgsa-claims.sh consults the existing shared COMPOSE_EDGES
  table. The FG-SA adapter needs those exact imports for its signatures.
  The former check rejected them before the audit-pool self-test could run.
- scripts/gate.sh adds FGSASafety-axioms and PCSASafety-axioms. The two
  new adapter audit modules must run in the gate.
- scripts/full-pass.py requires both new audit steps in a FULL receipt.
  An omitted or failed adapter audit must prevent a FULL result.
- scripts/check-proof-coverage.py adds both adapter audits to AUDITS.
  scripts/proof-audit-coverage.txt records each new name and its owner.
- scripts/check-layers-selftest.sh rejects adjacent .Extra imports,
  PC adapter imports of FG-SA run proofs, and the AcFrame lane edge.
  These controls test the new exact boundaries and preserve the lane STOP.

There is no S1P change to scripts/CheckFGAxioms.lean or check-gly-rules.
The exact S1P checker and inventory diff is in
FG-FINALITY-SAFETY-S1P-guards.patch.

S0/S1 validation passed before commit. Its complete results are in the S1
notes. The full S1P pre-commit list passes. The affected modules and full
build pass with --wfail. check-build.sh, the layer check, check-gly-rules,
and precheck.sh . pass. CheckProofEqns checks 742 proof modules and 1,033
existing exports, with zero unaccepted. Coverage checks 4,764 declarations
in 13 audits. The Compose closure checks 256 constants in 13 source modules.
Archive pins, FG-SA model/Run/Claims, FG-SA/V2/Generic manifests, and
CatalogLock pass. Claims checks use NEG=0. No required audit is skipped.
All 122 frozen hashes match. The explicit S1P axiom audits match all 39
saved declaration sets exactly. All sets use standard axioms only.
Validation log: /private/tmp/fg-fin-resume-full.log. The first resumed claims
check also passes: /private/tmp/fg-fin-resume-claims-before.log.

Resume fix: the previous claims/build run ended at unused-imports, rc 1.
Shake reported four new removals in Shared/FGSafetyClient. The adapter
now imports Run.Statements.Client for decodeRowObject. It uses supported
shake keep comments on the three imports needed by anonymous producer
signature checks. No shake baseline or checker rule was changed for this fix.
The S1 guard patch keeps its original bytes; its reformat was removed.

Frozen read-owner decision: keep the new reads and their _def theorems
in AvailableChainFGSARun/Model/Protocol.lean and
AvailableChainPCSARun/Model/Protocol.lean. Neither file is in the 122-file
frozen set. All frozen file hashes match. The five step-1 Lean API modules
keep their bytes. The FG-SA manifest/API check reports 1,174 entries in
50 modules, complete, with matching hashes. No frozen check objects.

The affected-module build passes with --wfail. The focused Shake command
then found stale downstream build files. The full repository build
rebuilds those files before the required Shake and claims checks.
