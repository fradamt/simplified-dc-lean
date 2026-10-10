# P-As Round 5 — remaining targets

Base: 7a30ce82. Full P-As remains OPEN; healing is OUT OF SCOPE.
44/66 targets are GREEN; 22 remain OPEN. The full map has 504 GREEN and
24 EXPECTED-FAIL entries, including two inherited S-Ap roots outside TARGETS.
Exact types and source locations: [P-As.blocker-types.md](P-As.blocker-types.md).

Clean assembly and Tests/Zero are now GREEN. The new independent
Tests/OutageAssemblyAxioms consumer composes the produced P-Ar prefix receipt
with P-Ou's restored receipt constructor. B02, B19, B20 and ZERO-BASE are retired.
No P-Cl2, P-Ar or P-WC producer request remains. FAST stays the one exact P-Fd request.

The following list is the complete EXPECTED-FAIL target set. HEAL means the deferred
P-H1/P-H2 closure or fixture port, with B03/B16/B17 retained in the blocker register.
ROOT means the full Root import (FAST, deferred H-time, and open P-Ou exports).
No conditional assembly adapter is marked as a closed public claim.

- `AvailableChainFGSAProofs`: ROOT.
- `AvailableChainFGSAProofs.Proofs.Assembly.Healing`: HEAL.
- `AvailableChainFGSAProofs.Proofs.Assembly.Outage`: OU-CLOSE, OU-INPUTS, OU-SCOPES, conditional growth callbacks; B04/OU-CONT import.
- `AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival`: HEAL.
- `AvailableChainFGSAProofs.Proofs.Assembly.Root`: ROOT.
- `AvailableChainFGSAProofs.Tests.Axioms`: ROOT.
- `AvailableChainFGSAProofs.Tests.FGCompose`: ROOT.
- `AvailableChainFGSAProofs.Tests.HealingAttempt`: HEAL.
- `AvailableChainFGSAProofs.Tests.HealingHTime`: HEAL.
- `AvailableChainFGSAProofs.Tests.HealingReset`: HEAL.
- `AvailableChainFGSAProofs.Tests.LiveDC`: ROOT.
- `AvailableChainFGSAProofs.Tests.NonVacuity.Adversarial`: ROOT.
- `AvailableChainFGSAProofs.Tests.NonVacuity.FinalityClaims`: ROOT.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingClaims`: HEAL.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingFirst`: HEAL.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingPackages`: B16 (HEAL).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingReset`: B17 (HEAL).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingRun`: HEAL.
- `AvailableChainFGSAProofs.Tests.OutageContinuationAxioms`: B04, OU-CONT, ROOT.
- `AvailableChainFGSAProofs.Tests.OutageContinuationInhabit`: OU-FIXTURE STOP (invalid inherited sleep trace); current premise port.
- `AvailableChainFGSAProofs.Tests.OutageExport`: OU-CLOSE, OU-INPUTS, OU-SCOPES, conditional growth callbacks; B04/OU-CONT import.
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms`: ROOT.

The exact WC Root caller bodies are prepared in Root:137/:158 and pass strict extraction.
They retain the selected H0 cutoff, source FAST and the actual continuation FAST.
The empty suffix uses no added participation or fault cap. Root's unconditional
callers stay open until P-Fd FAST is merged and deferred family closure is available.
The two safety aggregate bodies pass the same extracted audit; this does not close Root.

Clean no longer imports the outage continuation family. The unchanged
fgsa_outageContinuationClaim is now Root-owned; its full audit remains EXPECTED-FAIL.
The independent receipt check proves a complete receipt record, not continuation induction.
P-Ou still owns full restored/after-E induction, Close, both Exports, and Clean inclusion/growth.
No missing family proof is invented at assembly.

Headers PASS. Layers have 72 inherited findings and zero new. Public Claims/Statements
are unchanged. Bare P23, G-S2, final regeneration and deferred initialAt consumers remain OPEN.
