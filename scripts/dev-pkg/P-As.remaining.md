# P-As Round 4 — remaining targets

Base: 3a538409. Full P-As remains OPEN. There are 24 open targets of 65.
The target map has 41 GREEN targets. Its full map has 501 GREEN and
26 EXPECTED-FAIL entries, including two inherited S-Ap entries outside TARGETS.
P = AvailableChainFGSAProofs; I = AvailableChainFGSAInhabit.
Every B key below links to the exact source type and owner in
[P-As.blocker-types.md](P-As.blocker-types.md). Healing targets are OUT OF SCOPE.
The WC assembly modules, Interfaces/Safety/GrowthAxioms, full W1 and its consumers are GREEN.
No P-WC proof request remains. The exact FAST producer remains P-Fd-owned.

```text
┌──────────────────────────────────────────────┬──────────┐
│ Remaining target                             │ Requests │
├──────────────────────────────────────────────┼──────────┤
│ P                                            │ 6        │
│ P.Proofs.Assembly.Clean                      │ 4        │
│ P.Proofs.Assembly.Healing                    │ 1        │
│ P.Proofs.Assembly.Outage                     │ 3        │
│ P.Proofs.Assembly.ResetArrival               │ 1        │
│ P.Proofs.Assembly.Root                       │ 5        │
│ P.Tests.Axioms                               │ 6        │
│ P.Tests.FGCompose                            │ 6        │
│ P.Tests.HealingAttempt                       │ 1        │
│ P.Tests.HealingHTime                         │ 1        │
│ P.Tests.HealingReset                         │ 1        │
│ P.Tests.LiveDC                               │ 6        │
│ P.Tests.NonVacuity.Adversarial               │ 1        │
│ P.Tests.NonVacuity.FinalityClaims            │ 1        │
│ P.Tests.NonVacuity.HealingClaims             │ 1        │
│ P.Tests.NonVacuity.HealingFirst              │ 1        │
│ P.Tests.NonVacuity.HealingPackages           │ 1        │
│ P.Tests.NonVacuity.HealingReset              │ 1        │
│ P.Tests.NonVacuity.HealingRun                │ 1        │
│ P.Tests.OutageContinuationAxioms             │ 4        │
│ P.Tests.OutageContinuationInhabit            │ 4        │
│ P.Tests.OutageExport                         │ 3        │
│ P.Tests.WeakContinuationGrowthAssemblyAxioms │ 1        │
│ P.Tests.Zero                                 │ 4        │
└──────────────────────────────────────────────┴──────────┘
```

- `AvailableChainFGSAProofs`: B02, B03, B04, B19, B20, WCROOT.
- `AvailableChainFGSAProofs.Proofs.Assembly.Clean`: B02, B04, B19, B20.
- `AvailableChainFGSAProofs.Proofs.Assembly.Healing`: B03.
- `AvailableChainFGSAProofs.Proofs.Assembly.Outage`: B02, B19, B20.
- `AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival`: B03.
- `AvailableChainFGSAProofs.Proofs.Assembly.Root`: B02, B03, B04, B19, B20.
- `AvailableChainFGSAProofs.Tests.Axioms`: B02, B03, B04, B19, B20, WCROOT.
- `AvailableChainFGSAProofs.Tests.FGCompose`: B02, B03, B04, B19, B20, WCROOT.
- `AvailableChainFGSAProofs.Tests.HealingAttempt`: B03.
- `AvailableChainFGSAProofs.Tests.HealingHTime`: B03.
- `AvailableChainFGSAProofs.Tests.HealingReset`: B03.
- `AvailableChainFGSAProofs.Tests.LiveDC`: B02, B03, B04, B19, B20, WCROOT.
- `AvailableChainFGSAProofs.Tests.NonVacuity.Adversarial`: WCROOT.
- `AvailableChainFGSAProofs.Tests.NonVacuity.FinalityClaims`: WCROOT.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingClaims`: B03.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingFirst`: B03.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingPackages`: B16.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingReset`: B17.
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingRun`: B03.
- `AvailableChainFGSAProofs.Tests.OutageContinuationAxioms`: B02, B04, B19, B20.
- `AvailableChainFGSAProofs.Tests.OutageContinuationInhabit`: B02, B04, B19, B20.
- `AvailableChainFGSAProofs.Tests.OutageExport`: B02, B19, B20.
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms`: WCROOT.
- `AvailableChainFGSAProofs.Tests.Zero`: B02, B04, B19, B20.

The completed source seed and participation ports keep the selected H0 join cutoff.
The source endpoint is inclusive; continuation participation begins strictly after it.
The growth and empty routes derive cached proposal coverage from the original gate result.
No continuation participation or half-cap is added to the empty route.

Root and WeakContinuationGrowthAssemblyAxioms remain OPEN under the inherited family
imports and WCROOT/FAST. The local component strict audit is GREEN. The exact public
claim definitions are unchanged. A conditional internal supplier is not a closed claim.

Outage/Clean and their fixtures keep the exact P-Cl2/P-Ar/P-Ou requests in the blocker
register. No universal service field is supplied to replace a missing family proof.
Header checks have the same five inherited P-Ar/P-Ou import-all failures.

initialAt has no remaining W1 use. The Adversarial consumers at :1889-1891 and
:2981-2983 remain blocked by Root. Keep the Store/LeaseOutput/Metadata/StoreInv and
AncestorDeadlinesStore helpers until those consumers are repaired. No definition or
tracked note is deleted. Bare P23, final Root/FGSAClaims acceptance, G-S2 and final
SLEEP-1 regeneration remain OPEN.
