# P-As round 3 — remaining targets

Base: f5c77257. Full P-As remains OPEN. The register contains all 38 open P-As targets.
The package map also has two S-Ap roots outside TARGETS. GrowthNonVacuity is now GREEN.
P means AvailableChainFGSAProofs; I means AvailableChainFGSAInhabit.
Each B key links to the exact current file:line, declaration type and owner in
[P-As.blocker-types.md](P-As.blocker-types.md). These are failed import boundaries,
not assertions that every theorem in the importing target is false.
Healing targets remain listed for completeness, but are OUT OF SCOPE in this round.

```text
┌──────────────────────────────────────────────┬──────────┐
│ Remaining target                             │ Requests │
├──────────────────────────────────────────────┼──────────┤
│ I                                            │ 2        │
│ I.Tests.Axioms                               │ 2        │
│ I.Tests.WeakContinuationW1                   │ 2        │
│ I.Tests.WitnessPositive                      │ 2        │
│ I.WeakContinuationW1                         │ 2        │
│ I.WitnessPositive                            │ 2        │
│ P                                            │ 9        │
│ P.Proofs.Assembly.Clean                      │ 4        │
│ P.Proofs.Assembly.ContinuationReplay         │ 2        │
│ P.Proofs.Assembly.ContinuationService        │ 2        │
│ P.Proofs.Assembly.Healing                    │ 1        │
│ P.Proofs.Assembly.Outage                     │ 3        │
│ P.Proofs.Assembly.ResetArrival               │ 1        │
│ P.Proofs.Assembly.Root                       │ 9        │
│ P.Proofs.Assembly.WeakContinuation           │ 2        │
│ P.Proofs.Assembly.WeakContinuationGrowth     │ 4        │
│ P.Proofs.Assembly.WeakContinuationGrowthSeed │ 2        │
│ P.Tests.Axioms                               │ 9        │
│ P.Tests.FGCompose                            │ 9        │
│ P.Tests.HealingAttempt                       │ 1        │
│ P.Tests.HealingHTime                         │ 1        │
│ P.Tests.HealingReset                         │ 1        │
│ P.Tests.LiveDC                               │ 9        │
│ P.Tests.NonVacuity.Adversarial               │ 9        │
│ P.Tests.NonVacuity.FinalityClaims            │ 9        │
│ P.Tests.NonVacuity.HealingClaims             │ 1        │
│ P.Tests.NonVacuity.HealingFirst              │ 1        │
│ P.Tests.NonVacuity.HealingPackages           │ 1        │
│ P.Tests.NonVacuity.HealingReset              │ 1        │
│ P.Tests.NonVacuity.HealingRun                │ 1        │
│ P.Tests.OutageContinuationAxioms             │ 4        │
│ P.Tests.OutageContinuationInhabit            │ 4        │
│ P.Tests.OutageExport                         │ 3        │
│ P.Tests.WeakContinuationGrowthAssemblyAxioms │ 9        │
│ P.Tests.WeakContinuationGrowthAxioms         │ 4        │
│ P.Tests.WeakContinuationInterfaces           │ 2        │
│ P.Tests.WeakContinuationSafety               │ 2        │
│ P.Tests.Zero                                 │ 4        │
└──────────────────────────────────────────────┴──────────┘
```

- `AvailableChainFGSAInhabit`: B21, B22.
  B21 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` (`w1_tickBatch_st`).
  B22 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` (`w1_strongRecovery`).
- `AvailableChainFGSAInhabit.Tests.Axioms`: B21, B22.
  B21 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` (`w1_tickBatch_st`).
  B22 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` (`w1_strongRecovery`).
- `AvailableChainFGSAInhabit.Tests.WeakContinuationW1`: B21, B22.
  B21 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` (`w1_tickBatch_st`).
  B22 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` (`w1_strongRecovery`).
- `AvailableChainFGSAInhabit.Tests.WitnessPositive`: B21, B22.
  B21 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` (`w1_tickBatch_st`).
  B22 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` (`w1_strongRecovery`).
- `AvailableChainFGSAInhabit.WeakContinuationW1`: B21, B22.
  B21 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` (`w1_tickBatch_st`).
  B22 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` (`w1_strongRecovery`).
- `AvailableChainFGSAInhabit.WitnessPositive`: B21, B22.
  B21 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:307` (`w1_tickBatch_st`).
  B22 P-As: `AvailableChainFGSAInhabit/WeakContinuationW1.lean:1882` (`w1_strongRecovery`).
- `AvailableChainFGSAProofs`: B02, B03, B04, B09, B12, B13, B14, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Clean`: B02, B04, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Proofs.Assembly.ContinuationReplay`: B13, B14.
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.ContinuationService`: B13, B14.
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Healing`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Outage`: B02, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Root`: B02, B03, B04, B09, B12, B13, B14, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation`: B09, B12.
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth`: B09, B12, B13, B14.
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed`: B13, B14.
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.Axioms`: B02, B03, B04, B09, B12, B13, B14, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.FGCompose`: B02, B03, B04, B09, B12, B13, B14, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.HealingAttempt`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.HealingHTime`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.HealingReset`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.LiveDC`: B02, B03, B04, B09, B12, B13, B14, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.Adversarial`: B02, B03, B04, B09, B12, B13, B14, B19,
B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.FinalityClaims`: B02, B03, B04, B09, B12, B13, B14,
B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingClaims`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingFirst`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingPackages`: B16.
  B16 P-As: `AvailableChainFGSAProofs/Tests/NonVacuity/HealingPackages.lean:450` (`step_constant`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingReset`: B17.
  B17 P-As: `AvailableChainFGSAProofs/Tests/NonVacuity/HealingReset.lean:199` (`step_constant`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingRun`: B03.
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.OutageContinuationAxioms`: B02, B04, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.OutageContinuationInhabit`: B02, B04, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.OutageExport`: B02, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms`: B02, B03, B04, B09, B12,
B13, B14, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B03 P-H1: `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAxioms`: B09, B12, B13, B14.
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:254`
  (`wcg_retrospective`).
  B14 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationInterfaces`: B09, B12.
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationSafety`: B09, B12.
  B09 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:56`
  (`wc_headRead_stamped`).
  B12 P-WC: `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
- `AvailableChainFGSAProofs.Tests.Zero`: B02, B04, B19, B20.
  B02 P-Cl2: `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107` (`cleanSafetyAt_of_trunc`).
  B04 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B19 P-Ar: `AvailableChainFGSAProofs/Proofs/Outage/ArmingScores.lean:40`
  (`inclusion_proposer_prior_of_F_prefix_on`).
  B20 P-Ou: `AvailableChainFGSAProofs/Proofs/Outage/Induction.lean:44` (`outage_arming_sources`).

## Direct assembly ports after the import closures

Assembly/Outage's ExactProposal and inclusion wrappers still need P-Ou's OU-INPUTS
and OU-SCOPES producers. No universal receiver service is passed in this round.
The later-reader gate and public monotonicity projections are now concrete P-As bodies.
The legacy OutageCut/Induction body must consume the scoped P-Ar r5 history.
The full fast/slow history construction remains a family integration obligation.

Assembly/Clean and Tests/Zero remain blocked by B02 and the continuation import closure.
OutageContinuationAxioms and OutageContinuationInhabit remain blocked by B04/B20.
The latter fixture still needs its awake-only schedule, real wake restarts and current
receipt scope after those imports build. No invalid sleep record is assumed to close it.
Shared/Claims already has the current sleep sets, confirmed readers and recoveryStart types;
it builds on this base. No remaining request is assigned to its old lines 30/39.

Bare P23, full Root/FGSAClaims acceptance, G-S2 and final regeneration remain OPEN.
initialAt and its live consumers remain; this round does not claim their cleanup.

WCSEED remains a P-As caller port to the proved StepFacts finite-facts producer.
FAST remains the exact P-Fd current-epoch companion request used by that caller and
ContinuationService. WCIND, WCEMPTY, WCREADS and WCGATES retain their current exact
types in the blocker register. The old Dynamics:337 finite-facts proof request is dropped.

The count column covers current failed imports. ZERO-BASE and OU-FIXTURE record
additional P-As fixture ports hidden by those imports, with exact current types.
They remain local work; no family proof or public premise is added for them.
