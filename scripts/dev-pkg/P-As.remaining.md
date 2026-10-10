# P-As round 2 — remaining targets

Full P-As is OPEN. Every remaining target is listed below. P means
AvailableChainFGSAProofs; I means AvailableChainFGSAInhabit. 
The request count refers to the entries below. Each B key gives
file:line, exact current type and owner in [P-As.blocker-types.md](P-As.blocker-types.md).
This is the failed import closure. It does not claim that all code in that module is false.
PORT means a local P-As consumer still needs work; it is not a family proof request.

```text
┌──────────────────────────────────────────────┬──────────┐
│ Remaining target                             │ Requests │
├──────────────────────────────────────────────┼──────────┤
│ I                                            │ 1        │
│ I.Tests.Axioms                               │ 1        │
│ I.Tests.WeakContinuationW1                   │ 1        │
│ I.Tests.WitnessPositive                      │ 1        │
│ I.WeakContinuationW1                         │ 1        │
│ I.WitnessPositive                            │ 1        │
│ P                                            │ 13       │
│ P.Proofs.Assembly.Clean                      │ 3        │
│ P.Proofs.Assembly.ContinuationReplay         │ 2        │
│ P.Proofs.Assembly.ContinuationService        │ 2        │
│ P.Proofs.Assembly.Healing                    │ 1        │
│ P.Proofs.Assembly.Outage                     │ 4        │
│ P.Proofs.Assembly.ResetArrival               │ 1        │
│ P.Proofs.Assembly.Root                       │ 13       │
│ P.Proofs.Assembly.WeakContinuation           │ 5        │
│ P.Proofs.Assembly.WeakContinuationGrowth     │ 7        │
│ P.Proofs.Assembly.WeakContinuationGrowthSeed │ 2        │
│ P.Tests.Axioms                               │ 13       │
│ P.Tests.FGCompose                            │ 13       │
│ P.Tests.HealingAttempt                       │ 1        │
│ P.Tests.HealingHTime                         │ 1        │
│ P.Tests.HealingReset                         │ 1        │
│ P.Tests.LiveDC                               │ 13       │
│ P.Tests.NonVacuity.Adversarial               │ 13       │
│ P.Tests.NonVacuity.FinalityClaims            │ 13       │
│ P.Tests.NonVacuity.HealingClaims             │ 1        │
│ P.Tests.NonVacuity.HealingFirst              │ 1        │
│ P.Tests.NonVacuity.HealingPackages           │ 1        │
│ P.Tests.NonVacuity.HealingReset              │ 1        │
│ P.Tests.NonVacuity.HealingRun                │ 1        │
│ P.Tests.OutageContinuationAxioms             │ 3        │
│ P.Tests.OutageContinuationInhabit            │ 3        │
│ P.Tests.OutageExport                         │ 4        │
│ P.Tests.WeakContinuationGrowthAssemblyAxioms │ 13       │
│ P.Tests.WeakContinuationGrowthAxioms         │ 7        │
│ P.Tests.WeakContinuationGrowthNonVacuity     │ 1        │
│ P.Tests.WeakContinuationInterfaces           │ 5        │
│ P.Tests.WeakContinuationSafety               │ 5        │
│ P.Tests.Zero                                 │ 3        │
└──────────────────────────────────────────────┴──────────┘
```

- `AvailableChainFGSAInhabit`:
  B01 P-As:
  `AvailableChainFGSAInhabit/WeakContinuationW1.lean:91`
  (`w1_known_fold`).
- `AvailableChainFGSAInhabit.Tests.Axioms`:
  B01 P-As:
  `AvailableChainFGSAInhabit/WeakContinuationW1.lean:91`
  (`w1_known_fold`).
- `AvailableChainFGSAInhabit.Tests.WeakContinuationW1`:
  B01 P-As:
  `AvailableChainFGSAInhabit/WeakContinuationW1.lean:91`
  (`w1_known_fold`).
- `AvailableChainFGSAInhabit.Tests.WitnessPositive`:
  B01 P-As:
  `AvailableChainFGSAInhabit/WeakContinuationW1.lean:91`
  (`w1_known_fold`).
- `AvailableChainFGSAInhabit.WeakContinuationW1`:
  B01 P-As:
  `AvailableChainFGSAInhabit/WeakContinuationW1.lean:91`
  (`w1_known_fold`).
- `AvailableChainFGSAInhabit.WitnessPositive`:
  B01 P-As:
  `AvailableChainFGSAInhabit/WeakContinuationW1.lean:91`
  (`w1_known_fold`).
- `AvailableChainFGSAProofs`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Clean`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
- `AvailableChainFGSAProofs.Proofs.Assembly.ContinuationReplay`:
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.ContinuationService`:
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Healing`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Outage`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
- `AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Proofs.Assembly.Root`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation`:
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth`:
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed`:
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.Axioms`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.FGCompose`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.HealingAttempt`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.HealingHTime`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.HealingReset`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.LiveDC`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.Adversarial`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.FinalityClaims`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingClaims`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingFirst`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingPackages`:
  B16 P-As:
  `AvailableChainFGSAProofs/Tests/NonVacuity/HealingPackages.lean:450`
  (`step_constant`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingReset`:
  B17 P-As:
  `AvailableChainFGSAProofs/Tests/NonVacuity/HealingReset.lean:199`
  (`step_constant`).
- `AvailableChainFGSAProofs.Tests.NonVacuity.HealingRun`:
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
- `AvailableChainFGSAProofs.Tests.OutageContinuationAxioms`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
- `AvailableChainFGSAProofs.Tests.OutageContinuationInhabit`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
- `AvailableChainFGSAProofs.Tests.OutageExport`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B03 P-H1:
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226`
  (`healing_support_honest_head`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B05 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142`
  (`inclusion_comparison_lift`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).
  B07 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15`
  (`outage_supplier_history`).
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAxioms`:
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
  B13 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158`
  (`growthStepFacts_step_receiptOrigins`).
  B14 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55`
  (`wcg_empty_outputDomain`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationGrowthNonVacuity`:
  B18 P-As:
  `AvailableChainFGSAProofs/Tests/WeakContinuationGrowthNonVacuity.lean:744`
  (`nvGen_gen_tick_nonproposal_wire`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationInterfaces`:
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
- `AvailableChainFGSAProofs.Tests.WeakContinuationSafety`:
  B08 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17`
  (`wc_finalBelow`).
  B09 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24`
  (`wc_historyMax`).
  B10 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44`
  (`step_receiptOrigins`).
  B11 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17`
  (`wc_reconcileBound`).
  B12 P-WC:
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21`
  (`wc_retrospective`).
- `AvailableChainFGSAProofs.Tests.Zero`:
  B02 P-Cl2:
  `AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107`
  (`cleanSafetyAt_of_trunc`).
  B04 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19`
  (`outageV_source_path`).
  B06 P-Ou:
  `AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114`
  (`outage_gateStep_protection`).


## Current initialAt uses

Keep every helper until the two live consumer modules build.

```text
┌───────────────────────────────────────────────┬─────────────────────────────┐
│ File                                          │ Lines                       │
├───────────────────────────────────────────────┼─────────────────────────────┤
│ FGSA/Model/Store.lean                          │ 56                          │
│ FGSA/Proofs/LeaseOutput.lean                    │ 25–26                       │
│ FGSA/Proofs/Metadata.lean                       │ 279                         │
│ FGSA/Proofs/StoreInv.lean                       │ 185                         │
│ FGSARun/Proofs/AncestorDeadlinesStore.lean      │ 47–49                       │
│ Inhabit/WeakContinuationW1.lean                │ 106–108; 1185–1187          │
│ Proofs/Tests/NonVacuity/Adversarial.lean        │ 1889–1891; 2981–2983        │
└───────────────────────────────────────────────┴─────────────────────────────┘
```

All paths have the AvailableChain prefix. Proofs means AvailableChainFGSAProofs.
The legacy audit rows also stay until their declarations can be removed.
