module
public import AvailableChainFGCompose.Statements.Population.FrontierSearch -- shake: keep (audit)
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchBridges -- shake: keep (audit)

public section

open AvailableChain.FGCompose

#print axioms FrontierLocalServiceFG
#print axioms FrontierLocalServiceFG_def
#print axioms StrongServedFG
#print axioms StrongServedFG_def
#print axioms FrontierHG3ResultFG
#print axioms FrontierHG3ResultFG_def
#print axioms InterruptedRepairStatementFG
#print axioms InterruptedRepairStatementFG_def
#print axioms FrontierTailStatementFG
#print axioms FrontierTailStatementFG_def
#print axioms frontierLocalServiceFG_frozen_iff
#print axioms strongServedFG_frozen_iff
#print axioms frontierHG3ResultFG_frozen_iff
#print axioms interruptedRepairStatementFG_frozen_iff
#print axioms frontierTailStatementFG_frozen_iff

end
