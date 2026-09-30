module
public import AvailableChainKitFG.Accountable
public import AvailableChainKitFG.CrossingNoFinal
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.CausalCap

/-! Kernel dependency audit for the FG chain lemmas without root premises. -/

#print axioms AvailableChain.KitFG.slashableWeight_or_justified_eq
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_preceq
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_preceq
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_compatible_of_le
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_compatible
#print axioms AvailableChain.KitFG.exists_crossing_quorum_ne_justified
#print axioms AvailableChain.KitFG.e1Weight_of_finalityQC_not_preceq
#print axioms AvailableChain.KitFG.slashableWeight_of_finalized_crossing
#print axioms AvailableChain.KitFG.exists_honest_timeout_of_crossing
#print axioms AvailableChain.KitFG.frame_facts
#print axioms AvailableChain.KitFG.causalCap_row
#print axioms AvailableChain.KitFG.causalCap_justified_row
#print axioms AvailableChain.KitFG.finalityCap_row
#print axioms AvailableChain.KitFG.finalityCap_height_row
#print axioms AvailableChain.KitFG.causalCap
