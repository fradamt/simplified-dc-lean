module
public import AvailableChainKitFG.StoreSafetySimplex

public section

namespace AvailableChain.KitFG.Tests.StoreSafety

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- The concrete store supplies the shared structural invariant at initialization.
theorem store_safety_initial_test (E : Electorate V) (cfg : FGConfig) :
    FGStoreInvariant (simplexHeightView E cfg) (simplexFinalityView E cfg) Store.init :=
  (simplexStoreSafety E cfg).invariant Store.init (storeInv_init E cfg)

-- The store adapter keeps tree inclusion and accepted ancestry through a step.
theorem store_safety_step_test (E : Electorate V) (cfg : FGConfig)
    (st : Store V) (B : FGBlock V) (hi : StoreInv E cfg st) :
    StoreInv E cfg (on_block E cfg st B) ∧
      st.TF ⊆ (on_block E cfg st B).TF ∧ FGBlock.Preceq st.F (on_block E cfg st B).F :=
  ⟨(simplexStoreSafety E cfg).step_good st B hi,
    (simplexStoreSafety E cfg).tree_mono st B hi,
    (simplexStoreSafety E cfg).accepted_F_mono st B hi⟩

private def ssFinalGenesis : FGBlock (Fin 4) :=
  .node B1 2 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

-- Certificate height 1 remains 1. Only the accepted genesis threshold is zero.
private theorem store_accepted_genesis_threshold_test :
    (simplexFinalityView E4 cfg1 ssFinalGenesis).h_F = 1 ∧
      acceptedThreshold (simplexFinalityView E4 cfg1 ssFinalGenesis).F
        (simplexFinalityView E4 cfg1 ssFinalGenesis).h_F = 0 ∧
      ¬ (simplexFinalityView E4 cfg1 ssFinalGenesis).h_F <
        (simplexHeightView E4 cfg1 .genesis).h := by decide

-- The accepted wrapper applies when the historical strict-height test fails.
private theorem store_accepted_genesis_lock_test :
    FGBlock.Preceq (simplexFinalityView E4 cfg1 ssFinalGenesis).F .genesis := by
  apply accepted_lock_of_fault_bound E4 _ _ (simplexCertificateLaws E4 cfg1)
    ssFinalGenesis _ .genesis ∅ rfl (by decide) (by decide)
  intro a ha b hb _
  exact (Finset.notMem_empty b hb).elim

-- Away from genesis, the accepted wrapper keeps the carrier's scalar threshold.
example (F : FGBlock V) (j : Height) (hF : F ≠ .genesis) :
    acceptedThreshold F j = j := by
  rw [acceptedThreshold_def, ite_eq_right hF]

#print axioms store_safety_initial_test
#print axioms store_safety_step_test
#print axioms store_accepted_genesis_threshold_test
#print axioms store_accepted_genesis_lock_test
#print axioms no_slashableWeight_of_fault_bound
#print axioms finalized_preceq_of_no_evidence
#print axioms finalized_preceq_of_fault_bound
#print axioms finalized_compatible_of_fault_bound
#print axioms viewLock_of_certificate
#print axioms viewLock_of_fault_certificate
#print axioms accepted_lock_of_no_evidence
#print axioms accepted_lock_of_fault_bound
#print axioms FGStoreSafety.of_certificate
#print axioms FGStoreSafety.accepted_lock_no_evidence
#print axioms FGStoreSafety.accepted_lock_fault
#print axioms simplexStoreInvariant
#print axioms simplexStoreSafety

end AvailableChain.KitFG.Tests.StoreSafety
end
