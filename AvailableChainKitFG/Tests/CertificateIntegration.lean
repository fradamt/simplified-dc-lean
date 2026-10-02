module
public import AvailableChainKitFG.SelectionCore
public import AvailableChainKitFG.StoreSafetySimplex

public section

namespace AvailableChain.KitFG.Tests.CertificateIntegration

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- Start with the Simplex fields. The core constructor derives coverage.
private theorem cint_selection (E : Electorate V) (cfg : FGConfig) :
    FGSelectionLaws E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (simplexSelectionView E cfg) :=
  FGSelectionLaws.of_core E _ _ _
    (simplexSelectionLaws E cfg).initial (simplexSelectionLaws E cfg).ordered
    (simplexSelectionLaws E cfg).bounds (simplexSelectionLaws E cfg).entry_origin
    (simplexSelectionLaws E cfg).none_iff (simplexSelectionLaws E cfg).greatest
    (simplexSelectionLaws E cfg).write (simplexSelectionLaws E cfg).prune

-- Use the selection result to build the certificate laws and the full record.
private theorem cint_certificate (E : Electorate V) (cfg : FGConfig) :
    FGChainCertificate E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (simplexSelectionView E cfg) :=
  ⟨FGCertificateLaws.of_selection E _ _ _ (cint_selection E cfg)
    (simplexHeightLaws E cfg) rfl (justified_zero_is_genesis E cfg)
    (derive_F_preceq_J E cfg) (heights_ordered E cfg), cint_selection E cfg⟩

-- The full record supplies the accountable safety endpoint.
theorem certificate_integration_accountable_test (E : Electorate V) (cfg : FGConfig)
    (B₁ B₂ : FGBlock V) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (simplexFinalityView E cfg B₁).F
        (simplexFinalityView E cfg B₂).F = true :=
  slashableWeight_or_finalized_compatible_of_certificate E _ _
    (cint_certificate E cfg).laws B₁ B₂

-- Build store safety from the same certificate and the concrete store suppliers.
private theorem cint_store (E : Electorate V) (cfg : FGConfig) :
    FGStoreSafety E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (id : Store V → Store V)
      (fun _ B => (simplexHeightView E cfg B, simplexFinalityView E cfg B))
      Store.init (on_block E cfg) (StoreInv E cfg) :=
  FGStoreSafety.of_certificate E _ _ (cint_certificate E cfg).laws
    id _ Store.init (on_block E cfg) (StoreInv E cfg)
    (storeInv_init E cfg) (simplexStoreInvariant E cfg)
    (fun st B hi => storeInv_on_block E cfg st B hi (fun _ => viewRootInj_all _))
    (fun st B _ => on_block_TF_subset E cfg st B)
    (fun st B _ => on_block_F_mono E cfg st B) (fun _ _ _ _ => rfl)

-- The accepted lock needs both the strict fault bound and the honest-row premise.
theorem certificate_integration_accepted_lock_test (E : Electorate V) (cfg : FGConfig)
    (st : Store V) (hi : StoreInv E cfg st) (D W : FGBlock V) (faulty : Finset V)
    (hD : D ∈ st.TF) (hF : (simplexFinalityView E cfg D).F = st.F)
    (hh : acceptedThreshold st.F (simplexFinalityView E cfg D).h_F <
      (simplexHeightView E cfg W).h)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hno : NoSlashOutside faulty (chainRows D) (chainRows W)) :
    FGBlock.Preceq st.F W :=
  (cint_store E cfg).accepted_lock_fault E _ _ st hi D W faulty hD hF hh hcap hno

-- The existing three-block chain reaches a non-genesis accepted anchor.
private theorem cint_concrete_fault_lock :
    (simplexFinalityView E4 cfg1 B3).h_F = 2 ∧ stF.F = B1 ∧
      (HasSlashableWeightBetween E4 (chainRows B2) (chainRows B3) ∨
        FGBlock.compatible (simplexFinalityView E4 cfg1 B2).F
          (simplexFinalityView E4 cfg1 B3).F = true) ∧ FGBlock.Preceq stF.F B3 := by
  have hs := cint_store E4 cfg1
  have h1 := hs.step_good Store.init B1 hs.initial_good
  have h2 := hs.step_good (on_block E4 cfg1 Store.init B1) B2 h1
  have hi : StoreInv E4 cfg1 stF := by
    simpa only [stF, List.foldl_cons, List.foldl_nil] using
      hs.step_good (on_block E4 cfg1 (on_block E4 cfg1 Store.init B1) B2) B3 h2
  have hcap : E4.weightOf ({3} : Finset (Fin 4)) + E4.totalWeight < 2 * E4.q := by
    decide
  have hno : NoSlashOutside ({3} : Finset (Fin 4)) (chainRows B3) (chainRows B3) := by
    rw [NoSlashOutside_def]
    decide +kernel
  have hlock := certificate_integration_accepted_lock_test E4 cfg1 stF hi B3 B3 {3}
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hcap hno
  exact ⟨by decide +kernel, by decide +kernel,
    certificate_integration_accountable_test E4 cfg1 B2 B3, hlock⟩

-- A new target row makes the later carrier's row history different.
def cintLockChild : FGBlock (Fin 4) :=
  .node B3 4 0 [rowAt 4 B3.root false 0]

-- D remains B3. W strictly extends D and has an additional row.
private theorem cint_concrete_extended_fault_lock :
    StrictPrefix B3 cintLockChild ∧ chainRows B3 ≠ chainRows cintLockChild ∧
      (simplexHeightView E4 cfg1 cintLockChild).h = 4 ∧
      FGBlock.Preceq stF.F cintLockChild := by
  have hs := cint_store E4 cfg1
  have h1 := hs.step_good Store.init B1 hs.initial_good
  have h2 := hs.step_good (on_block E4 cfg1 Store.init B1) B2 h1
  have hi : StoreInv E4 cfg1 stF := by
    simpa only [stF, List.foldl_cons, List.foldl_nil] using
      hs.step_good (on_block E4 cfg1 (on_block E4 cfg1 Store.init B1) B2) B3 h2
  have hcap : E4.weightOf ({3} : Finset (Fin 4)) + E4.totalWeight < 2 * E4.q := by
    decide
  have hh : acceptedThreshold stF.F (simplexFinalityView E4 cfg1 B3).h_F <
      (simplexHeightView E4 cfg1 cintLockChild).h := by
    decide +kernel
  have hno : NoSlashOutside ({3} : Finset (Fin 4))
      (chainRows B3) (chainRows cintLockChild) := by
    rw [NoSlashOutside_def]
    decide +kernel
  have hlock := certificate_integration_accepted_lock_test E4 cfg1 stF hi B3
    cintLockChild {3} (by decide +kernel) (by decide +kernel) hh hcap hno
  refine ⟨?_, by decide +kernel, by decide +kernel, hlock⟩
  rw [StrictPrefix_def]
  decide +kernel

-- The public rewrite connects the certificate fields to the client adapter.
example (E : Electorate V) (cfg : FGConfig) (Hd : FGBlock V) :
    certificateHeadFields (simplexHeightView E cfg) (simplexFinalityView E cfg) Hd =
      HeadFields.ofBlock E cfg Hd := by
  rw [simplex_certificateHeadFields_eq]

#print axioms cint_selection
#print axioms cint_certificate
#print axioms certificate_integration_accountable_test
#print axioms cint_store
#print axioms certificate_integration_accepted_lock_test
#print axioms cint_concrete_fault_lock
#print axioms cint_concrete_extended_fault_lock
#print axioms simplex_certificateHeadFields_eq

end AvailableChain.KitFG.Tests.CertificateIntegration
end
