module
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainKitFG.CausalCapCore
public import AvailableChainKitFG.StoreSafetySimplex
public import AvailableChainKitFG.FrameChannels
public import AvailableChainKitFG.CausalCap

public section

namespace AvailableChain.KitFG.Tests.FrameGeometry

open AvailableChain.SimplexFG

-- The generic forms recover the old statements at the SimplexFG views.
variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) :
    storeControls E cfg st = fjControls E cfg st.F st.TF :=
  storeControlsView_eq_fjControlsView_of_inv _ _ st (simplexStoreInvariant E cfg st hi)

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) :
    storeFrame E cfg st st.TF = (fjFrame E cfg st.F st.TF).D := by
  rw [storeFrame_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl),
    fjFrame_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl)]
  exact storeFrameView_full_of_inv _ _ st (simplexStoreInvariant E cfg st hi)

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st)
    (B : FGBlock V) (hn : (storeControls E cfg st).contest = false)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B) :
    (storeControls E cfg st).lo ≤ hOf E cfg B :=
  storeFrameView_height_of_crossed_prefix_of_inv E _ (simplexHeightLaws E cfg) _ st
    (simplexStoreInvariant E cfg st hi) B hn hc

example (E : Electorate V) (cfg : FGConfig) (c : Controls V)
    (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFrom E cfg c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ hOf E cfg W :=
  mem_filteredFrom_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl) c blocks B

example (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V) (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hy : 0 < y) (hF : y ≤ (derive E cfg B).h_F) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      a.finality_pair = some ⟨(derive E cfg B).h_F, (derive E cfg B).F.root⟩ :=
  finalityCap_row_of_certificate E _ _ (simplexCertificateLaws E cfg)
    faulty hcap y B R hrows hy hF

private def frameGeometryStore : Store (Fin 4) := on_block E4 cfg1 Store.init B1

private theorem frameGeometry_store_inv :
    FGStoreInvariant (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1)
      frameGeometryStore :=
  simplexStoreInvariant E4 cfg1 _
    (storeInv_on_block E4 cfg1 _ B1 (storeInv_init E4 cfg1) (fun _ => viewRootInj_all _))

example : storeControlsView (simplexHeightView E4 cfg1) frameGeometryStore =
    fjControlsView (simplexHeightView E4 cfg1) frameGeometryStore.F frameGeometryStore.TF :=
  storeControlsView_eq_fjControlsView_of_inv _ _ _ frameGeometry_store_inv

example : storeFrameView (simplexHeightView E4 cfg1) frameGeometryStore frameGeometryStore.TF =
    (fjFrameView (simplexHeightView E4 cfg1) frameGeometryStore.F frameGeometryStore.TF).D :=
  storeFrameView_full_of_inv _ _ _ frameGeometry_store_inv

example : B1 ∈ filteredFromView (simplexHeightView E4 cfg1)
    (storeControlsView (simplexHeightView E4 cfg1) frameGeometryStore) frameGeometryStore.TF := by
  apply (mem_filteredFromView _ _ _ B1).2
  refine ⟨by decide, by decide, by decide, B1, by decide, preceq_refl B1, by decide⟩

example : (storeControlsView (simplexHeightView E4 cfg1)
    (Store.init : Store (Fin 4))).lo ≤ (simplexHeightView E4 cfg1 .genesis).h := by
  apply storeFrameView_height_of_crossed_prefix_of_inv E4 _ (simplexHeightLaws E4 cfg1)
    _ _ (simplexStoreInvariant E4 cfg1 _ (storeInv_init E4 cfg1)) .genesis (by decide)
  intro W hW U hU hlt
  have hW' : W = .genesis := Finset.mem_singleton.mp hW
  subst W
  have hU' := preceq_genesis.mp hU
  subst U
  exact (Nat.lt_irrefl _ hlt).elim

private def frameGeometryFinalBlock : FGBlock (Fin 4) :=
  .node B1 2 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

example : ∃ a ∈ chainRows frameGeometryFinalBlock,
    a.signer ∉ ({0, 2} : Finset (Fin 4)) ∧ True ∧
      a.finality_pair = some ⟨1, genesisRoot⟩ :=
  finalityCap_row_of_certificate E4 _ _ (simplexCertificateLaws E4 cfg1)
    {0, 2} (by decide) 1 frameGeometryFinalBlock (fun _ => True)
    (fun _ _ _ => True.intro) (by decide) (by decide)

-- The height record does not fix the height of J. No nonempty electorate
-- premise occurs in that record or in the requested frame statements.
private def frameGeometryEmptyElectorate : Electorate (Fin 0) :=
  ⟨fun _ => 1, fun _ => Nat.one_pos⟩

private def frameGeometryBadHeight (B : FGBlock (Fin 0)) : FGHeight (Fin 0) :=
  { simplexHeightView frameGeometryEmptyElectorate cfg1 B with
    J := (simplexHeightView frameGeometryEmptyElectorate cfg1 B).T_h }

private theorem frameGeometry_bad_height_laws :
    FGHeightLaws frameGeometryEmptyElectorate frameGeometryBadHeight := by
  refine { simplexHeightLaws frameGeometryEmptyElectorate cfg1 with
    justified_preceq_entry := fun B => preceq_refl _
    justification_certificate := ?_ }
  intro D _
  refine ⟨∅, ?_, ?_⟩
  · change frameGeometryEmptyElectorate.q ≤ frameGeometryEmptyElectorate.weightOf ∅
    decide
  intro i hi
  exact (Finset.notMem_empty i hi).elim

theorem frameGeometry_missing_J_height :
    ∃ (E : Electorate (Fin 0)) (H : FGHeightView (Fin 0)),
      FGHeightLaws E H ∧ ∃ C, (H C).h_j ≠ 0 ∧ (H (H C).J).h ≠ (H C).h_j := by
  refine ⟨frameGeometryEmptyElectorate, frameGeometryBadHeight,
    frameGeometry_bad_height_laws, .node .genesis 1 0 [], ?_⟩
  decide +kernel

#print axioms mem_filteredFromView
#print axioms mem_filteredFrom_of_bridge
#print axioms storeControlsView_eq_fjControlsView_of_inv
#print axioms storeFrameView_full_of_inv
#print axioms storeFrameView_height_of_crossed_prefix_of_inv
#print axioms finalityCap_row_of_certificate
#print axioms frameGeometry_store_inv
#print axioms frameGeometry_missing_J_height

end AvailableChain.KitFG.Tests.FrameGeometry
end
