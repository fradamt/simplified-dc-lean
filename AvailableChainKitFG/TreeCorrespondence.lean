module
public import AvailableChainKitFG.TreeFrameBridge
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.KitFG
open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
variable {E : Electorate V} (v : FGHeightView V) (hL : FGHeightLaws E v)

include hL in
/-- Repairs `pair_eq_of_lexKey_eq` for a supplied height view and its laws. -/
theorem treePair_eq_of_lexKey_eq {Vw : View V} (hinj : ViewRootInj Vw) {W W' : FGBlock V}
    (hW : W ∈ Vw) (hW' : W' ∈ Vw)
    (hk : lexKey ((v W).h_j, (v W).J) =
      lexKey ((v W').h_j, (v W').J)) :
    ((v W).h_j, (v W).J) =
      ((v W').h_j, (v W').J) := by
  have hk' := toLex.injective hk
  simp only [Prod.mk.injEq] at hk'
  obtain ⟨h1, h2⟩ := hk'
  have hJ : (v W).J = (v W').J :=
    hinj _ _ ⟨W, hW, (preceq_trans (hL.justified_preceq_entry W) (hL.entry_preceq W))⟩
      ⟨W', hW', (preceq_trans (hL.justified_preceq_entry W') (hL.entry_preceq W'))⟩ (BlockId.ext h2)
  rw [h1, hJ]

include hL in
/-- Repairs `lexMax_eq_of_greatest` for a supplied height view and its laws. -/
theorem treeLexMax_eq_of_greatest (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (K : FGBlock V) (hK : K ∈ Vw) (hFK : FGBlock.Preceq F (v K).J)
    (hmax : ∀ W ∈ Vw, FGBlock.Preceq F (v W).J →
      lexKey ((v W).h_j, (v W).J) ≤
        lexKey ((v K).h_j, (v K).J)) :
    lexMaxView v F Vw = ((v K).h_j, (v K).J) := by
  unfold lexMaxView
  dsimp only
  have hmem : ∀ q, q ∈ (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
      (fun W => ((v W).h_j, (v W).J)) ↔
      ∃ W ∈ Vw, FGBlock.Preceq F (v W).J ∧
        ((v W).h_j, (v W).J) = q := by
    intro q
    simp only [Finset.mem_image, Finset.mem_filter, FGBlock.Preceq, and_assoc]
  have hp : ((v K).h_j, (v K).J) ∈
      (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
        (fun W => ((v W).h_j, (v W).J)) :=
    (hmem _).2 ⟨K, hK, hFK, rfl⟩
  have hsup : ((Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
      (fun W => ((v W).h_j, (v W).J))).sup lexKey =
      lexKey ((v K).h_j, (v K).J) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      obtain ⟨W, hW, hFW, rfl⟩ := (hmem q).1 hq
      exact hmax W hW hFW
    · exact Finset.le_sup hp
  rw [hsup, pickPair_eq_of_unique _ _ _ hp (by simp)]
  · rfl
  · intro q hq hk
    obtain ⟨W, hW, -, rfl⟩ := (hmem q).1 hq
    exact treePair_eq_of_lexKey_eq v hL hinj hW hK (by simpa using hk)

include hL in
/-- Repairs `lexMax_spec` for a supplied height view and its laws. -/
theorem treeLexMax_spec (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (hne : ∃ K ∈ Vw, FGBlock.Preceq F (v K).J) :
    ∃ K ∈ Vw, FGBlock.Preceq F (v K).J ∧
      lexMaxView v F Vw = ((v K).h_j, (v K).J) ∧
      ∀ W ∈ Vw, FGBlock.Preceq F (v W).J →
        lexKey ((v W).h_j, (v W).J) ≤
          lexKey ((v K).h_j, (v K).J) := by
  have hS : (Vw.filter (fun W => FGBlock.Preceq F (v W).J)).Nonempty := by
    obtain ⟨K, hK, hFK⟩ := hne
    exact ⟨K, Finset.mem_filter.2 ⟨hK, hFK⟩⟩
  obtain ⟨K, hKS, hKmax⟩ := Finset.exists_max_image _
    (fun W => lexKey ((v W).h_j, (v W).J)) hS
  rw [Finset.mem_filter] at hKS
  have hmax : ∀ W ∈ Vw, FGBlock.Preceq F (v W).J →
      lexKey ((v W).h_j, (v W).J) ≤
        lexKey ((v K).h_j, (v K).J) :=
    fun W hW hFW => hKmax W (Finset.mem_filter.2 ⟨hW, hFW⟩)
  exact ⟨K, hKS.1, hKS.2, treeLexMax_eq_of_greatest v hL F Vw hinj K hKS.1 hKS.2 hmax, hmax⟩

omit [Fintype V] in
/-- Repairs `lexMax_of_none` for a supplied height view and its laws. -/
theorem treeLexMax_of_none (F : FGBlock V) (Vw : View V)
    (hno : ∀ W ∈ Vw, ¬ FGBlock.Preceq F (v W).J) :
    lexMaxView v F Vw = (0, .genesis) := by
  unfold lexMaxView
  dsimp only
  have hempty : (Vw.filter (fun W => FGBlock.preceq F (v W).J)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact hno
  rw [hempty, Finset.image_empty, pickPair_empty]
  rfl

omit [Fintype V] in
/-- Repairs `fjControls_J_preceq_of_rootIsJ`: a top block must also extend F. -/
theorem treeTop_extends_J (F : FGBlock V) (Vw : View V)
    (hr : (treeFjControlsView v F Vw).rootIsJ = true)
    (W : FGBlock V) (hW : W ∈ Vw) (hFW : FGBlock.Preceq F W)
    (hH : (v W).h = (treeFjControlsView v F Vw).H) :
    FGBlock.Preceq (treeFjControlsView v F Vw).J W :=
  treeFjControlsView_J_preceq_of_rootIsJ v F Vw hr W hW hFW hH

end AvailableChain.KitFG
end
