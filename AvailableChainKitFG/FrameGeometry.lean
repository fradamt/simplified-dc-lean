module
public import AvailableChainKitFG.FrameBridge
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V]

/-- The filter contains exactly the blocks above both anchors with a height witness. -/
theorem mem_filteredFromView (H : FGHeightView V) (c : Controls V)
    (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFromView H c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ (H W).h := by
  rw [filteredFromView_def]
  simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  simp only [FGBlock.Preceq, and_assoc]

variable [Fintype V] [RowCodec V]

/-- The old filter membership test reads view heights through the bridge. -/
theorem mem_filteredFrom_of_bridge (E : Electorate V) (cfg : FGConfig)
    (H : FGHeightView V) (hb : HeightBridge E cfg H) (c : Controls V)
    (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFrom E cfg c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ (H W).h := by
  rw [filteredFrom_of_bridge E cfg H hb]
  exact mem_filteredFromView H c blocks B

omit [Fintype V] in
/-- The structural pair fields select the same pair as the view selector. -/
private theorem frameGeometry_lexMax_of_inv (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hI : FGStoreInvariant H f st) :
    lexMaxView H st.F st.TF = (st.h_j, st.J) := by
  rw [lexMaxView_def]
  dsimp only
  let candidates := (st.TF.filter (fun W => FGBlock.preceq st.F (H W).J)).image
    (fun W => ((H W).h_j, (H W).J))
  have hmem : ∀ q, q ∈ candidates ↔
      ∃ W ∈ st.TF, FGBlock.Preceq st.F (H W).J ∧ ((H W).h_j, (H W).J) = q := by
    intro q
    simp only [candidates, Finset.mem_image, Finset.mem_filter, FGBlock.Preceq, and_assoc]
  obtain ⟨C, hC, hFC, hj, hJ⟩ := hI.pair.1
  have hp : (st.h_j, st.J) ∈ candidates :=
    (hmem _).2 ⟨C, hC, hFC, by rw [hj, hJ]⟩
  have hsup : candidates.sup lexKey = lexKey (st.h_j, st.J) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      obtain ⟨W, hW, hFW, rfl⟩ := (hmem q).1 hq
      exact hI.pair.2 W hW hFW
    · exact Finset.le_sup hp
  change (pickPair candidates (fun p => decide (lexKey p = candidates.sup lexKey))).getD
    (0, .genesis) = _
  rw [hsup, pickPair_eq_of_unique _ _ _ hp (by simp)]
  · rfl
  · intro q _ hk
    have hk' : (q.1, q.2.root.value) = (st.h_j, st.J.root.value) :=
      toLex.injective (show lexKey q = lexKey (st.h_j, st.J) from of_decide_eq_true hk)
    exact Prod.ext (Prod.mk.inj hk').1
      (FGBlock.root_injective (BlockId.ext (Prod.mk.inj hk').2))

omit [Fintype V] in
/-- The structural invariant makes the store controls equal to the full-tree controls. -/
theorem storeControlsView_eq_fjControlsView_of_inv
    (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hI : FGStoreInvariant H f st) :
    storeControlsView H st = fjControlsView H st.F st.TF := by
  rw [storeControlsView_def, fjControlsView_def, frontierView_def,
    frameGeometry_lexMax_of_inv H f st hI, ← hI.hmax]

omit [Fintype V] in
/-- The store frame on the full tree is the domain of its FJ frame. -/
theorem storeFrameView_full_of_inv (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hI : FGStoreInvariant H f st) :
    storeFrameView H st st.TF = (fjFrameView H st.F st.TF).D := by
  rw [storeFrameView_def, fjFrameView_def,
    storeControlsView_eq_fjControlsView_of_inv H f st hI]

/-- Crossed entries below a block bound the floor of an uncontested frame. -/
theorem storeFrameView_height_of_crossed_prefix_of_inv
    (E : Electorate V) (H : FGHeightView V) (hH : FGHeightLaws E H)
    (f : FGFinalityView V) (st : Store V) (hI : FGStoreInvariant H f st)
    (B : FGBlock V) (hn : (storeControlsView H st).contest = false)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → (H U).h < (H W).h →
      FGBlock.Preceq (H U).T_h B) :
    (storeControlsView H st).lo ≤ (H B).h := by
  have hlo : (storeControlsView H st).lo = st.h_max - 1 := by
    change (if (storeControlsView H st).contest then _ else _) = _
    rw [hn]
    rfl
  rw [hlo]
  by_cases hh : st.h_max ≤ 1
  · exact (Nat.sub_eq_zero_of_le hh) ▸ Nat.zero_le _
  obtain ⟨W, hW, hsup⟩ :=
    Finset.exists_mem_eq_sup st.TF ⟨_, hI.gen⟩ (fun W => (H W).h)
  have hw : (H W).h = st.h_max := by
    have hm := hI.hmax
    rw [hsup] at hm
    simp only [Height] at *
    omega
  obtain ⟨U, hU, hu, _⟩ := hH.height_crossing W (st.h_max - 1)
    (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
  have hm := hH.h_mono (hc W hW U hU (by simp only [Height] at *; omega))
  rw [hH.entry_same_height, hu] at hm
  exact hm

end AvailableChain.KitFG
end
