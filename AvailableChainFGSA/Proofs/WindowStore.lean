module
public import AvailableChainFGSA.Model.WindowStore
public import AvailableChainFGSA.Proofs.WindowInvariant
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive acceptViable update_finality on_block
open AvailableChain.KitFG

/-- The structural store invariant over the window height and finality views. -/
structure WindowStoreInv (p : Params) (K : Nat) (st : SimplexFG.Store (Fin p.n)) : Prop where
  closed : ∀ B ∈ st.TF, B.parent ∈ st.TF
  gen : FGBlock.genesis ∈ st.TF
  Fmem : st.F ∈ st.TF
  hmax : st.h_max = st.TF.sup (fun B => (projectHeight (derive p K B)).h) ⊔ 1
  pair : (∃ C ∈ st.TF, FGBlock.Preceq st.F (projectHeight (derive p K C)).J ∧
      st.h_j = (projectHeight (derive p K C)).h_j ∧
      st.J = (projectHeight (derive p K C)).J) ∧
    (∀ B ∈ st.TF, FGBlock.Preceq st.F (projectHeight (derive p K B)).J →
      lexKey ((projectHeight (derive p K B)).h_j, (projectHeight (derive p K B)).J) ≤
        lexKey (st.h_j, st.J))
  FJ : FGBlock.Preceq st.F st.J
  Fcar : ∃ D ∈ st.TF, (derive p K D).F = st.F

variable (p : Params) (K : Nat)

private theorem window_height_eq (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (derive p K B).h = (SimplexFG.derive p.E p.cfg B).h :=
  congrArg FGHeight.h (windowHeightBridge p K hK B)

private theorem window_J_eq (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (derive p K B).J = (SimplexFG.derive p.E p.cfg B).J :=
  congrArg FGHeight.J (windowHeightBridge p K hK B)

private theorem window_hj_eq (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (derive p K B).h_j = (SimplexFG.derive p.E p.cfg B).h_j :=
  congrArg FGHeight.h_j (windowHeightBridge p K hK B)

/-- The acceptance filter agrees because it reads only height. -/
theorem acceptViable_eq (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n)) :
    acceptViable p K st = SimplexFG.acceptViable p.E p.cfg st := by
  simp only [acceptViable_def, SimplexFG.acceptViable, window_height_eq p K hK, ← hOf_eq]

private theorem window_update_finality_TF
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).TF = st.TF := by
  rw [update_finality_def]
  dsimp only
  split_ifs <;> rfl

private theorem window_update_finality_h_max
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).h_max = max st.h_max ((derive p K B).h) := by
  rw [update_finality_def]
  dsimp only
  split_ifs <;> rfl

private theorem window_update_finality_pair
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    ((update_finality p K st B).h_j, (update_finality p K st B).J) =
      if FGBlock.Preceq st.F (derive p K B).J ∧
          lexKey (st.h_j, st.J) < lexKey ((derive p K B).h_j, (derive p K B).J)
        then ((derive p K B).h_j, (derive p K B).J) else (st.h_j, st.J) := by
  rw [update_finality_def]
  dsimp only
  by_cases hc : FGBlock.Preceq st.F (derive p K B).J ∧
      lexKey (st.h_j, st.J) < lexKey ((derive p K B).h_j, (derive p K B).J)
  · have hb : (FGBlock.preceq st.F (derive p K B).J && decide (lexKey (st.h_j, st.J) <
        lexKey ((derive p K B).h_j, (derive p K B).J))) = true := by
      simpa [FGBlock.Preceq] using hc
    rw [ite_eq_left hc, ite_eq_left hb]
    split_ifs <;> rfl
  · have hb : ¬ (FGBlock.preceq st.F (derive p K B).J && decide (lexKey (st.h_j, st.J) <
        lexKey ((derive p K B).h_j, (derive p K B).J))) = true := by
      simpa [FGBlock.Preceq] using hc
    rw [ite_eq_right hc, ite_eq_right hb]
    split_ifs <;> rfl

private theorem window_update_finality_F_cases
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).F = st.F ∨
      (FGBlock.Preceq st.F (derive p K B).F ∧ (derive p K B).F ∈ st.TF ∧
        FGBlock.Preceq (derive p K B).F (update_finality p K st B).J ∧
        (update_finality p K st B).F = (derive p K B).F) := by
  rw [update_finality_def]
  dsimp only
  split_ifs with h1 h2 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hF, -⟩, hJ⟩, hV⟩ := h2
    exact Or.inr ⟨hF, (Finset.mem_filter.1 hV).1, hJ, rfl⟩
  · exact Or.inl rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hF, -⟩, hJ⟩, hV⟩ := h2
    exact Or.inr ⟨hF, (Finset.mem_filter.1 hV).1, hJ, rfl⟩
  · exact Or.inl rfl

private theorem window_update_finality_F_mono
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    FGBlock.Preceq st.F (update_finality p K st B).F := by
  rcases window_update_finality_F_cases p K st B with h | ⟨hF, -, -, h⟩
  · rw [h]
    exact preceq_refl _
  · rw [h]
    exact hF

/-- One update from the same input has the same maximum height. -/
theorem update_finality_h_max_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).h_max = (SimplexFG.update_finality p.E p.cfg st B).h_max := by
  rw [window_update_finality_h_max, KitFG.update_finality_h_max, window_height_eq p K hK, hOf]

private theorem window_update_pair_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    ((update_finality p K st B).h_j, (update_finality p K st B).J) =
      ((SimplexFG.update_finality p.E p.cfg st B).h_j,
        (SimplexFG.update_finality p.E p.cfg st B).J) := by
  rw [window_update_finality_pair, KitFG.update_finality_pair, window_J_eq p K hK,
    window_hj_eq p K hK]

/-- One update from the same input has the same selected justification. -/
theorem update_finality_J_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).J = (SimplexFG.update_finality p.E p.cfg st B).J :=
  congrArg Prod.snd (window_update_pair_eq p K hK st B)

/-- One update from the same input has the same justification height. -/
theorem update_finality_h_j_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (update_finality p K st B).h_j = (SimplexFG.update_finality p.E p.cfg st B).h_j :=
  congrArg Prod.fst (window_update_pair_eq p K hK st B)

/-- The refusal tests and tree insertion agree for one step. -/
theorem on_block_TF_eq
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    (on_block p K st B).TF = (SimplexFG.on_block p.E p.cfg st B).TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [on_block_def, ite_eq_left hc, KitFG.on_block_of_refused p.E p.cfg st B hc]
  · rw [on_block_def, ite_eq_right hc, KitFG.on_block_of_accepted p.E p.cfg st B hc,
      window_update_finality_TF, KitFG.update_finality_TF]

private theorem window_pair_iff (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n))
    (hne : ∃ C ∈ st.TF, FGBlock.Preceq st.F (SimplexFG.derive p.E p.cfg C).J) :
    ((∃ C ∈ st.TF, FGBlock.Preceq st.F (projectHeight (derive p K C)).J ∧
      st.h_j = (projectHeight (derive p K C)).h_j ∧
      st.J = (projectHeight (derive p K C)).J) ∧
    (∀ B ∈ st.TF, FGBlock.Preceq st.F (projectHeight (derive p K B)).J →
      lexKey ((projectHeight (derive p K B)).h_j, (projectHeight (derive p K B)).J) ≤
        lexKey (st.h_j, st.J))) ↔ (st.h_j, st.J) = lexMax p.E p.cfg st.F st.TF := by
  simp only [projectHeight_def, window_J_eq p K hK, window_hj_eq p K hK]
  constructor
  · rintro ⟨⟨C, hC, hFC, hh, hJ⟩, hm⟩
    rw [lexMax_eq_of_greatest p.E p.cfg st.F st.TF (viewRootInj_all _) C hC hFC]
    · exact Prod.ext hh hJ
    · simpa only [← hh, ← hJ] using hm
  · intro hp
    obtain ⟨C, hC, hFC, heq, hm⟩ := lexMax_spec p.E p.cfg st.F st.TF (viewRootInj_all _) hne
    have hpair := hp.trans heq
    exact ⟨⟨C, hC, hFC, (Prod.mk.inj hpair).1, (Prod.mk.inj hpair).2⟩,
      fun B hB hFB => hpair ▸ hm B hB hFB⟩

/-- Genesis satisfies every window store field. -/
theorem windowStoreInv_init : WindowStoreInv p K SimplexFG.Store.init := by
  refine ⟨?_, Finset.mem_singleton_self _, Finset.mem_singleton_self _, ?_, ?_,
    preceq_refl _, .genesis, Finset.mem_singleton_self _, rfl⟩
  · intro B hB
    simp only [SimplexFG.Store.init, Finset.mem_singleton] at hB ⊢
    rw [hB]
    rfl
  · change 1 = ({FGBlock.genesis} : Finset (FGBlock (Fin p.n))).sup
      (fun B => (projectHeight (derive p K B)).h) ⊔ 1
    rw [Finset.sup_singleton]
    rfl
  · constructor
    · exact ⟨.genesis, Finset.mem_singleton_self _, preceq_refl _, rfl, rfl⟩
    · intro B hB _
      have hb : B = .genesis := Finset.mem_singleton.mp hB
      subst B
      exact le_refl _

/-- Insertion and the three cache steps preserve the structural invariant. -/
theorem windowStoreInv_accept (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (h : WindowStoreInv p K st) (hpar : B.parent ∈ st.TF) :
    WindowStoreInv p K (update_finality p K { st with TF := insert B st.TF } B) := by
  have hTF := window_update_finality_TF p K { st with TF := insert B st.TF } B
  have hsub : st.TF ⊆ insert B st.TF := Finset.subset_insert B st.TF
  obtain ⟨D, hD, hDF⟩ := h.Fcar
  have hne : ∃ C ∈ st.TF, FGBlock.Preceq st.F (SimplexFG.derive p.E p.cfg C).J := by
    refine ⟨D, hD, ?_⟩
    rw [← window_J_eq p K hK, ← hDF]
    exact window_F_preceq_J p K hK D
  have hp := (window_pair_iff p K hK st hne).mp h.pair
  have hpairJ : ((update_finality p K { st with TF := insert B st.TF } B).h_j,
      (update_finality p K { st with TF := insert B st.TF } B).J) =
      lexMax p.E p.cfg st.F (insert B st.TF) := by
    rw [window_update_pair_eq p K hK, KitFG.update_finality_pair,
      lexMax_insert p.E p.cfg st.F st.TF B (viewRootInj_all _) hne, ← hp]
  have hFJ : FGBlock.Preceq st.F
      (update_finality p K { st with TF := insert B st.TF } B).J := by
    have hj := window_update_finality_pair p K { st with TF := insert B st.TF } B
    dsimp only at hj
    split_ifs at hj with hc
    · rw [(Prod.mk.inj hj).2]
      exact hc.1
    · rw [(Prod.mk.inj hj).2]
      exact h.FJ
  have hne' : ∃ C ∈ insert B st.TF,
      FGBlock.Preceq st.F (SimplexFG.derive p.E p.cfg C).J :=
    hne.imp (fun _ hc => ⟨hsub hc.1, hc.2⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTF]
    intro C hC
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact hsub hpar
    · exact hsub (h.closed C hC)
  · rw [hTF]
    exact hsub h.gen
  · rw [hTF]
    rcases window_update_finality_F_cases p K { st with TF := insert B st.TF } B with
      hF | ⟨_, hmem, _, hF⟩
    · rw [hF]
      exact hsub h.Fmem
    · rw [hF]
      exact hmem
  · have hm : st.h_max = frontier p.E p.cfg st.TF := by
      simpa only [projectHeight_def, window_height_eq p K hK, SimplexFG.frontier, ← hOf_eq]
        using h.hmax
    simpa only [hTF, projectHeight_def, window_height_eq p K hK, SimplexFG.frontier, ← hOf_eq] using
      (show (update_finality p K { st with TF := insert B st.TF } B).h_max =
        frontier p.E p.cfg (insert B st.TF) by
          rw [update_finality_h_max_eq p K hK, KitFG.update_finality_h_max,
            frontier_insert, ← hm])
  · have hnew : ∃ C ∈ (update_finality p K { st with TF := insert B st.TF } B).TF,
        FGBlock.Preceq (update_finality p K { st with TF := insert B st.TF } B).F
          (SimplexFG.derive p.E p.cfg C).J := by
      obtain ⟨C, hC, _, heq, _⟩ := lexMax_spec p.E p.cfg st.F _ (viewRootInj_all _) hne'
      refine ⟨C, hTF ▸ hC, ?_⟩
      have hj := (Prod.mk.inj (hpairJ.trans heq)).2
      rw [← hj]
      rcases window_update_finality_F_cases p K { st with TF := insert B st.TF } B with
        hF | ⟨_, _, hJ, hF⟩
      · rw [hF]
        exact hFJ
      · rw [hF]
        exact hJ
    apply (window_pair_iff p K hK _ hnew).mpr
    rw [hTF]
    rcases window_update_finality_F_cases p K { st with TF := insert B st.TF } B with
      hF | ⟨hadv, _, hJ, hF⟩
    · rw [hF]
      exact hpairJ
    · rw [hF, hpairJ]
      apply (lexMax_of_advance p.E p.cfg st.F _ _ (viewRootInj_all _) hne' hadv ?_).symm
      rw [← hpairJ]
      exact hJ
  · rcases window_update_finality_F_cases p K { st with TF := insert B st.TF } B with
      hF | ⟨_, _, hJ, hF⟩
    · rw [hF]
      exact hFJ
    · rw [hF]
      exact hJ
  · rw [hTF]
    rcases window_update_finality_F_cases p K { st with TF := insert B st.TF } B with
      hF | ⟨_, _, _, hF⟩
    · rw [hF]
      exact ⟨D, hsub hD, hDF⟩
    · rw [hF]
      exact ⟨B, Finset.mem_insert_self B st.TF, rfl⟩

theorem window_on_block_of_refused (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot) :
    on_block p K st B = st := by
  rw [on_block_def]
  rw [ite_eq_left hc]

theorem window_on_block_of_accepted (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (hc : ¬ (B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot)) :
    on_block p K st B = update_finality p K { st with TF := insert B st.TF } B := by
  rw [on_block_def]
  rw [ite_eq_right hc]

theorem window_on_block_F_mono
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    FGBlock.Preceq st.F (on_block p K st B).F := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [window_on_block_of_refused p K st B hc]
    exact preceq_refl _
  · rw [window_on_block_of_accepted p K st B hc]
    exact window_update_finality_F_mono p K { st with TF := insert B st.TF } B

theorem windowStoreInv_on_block (hK : 2 ≤ K)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) (h : WindowStoreInv p K st) :
    WindowStoreInv p K (on_block p K st B) := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [window_on_block_of_refused p K st B hc]
    exact h
  · rw [window_on_block_of_accepted p K st B hc]
    simp only [not_or, not_not, Bool.not_eq_false] at hc
    obtain ⟨-, hpar, -, -⟩ := hc
    exact windowStoreInv_accept p K hK st B h hpar

theorem window_on_block_TF_subset
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    st.TF ⊆ (on_block p K st B).TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [window_on_block_of_refused p K st B hc]
  · rw [window_on_block_of_accepted p K st B hc, window_update_finality_TF]
    exact Finset.subset_insert B st.TF

end AvailableChain.FGSA.Window
end
