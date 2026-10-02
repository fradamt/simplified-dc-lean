module
public import AvailableChainFGSA.Proofs.WindowLiveness

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

/-- Latest justification height keeps its value or increases at a target crossing. -/
theorem window_hj_mono (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) :
    (derive p K A).h_j ≤ (derive p K B).h_j := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact Nat.le_refl _
  | node P s x rs ih =>
      by_cases hA : A = .node P s x rs
      · subst A
        exact Nat.le_refl _
      · apply (ih (preceq_parent_of_preceq_node hAB hA)).trans
        rcases window_latest_pair_kept p K P s x rs with h | h
        · exact h.1.ge
        · rw [h.1]
          exact Nat.le_of_lt ((windowHeightLaws p K hK).justified_below_height P)

private theorem retentionHeight_count (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (y : Nat) (S : Finset Nat)
    (cover : ∀ d ∈ (derive p K B).W, y < d.j → d.j ∈ S) :
    ((derive p K B).W.filter (fun d => decide (y < d.j))).length ≤ S.card := by
  let xs := (derive p K B).W.filter (fun d => decide (y < d.j))
  have ord : (xs.map Entry.j).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact ((window_ordered p K hK B).filter _).imp (fun h => h.1)
  have sub : (xs.map Entry.j).toFinset ⊆ S := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    obtain ⟨hd, hy⟩ := List.mem_filter.mp hd
    exact cover d hd (of_decide_eq_true hy)
  have count := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup ord.nodup, List.length_map] at count
  exact count

/-- [plan item 12] Finality below the key and a latest height below y + K
keep the key and all its bits. The step bounds follow by monotonicity. -/
theorem window_retained_of_scalar (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (above : (derive p K P).h_F < e.j)
    (near : (derive p K P).h_j < e.j + K) :
    ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have small : (derive p K P).h_j - e.j < K :=
    Nat.sub_lt_left_of_lt_add
      (((window_bounds p K hK A e he).2.1).trans (window_hj_mono p K hK A P hAP)) near
  apply window_retained_along p K hK A P hAP e he
  intro R s x rs _ hBP
  refine ⟨(window_hF_mono p K hK _ _ hBP).trans_lt above, ?_⟩
  have bound := retentionHeight_count p K hK (.node R s x rs) e.j
    (Finset.Ioc e.j (derive p K P).h_j) (fun d hd hy =>
      Finset.mem_Ioc.mpr ⟨hy, ((window_bounds p K hK _ d hd).2.1).trans
        (window_hj_mono p K hK _ _ hBP)⟩)
  rw [Nat.card_Ioc] at bound
  exact bound.trans_lt small

/-- [plan item 12] A finite set covers all births with certificate height
above the protected key up to P. Fewer than K such births prevents eviction.
The set may overestimate the births; no gap in certificate heights is required. -/
theorem window_retained_of_few_births (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (above : (derive p K P).h_F < e.j)
    (births : Finset (FGBlock (Fin p.n))) (few : births.card < K)
    (cover : ∀ C j X, FGBlock.Preceq C P → e.j < j →
      JustificationBirth p.E (certificateHeight p K) C j X → C ∈ births) :
    ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  apply window_retained_along p K hK A P hAP e he
  intro R s x rs _ hBP
  refine ⟨(window_hF_mono p K hK _ _ hBP).trans_lt above, ?_⟩
  apply lt_of_le_of_lt (retentionHeight_count p K hK (.node R s x rs) e.j
    (births.image (fun C => (derive p K C).h_j)) ?_)
    ((Finset.card_image_le).trans_lt few)
  intro d hd hy
  obtain ⟨C, hC, hb, _⟩ := window_entry_origin p K hK _ d hd
  exact Finset.mem_image.mpr ⟨C, cover C d.j d.X (preceq_trans hC hBP) hy hb,
    hb.2.2.2.1⟩

/-- [bp 22:1265–1272] A latest retained height survives at most one later
birth while finality stays below it. This is a fold fact with explicit bounds. -/
theorem window_retained_fresh_one_newer (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A P : FGBlock (Fin p.n)) (hAP : FGBlock.Preceq A P)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (latest : e.j = (derive p K A).h_j)
    (above : (derive p K P).h_F < e.j)
    (births : Finset (FGBlock (Fin p.n))) (one : births.card ≤ 1)
    (cover : ∀ C j X, StrictPrefix A C → FGBlock.Preceq C P →
      JustificationBirth p.E (certificateHeight p K) C j X → C ∈ births) :
    ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  apply window_retained_of_few_births p K hK A P hAP e he above births (by omega)
  intro C j X hCP hj hb
  have hAC : StrictPrefix A C := by
    have hcj : (derive p K C).h_j = j := hb.2.2.2.1
    rcases preceq_total_of_common hAP hCP with h | h
    · refine ⟨h, ?_⟩
      intro eq
      rw [latest, eq, hcj] at hj
      exact (Nat.lt_irrefl j) hj
    · have hm := window_hj_mono p K hK C A h
      rw [hcj, ← latest] at hm
      exact (Nat.not_lt_of_ge hm hj).elim
  exact cover C j X hAC hCP hb

end AvailableChain.FGSA.Window
end
