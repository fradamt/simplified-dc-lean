module
public import AvailableChainFGSA.Proofs.WindowCertificates
public import AvailableChainKitFG.SelectionCore

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem fold_keys (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W.map (fun e => (e.j, e.X)) =
      w.W.map (fun e => (e.j, e.X)) ∧
    projectFinality (rs.foldl process_row w) = projectFinality w := by
  have h := window_fold_fields rs w
  constructor
  · rw [h.1, List.map_map]
    apply List.map_congr_left
    intro e _
    exact Prod.ext (window_fold_entry rs e).1 (window_fold_entry rs e).2.1
  · simp only [projectFinality_def, h.2.2.2.2.2.1, h.2.2.2.2.2.2]

private theorem folded_keys (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    (certificateFolded p K B).W.map (fun e => (e.j, e.X)) =
      (derive p K B.parent).W.map (fun e => (e.j, e.X)) ∧
    projectFinality (certificateFolded p K B) = certificateFinality p K B.parent :=
  fold_keys B.rows { derive p K B.parent with s := B.slot }

private theorem before_ordered (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) :
    ((certificateSelection p K).before B).Pairwise
      (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X) := by
  have ho : ((derive p K B.parent).W.map (fun e => (e.j, e.X))).Pairwise
      (fun e d => e.1 < d.1 ∧ FGBlock.Preceq e.2 d.2) := by
    simpa only [List.pairwise_map] using window_ordered p K hK B.parent
  rw [← (folded_keys p K B).1] at ho
  simpa only [List.pairwise_map, certificateSelection_def, projectCertEntry_def] using ho

private theorem before_bounds (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : FGCertEntry (Fin p.n))
    (he : e ∈ (certificateSelection p K).before B) :
    (certificateFinality p K B.parent).h_F < e.j ∧
    e.j ≤ (certificateHeight p K B.parent).h_j ∧
    FGBlock.Preceq (certificateFinality p K B.parent).F e.X ∧
    FGBlock.Preceq e.X (certificateHeight p K B.parent).J := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have hk : (d.j, d.X) ∈ (certificateFolded p K B).W.map (fun e => (e.j, e.X)) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [(folded_keys p K B).1] at hk
  obtain ⟨c, hc, heq⟩ := List.mem_map.mp hk
  have hj := congrArg Prod.fst heq
  have hX := congrArg Prod.snd heq
  dsimp only at hj hX
  simpa only [projectCertEntry_def, certificateFinality_def, projectFinality_def,
    certificateHeight_def, projectHeight_def, ← hj, ← hX] using
    window_bounds p K hK B.parent c hc

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem events_finality (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (w : State V) :
    projectFinality (process_height_events E cfg K w) =
      projectFinality (finalizeWindow E w) := by
  rw [process_height_events_def]
  dsimp only
  split_ifs <;> rfl

private theorem finality_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    certificateFinality p K B = projectFinality (finalizeWindow p.E (certificateFolded p K B)) := by
  cases B with
  | genesis => rfl
  | node P s r_s x rs => exact events_finality p.E p.cfg K _

/-- [spec 1222–1227] The window supplies the core selection laws; KitFG derives coverage. -/
theorem windowSelectionLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGSelectionLaws p.E (certificateHeight p K) (certificateFinality p K)
      (certificateSelection p K) := by
  apply FGSelectionLaws.of_core
  · exact ⟨rfl, rfl, rfl⟩
  · exact before_ordered p K hK
  · exact before_bounds p K hK
  · intro B e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact window_prefinal_entry_origin p K hK B d hd
  · intro B
    change (greatestReady p.E (certificateFolded p K B)).map projectCertEntry = none ↔ _
    rw [Option.map_eq_none_iff]
    constructor
    · intro hn e he hq
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      have hb := (before_bounds p K hK B _ (List.mem_map.mpr ⟨d, hd, rfl⟩)).1
      have hf : (certificateFolded p K B).h_F < d.j := by
        simpa only [← (folded_keys p K B).2, projectFinality_def, projectCertEntry_def] using hb
      obtain ⟨c, hc, _⟩ := (window_greatest_spec p.E _).2 d hd hf hq
      rw [hn] at hc
      cases hc
    · intro hn
      cases hc : greatestReady p.E (certificateFolded p K B) with
      | none => rfl
      | some e =>
          have he := (window_greatest_spec p.E _).1 e hc
          exact (hn _ (List.mem_map.mpr ⟨e, he.1, rfl⟩) he.2.2).elim
  · intro B e he
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp he
    have hs := window_greatest_spec p.E (certificateFolded p K B)
    have hm := hs.1 c hc
    refine ⟨List.mem_map.mpr ⟨c, hm.1, rfl⟩, hm.2.2, ?_⟩
    intro d hd hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    have hb := (before_bounds p K hK B _ (List.mem_map.mpr ⟨a, ha, rfl⟩)).1
    have hf : (certificateFolded p K B).h_F < a.j := by
      simpa only [← (folded_keys p K B).2, projectFinality_def, projectCertEntry_def] using hb
    obtain ⟨b, hb, hle⟩ := hs.2 a ha hf hq
    have heq : b = c := Option.some.inj (hb.symm.trans hc)
    exact heq ▸ hle
  · intro B _
    rw [finality_eq, finalizeWindow_def, certificateSelection_def]
    dsimp only
    cases greatestReady p.E (certificateFolded p K B) with
    | none => exact (folded_keys p K B).2
    | some e => rfl
  · intro B
    rw [finality_eq]
    change (finalizeWindow p.E (certificateFolded p K B)).W.map projectCertEntry = _
    rw [finalizeWindow_def]
    cases greatestReady p.E (certificateFolded p K B) <;>
      simp only [projectFinality_def, certificateSelection_def, List.filter_map] <;> rfl

/-- [design §5] Height and finality bounds complete the generic certificate constructor. -/
theorem windowCertificateLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGCertificateLaws p.E (certificateHeight p K) (certificateFinality p K) := by
  apply FGCertificateLaws.of_selection p.E _ _ _ (windowSelectionLaws p K hK)
  · exact windowHeightLaws p K hK
  · rfl
  · intro B hz
    have hbridge := windowHeightBridge p K hK B
    dsimp only at hbridge
    have hz' : (SimplexFG.derive p.E p.cfg B).h_j = 0 := by
      change (projectHeight (derive p K B)).h_j = 0 at hz
      rw [hbridge] at hz
      exact hz
    change (projectHeight (derive p K B)).J = .genesis
    rw [hbridge]
    exact justified_zero_is_genesis p.E p.cfg B hz'
  · exact window_F_preceq_J p K hK
  · exact window_hF_le_hj p K hK

/-- [design §5] Assemble the certificate and selection laws. -/
theorem windowChainCertificate (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGChainCertificate p.E (certificateHeight p K) (certificateFinality p K)
      (certificateSelection p K) :=
  ⟨windowCertificateLaws p K hK, windowSelectionLaws p K hK⟩

end AvailableChain.FGSA.Window
end
