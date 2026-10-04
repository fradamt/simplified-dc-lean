module
public import AvailableChainFGSA.Proofs.WindowCertificates
public import AvailableChainKitFG.SelectionCore

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- Rows change bits, but preserve the list of keys and the finality pair. -/
private theorem row_keys (w : State V) (a : Row V) :
    (process_row w a).W.map (fun e => (e.j, e.X)) = w.W.map (fun e => (e.j, e.X)) ∧
    projectFinality (process_row w a) = projectFinality w := by
  have hm : (w.W.map (fun e =>
      if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map (fun e => (e.j, e.X)) =
      w.W.map (fun e => (e.j, e.X)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e _
    dsimp only [Function.comp_def]
    split_ifs <;> rfl
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [process_row_def, NamedHeightPair.matchesEntry]
      exact ⟨hm, rfl⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def] <;> split_ifs <;> exact ⟨hm, rfl⟩

private theorem fold_keys (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W.map (fun e => (e.j, e.X)) =
      w.W.map (fun e => (e.j, e.X)) ∧
    projectFinality (rs.foldl process_row w) = projectFinality w := by
  induction rs generalizing w with
  | nil => exact ⟨rfl, rfl⟩
  | cons a rs ih =>
      exact ⟨(ih _).1.trans (row_keys w a).1, (ih _).2.trans (row_keys w a).2⟩

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
/-- The fold selects a ready member and dominates every ready height. -/
private theorem greatest_spec (E : Electorate V) (w : State V) :
    (∀ e, greatestReady E w = some e →
      e ∈ w.W ∧ w.h_F < e.j ∧ E.IsQuorum e.Q) ∧
    (∀ d ∈ w.W, w.h_F < d.j → E.IsQuorum d.Q →
      ∃ e, greatestReady E w = some e ∧ d.j ≤ e.j) := by
  let step := fun (best : Option (Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  have go (xs : List (Entry V)) (best : Option (Entry V)) :
      (∀ e, xs.foldl step best = some e →
        best = some e ∨ (e ∈ xs ∧ w.h_F < e.j ∧ E.IsQuorum e.Q)) ∧
      (∀ d, (best = some d ∨ (d ∈ xs ∧ w.h_F < d.j ∧ E.IsQuorum d.Q)) →
        ∃ e, xs.foldl step best = some e ∧ d.j ≤ e.j) := by
    induction xs generalizing best with
    | nil =>
        simp only [List.foldl_nil, List.not_mem_nil, false_and, or_false]
        exact ⟨fun _ h => h, fun d h => ⟨d, h, le_rfl⟩⟩
    | cons a xs ih =>
        have h := ih (step best a)
        simp only [List.foldl_cons]
        constructor
        · intro e he
          rcases h.1 e he with he | he
          · unfold step at he
            dsimp only [Electorate.IsQuorum] at *
            split_ifs at he with ha <;> cases best <;> simp_all
            all_goals aesop
          · exact Or.inr ⟨List.mem_cons_of_mem _ he.1, he.2⟩
        · intro d hd
          have next : ∃ b, (step best a = some b ∨
              (b ∈ xs ∧ w.h_F < b.j ∧ E.IsQuorum b.Q)) ∧ d.j ≤ b.j := by
            rcases hd with hd | ⟨hd, hf, hq⟩
            · subst best
              by_cases ha : w.h_F < a.j ∧ E.q ≤ E.weightOf a.Q
              · by_cases hj : d.j < a.j
                · exact ⟨a, Or.inl (by simp [step, ha, hj]), Nat.le_of_lt hj⟩
                · exact ⟨d, Or.inl (by simp [step, ha, hj]), le_rfl⟩
              · exact ⟨d, Or.inl (by simp [step, ha]), le_rfl⟩
            · rcases List.mem_cons.mp hd with hd | hd
              · subst d
                have ha : w.h_F < a.j ∧ E.q ≤ E.weightOf a.Q := ⟨hf, hq⟩
                cases best with
                | none => exact ⟨a, Or.inl (by simp [step, ha]), le_rfl⟩
                | some old =>
                    by_cases hj : old.j < a.j
                    · exact ⟨a, Or.inl (by simp [step, ha, hj]), le_rfl⟩
                    · exact ⟨old, Or.inl (by simp [step, ha, hj]), Nat.le_of_not_gt hj⟩
              · exact ⟨d, Or.inr ⟨hd, hf, hq⟩, le_rfl⟩
          obtain ⟨b, hb, hdb⟩ := next
          obtain ⟨e, he, hbe⟩ := h.2 b hb
          exact ⟨e, he, hdb.trans hbe⟩
  have heq : greatestReady E w = w.W.foldl step none := by
    rw [greatestReady_def]
    congr 1
    funext best e
    dsimp [step]
    split_ifs <;> cases best <;> rfl
  rw [heq]
  have h := go w.W none
  exact ⟨fun e he => (h.1 e he).resolve_left (by simp),
    fun d hd hf hq => h.2 d (Or.inr ⟨hd, hf, hq⟩)⟩

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
      obtain ⟨c, hc, _⟩ := (greatest_spec p.E _).2 d hd hf hq
      rw [hn] at hc
      cases hc
    · intro hn
      cases hc : greatestReady p.E (certificateFolded p K B) with
      | none => rfl
      | some e =>
          have he := (greatest_spec p.E _).1 e hc
          exact (hn _ (List.mem_map.mpr ⟨e, he.1, rfl⟩) he.2.2).elim
  · intro B e he
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp he
    have hs := greatest_spec p.E (certificateFolded p K B)
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
