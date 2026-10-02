module
public import AvailableChainFGSA.Statements.WindowCertificate
public import AvailableChainFGSA.Proofs.WindowInvariant
public import AvailableChainKitFG.CertificateSimplex

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

/-- Birth uses only the height fields supplied by the landed bridge. -/
theorem justificationBirth_window_iff_simplex (p : Params) (K : Nat) (hK : 2 ≤ K)
    (C : FGBlock (Fin p.n)) (j : Height) (X : FGBlock (Fin p.n)) :
    JustificationBirth p.E (certificateHeight p K) C j X ↔
      JustificationBirth p.E (simplexHeightView p.E p.cfg) C j X := by
  have hv : certificateHeight p K = simplexHeightView p.E p.cfg :=
    funext (windowHeightBridge p K hK)
  rw [hv]

private theorem strict_node (p : Params) {C P : FGBlock (Fin p.n)}
    (s : Slot) (x : Nat) (rs : List (Row (Fin p.n))) (hCP : FGBlock.Preceq C P) :
    StrictPrefix C (.node P s x rs) := by
  refine ⟨preceq_node_of_preceq s x rs hCP, ?_⟩
  intro he
  have hcycle := preceq_antisymm (he ▸ hCP) (preceq_parent_node P s x rs)
  have hs := congrArg sizeOf hcycle
  simp only [FGBlock.node.sizeOf_spec] at hs
  omega

/-- The transported birth is this node when its justification height is
its parent's height. A proper ancestor has a smaller justification height. -/
private theorem birth_at_target (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (x : Nat) (rs : List (Row (Fin p.n)))
    (hj : (derive p K (.node P s x rs)).h_j = (derive p K P).h)
    (hJ : (derive p K (.node P s x rs)).J = (derive p K P).T_h) :
    JustificationBirth p.E (certificateHeight p K) (.node P s x rs)
      (derive p K P).h (derive p K P).T_h := by
  let B := FGBlock.node P s x rs
  change (derive p K B).h_j = (derive p K P).h at hj
  change (derive p K B).J = (derive p K P).T_h at hJ
  have hb := windowHeightBridge p K hK B
  have hjb := congrArg FGHeight.h_j hb
  have hJb := congrArg FGHeight.J hb
  change (derive p K B).h_j = (SimplexFG.derive p.E p.cfg B).h_j at hjb
  change (derive p K B).J = (SimplexFG.derive p.E p.cfg B).J at hJb
  have hg := windowHeightLaws p K hK
  have hnz : (SimplexFG.derive p.E p.cfg B).h_j ≠ 0 := by
    rw [← hjb, hj]
    exact Nat.ne_of_gt (hg.one_le_h P)
  obtain ⟨C, hCB, hbirth, _⟩ := simplex_justification_birth_interval p.E p.cfg B hnz
  have hw := (justificationBirth_window_iff_simplex p K hK C _ _).mpr hbirth
  rw [← hjb, ← hJb] at hw
  have hC : C = B := by
    by_contra hne
    have hCP := preceq_parent_of_preceq_node hCB hne
    have hm := hg.h_mono hCP
    have hlt := hg.justified_below_height C
    have hcj := hw.2.2.2.1
    change (derive p K C).h_j = (derive p K B).h_j at hcj
    change (derive p K C).h ≤ (derive p K P).h at hm
    change (derive p K C).h_j < (derive p K C).h at hlt
    rw [hj] at hcj
    exact (Nat.not_lt_of_ge hm) (hcj ▸ hlt)
  subst C
  simpa only [hj, hJ] using hw

/-- The row fold changes only bits of existing entries. Each new bit names
an exact finality pair from a row in this fold. -/
private theorem fold_sources (p : Params) (rs : List (Row (Fin p.n)))
    (w : State (Fin p.n)) :
    (rs.foldl process_row w).h = w.h ∧
    (rs.foldl process_row w).T_h = w.T_h ∧
    ∀ e ∈ (rs.foldl process_row w).W, ∃ d ∈ w.W,
      d.j = e.j ∧ d.X = e.X ∧
      ∀ i ∈ e.Q, i ∈ d.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have row (w : State (Fin p.n)) (a : Row (Fin p.n)) :
      (process_row w a).h = w.h ∧ (process_row w a).T_h = w.T_h ∧
      (process_row w a).W = w.W.map (fun e =>
        if a.finality_pair = some ⟨e.j, e.X.root⟩ then
          { e with Q := insert a.signer e.Q } else e) := by
    obtain ⟨i, pair, fp⟩ := a
    cases pair with
    | empty => simp only [process_row_def, NamedHeightPair.matchesEntry]; exact ⟨rfl, rfl, rfl⟩
    | vote j X t =>
        cases t <;> simp only [process_row_def] <;> split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  induction rs generalizing w with
  | nil => exact ⟨rfl, rfl, fun e he => ⟨e, he, rfl, rfl, fun _ hi => Or.inl hi⟩⟩
  | cons a rs ih =>
      obtain ⟨hh, hT, hs⟩ := ih (process_row w a)
      obtain ⟨rh, rT, rW⟩ := row w a
      refine ⟨hh.trans rh, hT.trans rT, ?_⟩
      intro e he
      obtain ⟨d, hd, hj, hX, hbits⟩ := hs e he
      rw [rW, List.mem_map] at hd
      obtain ⟨c, hc, hcd⟩ := hd
      have keys : c.j = d.j ∧ c.X.root = d.X.root := by
        split_ifs at hcd <;> subst d <;> exact ⟨rfl, rfl⟩
      have cX : c.X = e.X := (FGBlock.root_injective keys.2).trans hX
      have cj := keys.1.trans hj
      refine ⟨c, hc, cj, cX, ?_⟩
      intro i hi
      rcases hbits i hi with hi | ⟨b, hb, hbi, hbf⟩
      · split_ifs at hcd with hm
        · subst d
          rcases Finset.mem_insert.mp hi with hi | hi
          · exact Or.inr ⟨a, List.mem_cons_self, hi.symm, by simpa only [cj, cX] using hm⟩
          · exact Or.inl hi
        · subst d; exact Or.inl hi
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hbi, hbf⟩

private theorem prefinal_of_parent (p : Params) (K : Nat)
    (P : FGBlock (Fin p.n)) (s : Slot) (x : Nat) (rs : List (Row (Fin p.n)))
    (hp : ∀ e ∈ (derive p K P).W, EntryOriginAt p K P e)
    (e : Entry (Fin p.n)) (he : e ∈ (certificateFolded p K (.node P s x rs)).W) :
    ∃ C, StrictPrefix C (.node P s x rs) ∧
      JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier (.node P s x rs) ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  obtain ⟨d, hd, hj, hX, hbits⟩ :=
    (fold_sources p rs { derive p K P with s := s }).2.2 e he
  obtain ⟨C, hCP, hb, hw⟩ := hp d hd
  refine ⟨C, strict_node p s x rs hCP, ?_, ?_⟩
  · simpa only [hj, hX] using hb
  · intro i hi
    rcases hbits i hi with hi | ⟨a, ha, hai, haf⟩
    · obtain ⟨carrier, a, hCc, hcP, ha, hai, haf⟩ := hw i hi
      exact ⟨carrier, a, hCc, preceq_node_of_preceq s x rs hcP, ha, hai,
        by simpa only [hj, hX] using haf⟩
    · exact ⟨.node P s x rs, a, strict_node p s x rs hCP, preceq_refl _, ha, hai, haf⟩

/-- [bp §3.1–3.2] Every retained entry has a birth on this chain and exact
finality rows strictly after that birth. A new entry has no bits. -/
theorem window_entry_origin (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n))
    (he : e ∈ (derive p K B).W) : EntryOriginAt p K B e := by
  induction B generalizing e with
  | genesis => exact (List.not_mem_nil he).elim
  | node P s x rs ih =>
      let B := FGBlock.node P s x rs
      let w := certificateFolded p K B
      let f := finalizeWindow p.E w
      have hf : f.h = w.h ∧ f.T_h = w.T_h ∧ f.W ⊆ w.W := by
        dsimp only [f]
        rw [finalizeWindow_def]
        cases greatestReady p.E w <;> simp
      have ff := fold_sources p rs { derive p K P with s := s }
      have fh : f.h = (derive p K P).h := hf.1.trans ff.1
      have fT : f.T_h = (derive p K P).T_h := hf.2.1.trans ff.2.1
      have old (d : Entry (Fin p.n)) (hd : d ∈ f.W) : EntryOriginAt p K B d := by
        obtain ⟨C, hC, hb, hw⟩ := prefinal_of_parent p K P s x rs ih d (hf.2.2 hd)
        exact ⟨C, hC.1, hb, hw⟩
      change e ∈ (process_height_events p.E p.cfg K w).W at he
      rw [process_height_events_def] at he
      change e ∈ (if targetQuorum p.E f then
        advance_height { f with
          J := f.T_h
          h_j := f.h
          W := (f.W ++ [Entry.mk f.h f.T_h ∅]).drop ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) }
        else if progReady p.E p.cfg f then advance_height f else f).W at he
      split_ifs at he with ht
      · rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
        · exact old e he
        · obtain rfl := List.mem_singleton.mp he
          have hnew : derive p K B = advance_height { f with
              J := f.T_h, h_j := f.h,
              W := (f.W ++ [Entry.mk f.h f.T_h ∅]).drop
                ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) } := by
            change process_height_events p.E p.cfg K w = _
            rw [process_height_events_def, ite_eq_left ht]
          refine ⟨B, preceq_refl _, ?_, ?_⟩
          · rw [fh, fT]
            apply birth_at_target p K hK P s x rs
            · rw [hnew]; exact fh
            · rw [hnew]; exact fT
          · intro i hi; exact (Finset.notMem_empty i hi).elim
      · exact old e he
      · exact old e he

/-- [spec 1220–1227] An entry available to finality was born strictly
before this block; rows in its birth block cannot set its bits. -/
theorem window_prefinal_entry_origin (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n))
    (he : e ∈ (certificateFolded p K B).W) :
    ∃ C, StrictPrefix C B ∧
      JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  cases B with
  | genesis => exact (List.not_mem_nil he).elim
  | node P s x rs =>
      exact prefinal_of_parent p K P s x rs (window_entry_origin p K hK P) e he

end AvailableChain.FGSA.Window
end
