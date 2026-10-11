module
public import AvailableChainFGSA.Proofs.WindowSteps
public import AvailableChainKitFG.WindowInvariant
public import AvailableChainKitFG.WindowTransport

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

section

private abbrev Old := FGSA.Window.State
private abbrev New := SimplexFG.Window.State

private def toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def toWindow {V : Type} (w : Old V) : New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (toEntry e).j = e.j ∧ (toEntry e).X = e.X ∧ (toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem state_fields {V : Type} (w : Old V) :
    (toWindow w).L = w.L ∧ (toWindow w).s = w.s ∧
    (toWindow w).h = w.h ∧ (toWindow w).T_h = w.T_h ∧
    (toWindow w).target_participation = w.target_participation ∧
    (toWindow w).progress = w.progress ∧ (toWindow w).W = w.W.map toEntry ∧
    (toWindow w).J = w.J ∧ (toWindow w).h_j = w.h_j ∧
    (toWindow w).F = w.F ∧ (toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem initial_eq {V : Type} :
    toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem row_eq (w : Old V) (a : Row V) :
    toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map toEntry =
      (w.W.map toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [toEntry, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row, SimplexFG.Window.process_row,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, toWindow] using
        congrArg (fun es => ({ toWindow w with W := es } : New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row, SimplexFG.Window.process_row,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [toWindow] <;> rw [bits] <;> simp_all [toWindow]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem rows_eq (rs : List (Row V)) (w : Old V) :
    toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem advance_eq (w : Old V) :
    toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem greatest_eq (E : Electorate V) (w : Old V) :
    (FGSA.Window.greatestReady E w).map toEntry =
      SimplexFG.Window.greatestReady E (toWindow w) := by
  classical
  let oldStep := fun (best : Option (FGSA.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      match best with
      | none => some e
      | some old => if old.j < e.j then some e else best
    else best
  let newStep := fun (best : Option (SimplexFG.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      match best with
      | none => some e
      | some old => if old.j < e.j then some e else best
    else best
  have step (best) (e) :
      (oldStep best e).map toEntry = newStep (best.map toEntry) (toEntry e) := by
    dsimp [oldStep, newStep, toEntry]
    split_ifs <;> cases best <;> simp_all [toEntry]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map toEntry =
        (es.map toEntry).foldl newStep (best.map toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  convert fold w.W none using 1 <;>
    simp only [FGSA.Window.greatestReady, SimplexFG.Window.greatestReady, toWindow]
  · congr 2
    funext best e
    cases best <;> rfl
  · congr 1
    funext best e
    cases best <;> rfl

omit [DecidableEq V] [RowCodec V] in
private theorem finalize_eq (E : Electorate V) (w : Old V) :
    toWindow (FGSA.Window.finalizeWindow E w) =
      SimplexFG.Window.finalizeWindow E (toWindow w) := by
  unfold FGSA.Window.finalizeWindow SimplexFG.Window.finalizeWindow
  rw [← greatest_eq]
  cases FGSA.Window.greatestReady E w <;>
    simp [toWindow, toEntry, List.filter_map, Function.comp_def] <;> rfl

omit [DecidableEq V] [RowCodec V] [Fintype V] in
/-- Appending the new empty entry and dropping old entries preserve conversion. -/
private theorem append_eviction_eq (es : List (FGSA.Window.Entry V))
    (j : Height) (X : FGBlock V) (K : Nat) :
    ((es ++ [FGSA.Window.Entry.mk j X ∅]).drop
      ((es ++ [FGSA.Window.Entry.mk j X ∅]).length - K)).map toEntry =
      (es.map toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).drop
        ((es.map toEntry ++ [SimplexFG.Window.Entry.mk j X ∅]).length - K) := by
  simp [List.map_drop, toEntry]

omit [DecidableEq V] [RowCodec V] in
private theorem events_eq (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : Old V) :
    toWindow (FGSA.Window.process_height_events E cfg K w) =
      SimplexFG.Window.process_height_events E cfg K (toWindow w) := by
  unfold FGSA.Window.process_height_events SimplexFG.Window.process_height_events
  rw [← finalize_eq]
  generalize FGSA.Window.finalizeWindow E w = u
  change toWindow (if FGSA.Window.targetQuorum E u then _ else _) =
    (if FGSA.Window.targetQuorum E u then _ else _)
  rw [show SimplexFG.Window.progReady E cfg (toWindow u) =
    FGSA.Window.progReady E cfg u from rfl]
  split_ifs <;>
    simp [FGSA.Window.advance_height, SimplexFG.Window.advance_height,
      toWindow, toEntry, List.map_drop]

private theorem transition_eq (p : Params) (K : Nat) (w : Old (Fin p.n))
    (B : FGBlock (Fin p.n)) (rs : List (Row (Fin p.n))) :
    toWindow (FGSA.Window.transition p K w B rs) =
      SimplexFG.Window.transition p.E p.cfg K (toWindow w) B rs := by
  rw [FGSA.Window.transition_def, events_eq, SimplexFG.Window.transition_def]
  have h := rows_eq rs { w with s := B.slot }
  change SimplexFG.Window.process_height_events p.E p.cfg K
    { toWindow (rs.foldl FGSA.Window.process_row { w with s := B.slot }) with L := B } = _
  rw [h]
  rfl

private theorem foldMap (p : Params) (K : Nat) :
    KitFG.WindowFoldMap p.E p.cfg K FGSA.Window.initial (FGSA.Window.transition p K)
      (FGSA.Window.derive p K) toWindow where
  initial := initial_eq
  genesis := rfl
  node := fun _ _ _ _ _ => rfl
  step := transition_eq p K

private theorem derive_eq (p : Params) (K : Nat) (B : FGBlock (Fin p.n)) :
    toWindow (FGSA.Window.derive p K B) = SimplexFG.Window.derive p.E p.cfg K B :=
  (foldMap p K).fold_eq B

end

private theorem empty_not_quorum (p : Params) : ¬ p.E.IsQuorum ∅ := by
  have hn := p.nPos
  dsimp only [Params.E, Electorate.IsQuorum, Electorate.q, Electorate.totalWeight,
    Electorate.weightOf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Finset.card_empty]
  omega

private theorem entry_mem (p : Params) (K : Nat) (B : FGBlock (Fin p.n))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K B).W) :
    toEntry e ∈ (SimplexFG.Window.derive p.E p.cfg K B).W := by
  rw [← derive_eq]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- [bp §3.1; W5] Entry heights strictly increase in chain order. -/
theorem window_ordered (p : Params) (K : Nat) (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    ((derive p K B).W).Pairwise (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X) := by
  simpa only [← derive_eq, toWindow, List.pairwise_map, List.length_map, toEntry] using
    KitFG.Window.window_ordered p.E p.cfg K (empty_not_quorum p) hK B

/-- [bp §3.1] Every retained entry lies between finality and the latest justification. -/
theorem window_bounds (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n)) (he : e ∈ (derive p K B).W) :
    (derive p K B).h_F < e.j ∧ e.j ≤ (derive p K B).h_j ∧
    FGBlock.Preceq (derive p K B).F e.X ∧ FGBlock.Preceq e.X (derive p K B).J := by
  simpa only [← derive_eq, toWindow, toEntry] using
    KitFG.Window.window_bounds p.E p.cfg K (empty_not_quorum p) hK B
      (toEntry e) (entry_mem p K B e he)

/-- [bp §3.1] The window keeps at most K entries. -/
theorem window_capacity (p : Params) (K : Nat) (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (derive p K B).W.length ≤ K := by
  simpa only [← derive_eq, toWindow, List.pairwise_map, List.length_map, toEntry] using
    KitFG.Window.window_capacity p.E p.cfg K (empty_not_quorum p) hK B

/-- [bp §3.1] Finality removes every ready entry; new entries have no bits. -/
theorem window_post_not_ready (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (e : Entry (Fin p.n)) (he : e ∈ (derive p K B).W) :
    ¬ p.E.IsQuorum e.Q := by
  simpa only [← derive_eq, toWindow, toEntry] using
    KitFG.Window.window_post_not_ready p.E p.cfg K (empty_not_quorum p) hK B
      (toEntry e) (entry_mem p K B e he)

/-- [bp §3.1] Finality precedes the latest justification. -/
theorem window_F_preceq_J (p : Params) (K : Nat) (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    FGBlock.Preceq (derive p K B).F (derive p K B).J := by
  simpa only [← derive_eq, toWindow, List.pairwise_map, List.length_map, toEntry] using
    KitFG.Window.window_F_preceq_J p.E p.cfg K (empty_not_quorum p) hK B

/-- [bp §3.1] Finalized height does not exceed justified height. -/
theorem window_hF_le_hj (p : Params) (K : Nat) (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (derive p K B).h_F ≤ (derive p K B).h_j := by
  simpa only [← derive_eq, toWindow, List.pairwise_map, List.length_map, toEntry] using
    KitFG.Window.window_hF_le_hj p.E p.cfg K (empty_not_quorum p) hK B

/-- [bp §3.1] Finality at height zero is genesis. -/
theorem window_finalized_zero (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (hz : (derive p K B).h_F = 0) :
    (derive p K B).F = .genesis := by
  have hz' : (SimplexFG.Window.derive p.E p.cfg K B).h_F = 0 := by
    simpa only [← derive_eq, toWindow] using hz
  simpa only [← derive_eq, toWindow] using
    KitFG.Window.window_finalized_zero p.E p.cfg K (empty_not_quorum p) hK B hz'

/-- [bp §3.1] Finalized height is monotone along ancestry. -/
theorem window_hF_mono (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) :
    (derive p K A).h_F ≤ (derive p K B).h_F := by
  simpa only [← derive_eq, toWindow, List.pairwise_map, List.length_map, toEntry] using
    KitFG.Window.window_hF_mono p.E p.cfg K (empty_not_quorum p) hK A B hAB

/-- [bp §3.1] Finalized blocks are monotone along ancestry. -/
theorem window_F_mono (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) :
    FGBlock.Preceq (derive p K A).F (derive p K B).F := by
  simpa only [← derive_eq, toWindow, List.pairwise_map, List.length_map, toEntry] using
    KitFG.Window.window_F_mono p.E p.cfg K (empty_not_quorum p) hK A B hAB

/-- [bp §3.1] Bits only grow while the exact entry is retained. -/
theorem window_bit_retained (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e d : Entry (Fin p.n)) (he : e ∈ (derive p K A).W) (hd : d ∈ (derive p K B).W)
    (hj : e.j = d.j) (hX : e.X = d.X) : e.Q ⊆ d.Q := by
  exact KitFG.Window.window_bit_retained p.E p.cfg K (empty_not_quorum p) hK A B hAB
    (toEntry e) (toEntry d) (entry_mem p K A e he) (entry_mem p K B d hd) hj hX

/-- [bp §3.1] Removal is permanent: all later births have greater height. -/
theorem window_no_reentry (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B C : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) (hBC : FGBlock.Preceq B C)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) :
    ¬ ∃ d ∈ (derive p K C).W, d.j = e.j ∧ d.X = e.X := by
  have gone' : ¬ ∃ d ∈ (SimplexFG.Window.derive p.E p.cfg K B).W,
      d.j = (toEntry e).j ∧ d.X = (toEntry e).X := by
    rintro ⟨d, hd, hj, hX⟩
    rw [← derive_eq] at hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact gone ⟨c, hc, hj, hX⟩
  have h := KitFG.Window.window_no_reentry p.E p.cfg K (empty_not_quorum p) hK A B C hAB hBC
    (toEntry e) (entry_mem p K A e he) gone'
  rintro ⟨d, hd, hj, hX⟩
  exact h ⟨toEntry d, entry_mem p K C d hd, hj, hX⟩

/-- [design §5; bp 22 I7] A covered quorum finalizes this entry or a later entry. -/
theorem window_finality_of_cover (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (Q : Finset (Fin p.n)) (hQ : p.E.IsQuorum Q)
    (hcover : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ a ∈ rs,
      a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) :
    FGBlock.Preceq e.X (derive p K (.node P s r_s x rs)).F ∧
      e.j ≤ (derive p K (.node P s r_s x rs)).h_F := by
  simpa only [← derive_eq, toWindow, toEntry] using
    KitFG.Window.window_finality_of_cover p.E p.cfg K (empty_not_quorum p) hK P s r_s x rs
      (toEntry e) (entry_mem p K P e he) Q hQ hcover

#print axioms entry_fields
#print axioms state_fields
#print axioms initial_eq
#print axioms row_eq
#print axioms rows_eq
#print axioms advance_eq
#print axioms greatest_eq
#print axioms finalize_eq
#print axioms append_eviction_eq
#print axioms events_eq
#print axioms transition_eq
#print axioms foldMap
#print axioms derive_eq
#print axioms empty_not_quorum
#print axioms entry_mem

end AvailableChain.FGSA.Window
end
