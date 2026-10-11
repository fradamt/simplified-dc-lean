module
public import AvailableChainFGSA.Statements.WindowCertificate
public import AvailableChainFGSA.Proofs.WindowHeightBridge
public import AvailableChainKitFG.WindowSteps

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

end

private theorem toEntry_injective {V : Type} :
    Function.Injective (toEntry (V := V)) := by
  intro a b h
  cases a
  cases b
  simpa only [toEntry, SimplexFG.Window.Entry.mk.injEq, Entry.mk.injEq] using h

private theorem mem_toEntry {V : Type} (e : Entry V) (es : List (Entry V)) :
    toEntry e ∈ es.map toEntry ↔ e ∈ es :=
  List.mem_map_of_injective toEntry_injective

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- [bp §3.1] One row changes only the bits of its exact entry. -/
def window_addBit (a : Row V) (e : Entry V) : Entry V :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then { e with Q := insert a.signer e.Q } else e

private theorem addBit_eq (a : Row V) (e : Entry V) :
    toEntry (window_addBit a e) = KitFG.Window.window_addBit a (toEntry e) := by
  by_cases h : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
    simp [window_addBit, KitFG.Window.window_addBit, toEntry, h]

private theorem bits_fold_eq (rs : List (Row V)) (e : Entry V) :
    toEntry (rs.foldl (fun e a => window_addBit a e) e) =
      rs.foldl (fun e a => KitFG.Window.window_addBit a e) (toEntry e) := by
  induction rs generalizing e with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, addBit_eq]

theorem window_addBit_key (a : Row V) (e : Entry V) :
    (window_addBit a e).j = e.j ∧ (window_addBit a e).X = e.X := by
  have h := KitFG.Window.window_addBit_key a (toEntry e)
  rw [← addBit_eq] at h
  exact h

theorem window_addBit_bits (a : Row V) (e : Entry V) (i : V) :
    i ∈ (window_addBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  have h := KitFG.Window.window_addBit_bits a (toEntry e) i
  rw [← addBit_eq] at h
  exact h

theorem window_row_fields (w : State V) (a : Row V) :
    (process_row w a).W = w.W.map (window_addBit a) ∧
    (process_row w a).h = w.h ∧ (process_row w a).T_h = w.T_h ∧
    (process_row w a).h_j = w.h_j ∧ (process_row w a).J = w.J ∧
    (process_row w a).h_F = w.h_F ∧ (process_row w a).F = w.F := by
  have h := KitFG.Window.window_row_fields (toWindow w) a
  simp only [← row_eq] at h
  simp only [toWindow, List.map_map, Function.comp_def, ← addBit_eq] at h
  exact ⟨(List.map_injective_iff.mpr toEntry_injective) (by
    simpa only [List.map_map, Function.comp_def] using h.1), h.2⟩

theorem window_fold_fields (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W = w.W.map (fun e => rs.foldl (fun e a => window_addBit a e) e) ∧
    (rs.foldl process_row w).h = w.h ∧ (rs.foldl process_row w).T_h = w.T_h ∧
    (rs.foldl process_row w).h_j = w.h_j ∧ (rs.foldl process_row w).J = w.J ∧
    (rs.foldl process_row w).h_F = w.h_F ∧ (rs.foldl process_row w).F = w.F := by
  have h := KitFG.Window.window_fold_fields rs (toWindow w)
  simp only [← rows_eq] at h
  simp only [toWindow, List.map_map, Function.comp_def, ← bits_fold_eq] at h
  exact ⟨(List.map_injective_iff.mpr toEntry_injective) (by
    simpa only [List.map_map, Function.comp_def] using h.1), h.2⟩

theorem window_fold_entry (rs : List (Row V)) (e : Entry V) :
    let d := rs.foldl (fun e a => window_addBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have h := KitFG.Window.window_fold_entry rs (toEntry e)
  dsimp only at h
  rw [← bits_fold_eq] at h
  exact h

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
/-- The fold selects a ready member and dominates every ready height. -/
theorem window_greatest_spec (E : Electorate V) (w : State V) :
    (∀ e, greatestReady E w = some e →
      e ∈ w.W ∧ w.h_F < e.j ∧ E.IsQuorum e.Q) ∧
    (∀ d ∈ w.W, w.h_F < d.j → E.IsQuorum d.Q →
      ∃ e, greatestReady E w = some e ∧ d.j ≤ e.j) := by
  have h := KitFG.Window.window_greatest_spec E (toWindow w)
  constructor
  · intro e he
    have hm : SimplexFG.Window.greatestReady E (toWindow w) = some (toEntry e) := by
      rw [← greatest_eq, he]
      rfl
    have hs := h.1 (toEntry e) hm
    exact ⟨(mem_toEntry e w.W).mp hs.1, hs.2⟩
  · intro d hd hf hq
    obtain ⟨e, he, hj⟩ := h.2 (toEntry d) ((mem_toEntry d w.W).mpr hd) hf hq
    rw [← greatest_eq] at he
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    exact ⟨a, ha, hj⟩

theorem window_strict_node (p : Params) {C P : FGBlock (Fin p.n)}
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n))) (hCP : FGBlock.Preceq C P) :
    StrictPrefix C (.node P s r_s x rs) := by
  exact KitFG.Window.window_strict_node s r_s x rs hCP

/-- The row fold changes only bits of existing entries. Each new bit names
an exact finality pair from a row in this fold. -/
theorem window_fold_sources (p : Params) (rs : List (Row (Fin p.n)))
    (w : State (Fin p.n)) :
    (rs.foldl process_row w).h = w.h ∧
    (rs.foldl process_row w).T_h = w.T_h ∧
    ∀ e ∈ (rs.foldl process_row w).W, ∃ d ∈ w.W,
      d.j = e.j ∧ d.X = e.X ∧
      ∀ i ∈ e.Q, i ∈ d.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have h := KitFG.Window.window_fold_sources rs (toWindow w)
  rw [← rows_eq] at h
  refine ⟨h.1, h.2.1, ?_⟩
  intro e he
  obtain ⟨d, hd, hj, hX, hb⟩ :=
    h.2.2 (toEntry e) ((mem_toEntry e _).mpr he)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact ⟨c, hc, hj, hX, hb⟩

#print axioms entry_fields
#print axioms state_fields
#print axioms initial_eq
#print axioms row_eq
#print axioms rows_eq
#print axioms advance_eq
#print axioms greatest_eq
#print axioms toEntry_injective
#print axioms mem_toEntry
#print axioms addBit_eq
#print axioms bits_fold_eq

end AvailableChain.FGSA.Window
end
