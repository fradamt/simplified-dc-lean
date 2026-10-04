module
public import AvailableChainFGSA.Proofs.WindowCertificates

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

variable {V : Type} [DecidableEq V] [RowCodec V]

private def addBit (a : Row V) (e : Entry V) : Entry V :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then { e with Q := insert a.signer e.Q } else e

private theorem addBit_key (a : Row V) (e : Entry V) :
    (addBit a e).j = e.j ∧ (addBit a e).X = e.X := by
  unfold addBit
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem addBit_bits (a : Row V) (e : Entry V) (i : V) :
    i ∈ (addBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  unfold addBit
  split_ifs with h <;> simp [h, eq_comm, or_comm]

private theorem row_fields (w : State V) (a : Row V) :
    (process_row w a).W = w.W.map (addBit a) ∧
    (process_row w a).h = w.h ∧ (process_row w a).T_h = w.T_h ∧
    (process_row w a).h_j = w.h_j ∧ (process_row w a).J = w.J ∧
    (process_row w a).h_F = w.h_F ∧ (process_row w a).F = w.F := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [process_row_def, NamedHeightPair.matchesEntry]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def] <;> split_ifs <;>
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fold_fields (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W = w.W.map (fun e => rs.foldl (fun e a => addBit a e) e) ∧
    (rs.foldl process_row w).h = w.h ∧ (rs.foldl process_row w).T_h = w.T_h ∧
    (rs.foldl process_row w).h_j = w.h_j ∧ (rs.foldl process_row w).J = w.J ∧
    (rs.foldl process_row w).h_F = w.h_F ∧ (rs.foldl process_row w).F = w.F := by
  induction rs generalizing w with
  | nil => simp
  | cons a rs ih =>
      have h := row_fields w a
      have t := ih (process_row w a)
      simpa only [List.foldl_cons, t.1, h.1, List.map_map, Function.comp_def,
        t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
        t.2.2.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2] using
        (show True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True from by trivial)

private theorem fold_entry (rs : List (Row V)) (e : Entry V) :
    let d := rs.foldl (fun e a => addBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  induction rs generalizing e with
  | nil => simp
  | cons a rs ih =>
      have h := ih (addBit a e)
      have k := addBit_key a e
      simp only [List.foldl_cons]
      refine ⟨h.1.trans k.1, h.2.1.trans k.2, ?_⟩
      intro i
      rw [h.2.2, addBit_bits, k.1, k.2]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

private theorem greatest_mem (p : Params) (w : State (Fin p.n))
    (e : Entry (Fin p.n)) (he : greatestReady p.E w = some e) : e ∈ w.W := by
  let step := fun (best : Option (Entry (Fin p.n))) d =>
    if w.h_F < d.j ∧ p.E.q ≤ p.E.weightOf d.Q then
      best.elim (some d) (fun old => if old.j < d.j then some d else best)
    else best
  have go (xs : List (Entry (Fin p.n))) (best : Option (Entry (Fin p.n))) :
      xs.foldl step best = some e → best = some e ∨ e ∈ xs := by
    induction xs generalizing best with
    | nil => simp
    | cons a xs ih =>
        intro h
        rcases ih (step best a) h with h | h
        · dsimp [step] at h
          split_ifs at h <;> cases best <;> simp_all
          all_goals aesop
        · exact Or.inr (List.mem_cons_of_mem _ h)
  have heq : greatestReady p.E w = w.W.foldl step none := by
    rw [greatestReady_def]
    congr 1
    funext best d
    dsimp [step]
    split_ifs <;> cases best <;> rfl
  exact (go w.W none (heq ▸ he)).resolve_left (by simp)

private theorem final_fields (p : Params) (w : State (Fin p.n)) :
    (finalizeWindow p.E w).h = w.h ∧
    (finalizeWindow p.E w).T_h = w.T_h ∧
    (finalizeWindow p.E w).h_j = w.h_j ∧
    (finalizeWindow p.E w).J = w.J ∧
    (finalizeWindow p.E w).W =
      w.W.filter (fun e => decide ((finalizeWindow p.E w).h_F < e.j)) := by
  rw [finalizeWindow_def]
  cases greatestReady p.E w <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem events_finality (p : Params) (K : Nat) (w : State (Fin p.n)) :
    (process_height_events p.E p.cfg K w).F = (finalizeWindow p.E w).F ∧
    (process_height_events p.E p.cfg K w).h_F = (finalizeWindow p.E w).h_F := by
  rw [process_height_events_def]
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- Every nonzero finalized pair was born on this chain, including pairs
whose older entries have already left the window. -/
theorem window_final_birth (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) (hnz : (derive p K B).h_F ≠ 0) :
    ∃ C, FGBlock.Preceq C B ∧ JustificationBirth p.E (certificateHeight p K)
      C (derive p K B).h_F (derive p K B).F := by
  induction B with
  | genesis => exact (hnz rfl).elim
  | node P s r_s x rs ih =>
      let B := FGBlock.node P s r_s x rs
      let w := certificateFolded p K B
      have ff := fold_fields rs { derive p K P with s := s }
      have ef := events_finality p K w
      change (derive p K B).F = _ ∧ (derive p K B).h_F = _ at ef
      rw [ef.2] at hnz
      rw [ef.1, ef.2]
      cases hg : greatestReady p.E w with
      | none =>
          have hF : (finalizeWindow p.E w).F = (derive p K P).F := by
            rw [finalizeWindow_def, hg]; exact ff.2.2.2.2.2.2
          have hh : (finalizeWindow p.E w).h_F = (derive p K P).h_F := by
            rw [finalizeWindow_def, hg]; exact ff.2.2.2.2.2.1
          rw [hh, hF]
          obtain ⟨C, hc, hb⟩ := ih (hh ▸ hnz)
          exact ⟨C, preceq_node_of_preceq s r_s x rs hc, hb⟩
      | some d =>
          obtain ⟨C, hc, hb, _⟩ := window_prefinal_entry_origin p K hK B d
            (greatest_mem p w d hg)
          refine ⟨C, hc.1, ?_⟩
          simpa only [finalizeWindow_def, hg] using hb

private theorem birth_geometry (p : Params) (K : Nat) (hK : 2 ≤ K)
    {C X : FGBlock (Fin p.n)} {j : Height}
    (hb : JustificationBirth p.E (certificateHeight p K) C j X) :
    FGBlock.Preceq X C ∧ (certificateHeight p K X).h = j ∧
      (certificateHeight p K X).T_h = X := by
  have laws : FGHeightLaws p.E (certificateHeight p K) := windowHeightLaws p K hK
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb.2.2.1]
    apply preceq_trans (laws.entry_preceq C.parent)
    cases C with
    | genesis => exact preceq_refl _
    | node P s r_s x rs => exact preceq_parent_node P s r_s x rs
  · rw [← hb.2.2.1, laws.entry_same_height, hb.2.1]
  · rw [← hb.2.2.1, laws.entry_idem]

private theorem birth_order (p : Params) (K : Nat) (hK : 2 ≤ K)
    {B C D X Y : FGBlock (Fin p.n)} {j k : Height}
    (hC : FGBlock.Preceq C B) (hD : FGBlock.Preceq D B)
    (hbC : JustificationBirth p.E (certificateHeight p K) C j X)
    (hbD : JustificationBirth p.E (certificateHeight p K) D k Y)
    (hjk : j ≤ k) : FGBlock.Preceq X Y := by
  have c := birth_geometry p K hK hbC
  have d := birth_geometry p K hK hbD
  rcases preceq_total_of_common (preceq_trans c.1 hC) (preceq_trans d.1 hD) with h | h
  · exact h
  · have laws : FGHeightLaws p.E (certificateHeight p K) := windowHeightLaws p K hK
    have hm := laws.h_mono h
    have heq : (certificateHeight p K Y).h = (certificateHeight p K X).h := by
      change (certificateHeight p K Y).h ≤ (certificateHeight p K X).h at hm
      rw [d.2.1, c.2.1] at hm ⊢
      exact Nat.le_antisymm hm hjk
    have ht := laws.entry_plateau h heq
    change (certificateHeight p K Y).T_h = (certificateHeight p K X).T_h at ht
    rw [c.2.2, d.2.2] at ht
    rw [ht]
    exact preceq_refl _

/-- [bp §3.1; bp 22 I7] Every old key at or below finality is covered, even if
capacity removed it earlier. Birth order supplies the ancestry claim. -/
theorem window_le_hF_covered (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (hle : e.j ≤ (derive p K B).h_F) : FGBlock.Preceq e.X (derive p K B).F := by
  have hb := window_bounds p K hK A e he
  have hnz : (derive p K B).h_F ≠ 0 := Nat.ne_of_gt ((Nat.zero_lt_of_lt hb.1).trans_le hle)
  obtain ⟨C, hc, hbirth, _⟩ := window_entry_origin p K hK A e he
  obtain ⟨D, hd, hfinal⟩ := window_final_birth p K hK B hnz
  exact birth_order p K hK (preceq_trans hc hAB) hd hbirth hfinal hle

/-- [bp §3.1; bp 22 I7] The absent-key form of `window_le_hF_covered`. Absence is
not used; the form matches the COVERED case of `window_entry_history`. -/
theorem window_absent_le_hF_covered (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X)
    (hle : e.j ≤ (derive p K B).h_F) : FGBlock.Preceq e.X (derive p K B).F := by
  have _absent := gone
  exact window_le_hF_covered p K hK A B hAB e he hle

/-- At B an absent key that is not covered is strictly above finality.
This does not assert that it stays uncovered at later blocks. -/
theorem window_evicted_above_hF (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X)
    (uncovered : ¬ (e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F)) :
    (derive p K B).h_F < e.j := by
  by_contra h
  have hle := Nat.le_of_not_gt h
  exact uncovered ⟨hle, window_absent_le_hF_covered p K hK A B hAB e he gone hle⟩

/-- [bp §3.1] Retention at both ends forbids a gap and preserves all bits. -/
theorem window_retained_bits_mono (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B C : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B) (hBC : FGBlock.Preceq B C)
    (e d : Entry (Fin p.n)) (he : e ∈ (derive p K A).W) (hd : d ∈ (derive p K C).W)
    (hj : d.j = e.j) (hX : d.X = e.X) :
    ∃ b ∈ (derive p K B).W, b.j = e.j ∧ b.X = e.X ∧ e.Q ⊆ b.Q ∧ b.Q ⊆ d.Q := by
  have present : ∃ b ∈ (derive p K B).W, b.j = e.j ∧ b.X = e.X := by
    by_contra gone
    exact window_no_reentry p K hK A B C hAB hBC e he gone ⟨d, hd, hj, hX⟩
  obtain ⟨b, hb, hbj, hbX⟩ := present
  exact ⟨b, hb, hbj, hbX,
    window_bit_retained p K hK A B hAB e b he hb hbj.symm hbX.symm,
    window_bit_retained p K hK B C hBC b d hb hd (hbj.trans hj.symm) (hbX.trans hX.symm)⟩

/-- [spec 605–607] A step keeps the latest pair unless it crosses a target
quorum. Pruning does not clear the pair; a capacity append writes a new pair. -/
theorem window_latest_pair_kept (p : Params) (K : Nat)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n))) :
    let B := FGBlock.node P s r_s x rs
    let w := certificateFolded p K B
    ((derive p K B).h_j = (derive p K P).h_j ∧
      (derive p K B).J = (derive p K P).J ∧
      targetQuorum p.E (finalizeWindow p.E w) = false) ∨
    ((derive p K B).h_j = (derive p K P).h ∧
      (derive p K B).J = (derive p K P).T_h ∧
      targetQuorum p.E (finalizeWindow p.E w) = true) := by
  dsimp only
  have ff := fold_fields rs { derive p K P with s := s }
  have fin := final_fields p (certificateFolded p K (.node P s r_s x rs))
  simp only [derive_def p K (.node P s r_s x rs), transition_def, process_height_events_def]
  split_ifs with ht
  · exact Or.inr ⟨fin.1.trans ff.2.1, fin.2.1.trans ff.2.2.1, ht⟩
  · exact Or.inl ⟨fin.2.2.1.trans ff.2.2.2.1, fin.2.2.2.1.trans ff.2.2.2.2.1,
      Bool.eq_false_iff.mpr ht⟩
  · exact Or.inl ⟨fin.2.2.1.trans ff.2.2.2.1, fin.2.2.2.1.trans ff.2.2.2.2.1,
      Bool.eq_false_iff.mpr ht⟩

omit [RowCodec V] in
private theorem drop_oldest (K : Nat) (xs : List (Entry V))
    (new e : Entry V) (hcap : xs.length ≤ K)
    (hord : (xs ++ [new]).Pairwise (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X))
    (he : e ∈ xs) (gone : e ∉ (xs ++ [new]).drop ((xs ++ [new]).length - K)) :
    ((xs ++ [new]).drop ((xs ++ [new]).length - K)).length = K ∧
    ∀ d ∈ (xs ++ [new]).drop ((xs ++ [new]).length - K), e.j < d.j := by
  have hlen : (xs ++ [new]).length = K + 1 := by
    simp only [List.length_append, List.length_singleton]
    by_contra h
    have hz : (xs ++ [new]).length - K = 0 := by
      simp only [List.length_append, List.length_singleton]; omega
    exact gone (by simpa only [hz, List.drop_zero] using List.mem_append_left [new] he)
  have hdrop : (xs ++ [new]).length - K = 1 := by omega
  rw [hdrop] at gone ⊢
  constructor
  · simp only [List.length_drop]; omega
  · cases xs with
    | nil => simp at he
    | cons a xs =>
        have hea : e = a := by
          rcases List.mem_cons.mp he with h | h
          · exact h
          · exact (gone (by simpa using List.mem_append_left [new] h)).elim
        subst e
        change (a :: (xs ++ [new])).Pairwise _ at hord
        exact fun d hd => ((List.pairwise_cons.mp hord).1 d hd).1

private theorem node_evicted (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (gone : ¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X)
    (above : (derive p K (.node P s r_s x rs)).h_F < e.j) :
    (derive p K (.node P s r_s x rs)).W.length = K ∧
    ∀ d ∈ (derive p K (.node P s r_s x rs)).W, e.j < d.j := by
  let B := FGBlock.node P s r_s x rs
  let w := certificateFolded p K B
  let f := finalizeWindow p.E w
  let d := rs.foldl (fun e a => addBit a e) e
  have ff := fold_fields rs { derive p K P with s := s }
  have dk := fold_entry rs e
  have fin := final_fields p w
  have ef := events_finality p K w
  have dw : d ∈ w.W := by
    change d ∈ (rs.foldl process_row { derive p K P with s := s }).W
    rw [ff.1]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have df : d ∈ f.W := by
    rw [fin.2.2.2.2, List.mem_filter]
    refine ⟨dw, decide_eq_true ?_⟩
    rw [← ef.2, dk.1]
    exact above
  have cap : f.W.length ≤ K := by
    rw [fin.2.2.2.2]
    refine (List.length_filter_le _ _).trans ?_
    change (rs.foldl process_row { derive p K P with s := s }).W.length ≤ K
    rw [ff.1, List.length_map]
    exact window_capacity p K hK P
  have ord : f.W.Pairwise (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X) := by
    rw [fin.2.2.2.2]
    apply List.Pairwise.filter
    change (rs.foldl process_row { derive p K P with s := s }).W.Pairwise _
    rw [ff.1, List.pairwise_map]
    exact (window_ordered p K hK P).imp (fun {a b} h => by
      simpa only [(fold_entry rs a).1, (fold_entry rs a).2.1,
        (fold_entry rs b).1, (fold_entry rs b).2.1] using h)
  have fh : w.h = (derive p K P).h := ff.2.1
  have fT : w.T_h = (derive p K P).T_h := ff.2.2.1
  have newer : ∀ a ∈ f.W, a.j < f.h ∧ FGBlock.Preceq a.X f.T_h := by
    intro a ha
    have haw := (List.mem_filter.mp (fin.2.2.2.2 ▸ ha)).1
    change a ∈ (rs.foldl process_row { derive p K P with s := s }).W at haw
    rw [ff.1, List.mem_map] at haw
    obtain ⟨c, hc, rfl⟩ := haw
    have cb := window_bounds p K hK P c hc
    have laws := windowHeightLaws p K hK
    exact ⟨by rw [(fold_entry rs c).1, fin.1, fh]
              exact cb.2.1.trans_lt (laws.justified_below_height P),
      by rw [(fold_entry rs c).2.1, fin.2.1, fT]
         exact preceq_trans cb.2.2.2 (laws.justified_preceq_entry P)⟩
  have appendOrd : (f.W ++ [Entry.mk f.h f.T_h ∅]).Pairwise
      (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X) := by
    rw [List.pairwise_append]
    exact ⟨ord, by simp, fun a ha b hb => List.mem_singleton.mp hb ▸ newer a ha⟩
  change (process_height_events p.E p.cfg K w).W.length = K ∧
    ∀ d ∈ (process_height_events p.E p.cfg K w).W, e.j < d.j
  change ¬ ∃ d ∈ (process_height_events p.E p.cfg K w).W, _ at gone
  rw [process_height_events_def] at gone ⊢
  dsimp only at gone ⊢
  split_ifs at gone ⊢ with ht hp
  · have gd : d ∉ (f.W ++ [Entry.mk f.h f.T_h ∅]).drop
        ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) := by
      intro hd
      exact gone ⟨d, hd, dk.1, dk.2.1⟩
    obtain ⟨hl, hn⟩ := drop_oldest K f.W _ d cap appendOrd df gd
    exact ⟨hl, fun a ha => dk.1 ▸ hn a ha⟩
  · exact (gone ⟨d, df, dk.1, dk.2.1⟩).elim
  · exact (gone ⟨d, df, dk.1, dk.2.1⟩).elim

/-- A capacity removal leaves exactly K newer entries. Each has a birth
strictly after the removed entry's birth on the same chain. -/
theorem window_evicted_has_K_newer (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n)))
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K P).W)
    (gone : ¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X)
    (above : (derive p K (.node P s r_s x rs)).h_F < e.j) :
    (derive p K (.node P s r_s x rs)).W.length = K ∧
    ∃ C, FGBlock.Preceq C P ∧
      JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
      ∀ d ∈ (derive p K (.node P s r_s x rs)).W, e.j < d.j ∧
        ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
          JustificationBirth p.E (certificateHeight p K) D d.j d.X := by
  obtain ⟨hl, hn⟩ := node_evicted p K hK P s r_s x rs e he gone above
  obtain ⟨C, hc, hb, _⟩ := window_entry_origin p K hK P e he
  refine ⟨hl, C, hc, hb, ?_⟩
  intro d hd
  obtain ⟨D, hD, hbirth, _⟩ := window_entry_origin p K hK (.node P s r_s x rs) d hd
  have hlt := hn d hd
  have heights : (certificateHeight p K C).h < (certificateHeight p K D).h := by
    rw [hb.2.2.2.2.2.1, hbirth.2.2.2.2.2.1]
    exact Nat.succ_lt_succ hlt
  have hCD : FGBlock.Preceq C D := by
    rcases preceq_total_of_common (preceq_node_of_preceq s r_s x rs hc) hD with h | h
    · exact h
    · exact (Nat.not_lt_of_ge ((windowHeightLaws p K hK).h_mono h) heights).elim
  exact ⟨hlt, D, ⟨hCD, fun h => by simp only [h, lt_self_iff_false] at heights⟩, hD, hbirth⟩

private theorem first_removal (p : Params) (K : Nat)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W)
    (gone : ¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) :
    ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
      (∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X) ∧
      ¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact (gone ⟨e, he, rfl, rfl⟩).elim
  | node P s r_s x rs ih =>
      by_cases ha : A = .node P s r_s x rs
      · subst A
        exact (gone ⟨e, he, rfl, rfl⟩).elim
      · have hAP := preceq_parent_of_preceq_node hAB ha
        by_cases hp : ∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X
        · exact ⟨P, s, r_s, x, rs, hAP, preceq_refl _, hp, gone⟩
        · obtain ⟨R, t, r_t, y, rows, hAR, hRP, hr, hg⟩ := ih hAP hp
          exact ⟨R, t, r_t, y, rows, hAR, preceq_node_of_preceq s r_s x rs hRP, hr, hg⟩

/-- [07-F entry] The cases refer to B's state and are exclusive by key
presence and coverage. A later finalization can cover an earlier eviction. -/
theorem window_entry_history (p : Params) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock (Fin p.n)) (hAB : FGBlock.Preceq A B)
    (e : Entry (Fin p.n)) (he : e ∈ (derive p K A).W) :
    (∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q) ∨
    ((¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) ∧
      e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F) ∨
    ((¬ ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X) ∧
      ¬ (e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F) ∧
      (derive p K B).h_F < e.j ∧
      ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
        (∃ d ∈ (derive p K P).W, d.j = e.j ∧ d.X = e.X) ∧
        (¬ ∃ d ∈ (derive p K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X) ∧
        (derive p K (.node P s r_s x rs)).W.length = K ∧
        ∃ C, FGBlock.Preceq C P ∧
          JustificationBirth p.E (certificateHeight p K) C e.j e.X ∧
          ∀ d ∈ (derive p K (.node P s r_s x rs)).W, e.j < d.j ∧
            ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
              JustificationBirth p.E (certificateHeight p K) D d.j d.X) := by
  by_cases present : ∃ d ∈ (derive p K B).W, d.j = e.j ∧ d.X = e.X
  · obtain ⟨d, hd, hj, hX⟩ := present
    exact Or.inl ⟨d, hd, hj, hX,
      window_bit_retained p K hK A B hAB e d he hd hj.symm hX.symm⟩
  · by_cases covered : e.j ≤ (derive p K B).h_F ∧ FGBlock.Preceq e.X (derive p K B).F
    · exact Or.inr (Or.inl ⟨present, covered⟩)
    · have above := window_evicted_above_hF p K hK A B hAB e he present covered
      obtain ⟨P, s, r_s, x, rs, hAP, hPB, hp, hg⟩ := first_removal p K A B hAB e he present
      obtain ⟨d, hd, hj, hX⟩ := hp
      have stepAbove : (derive p K (.node P s r_s x rs)).h_F < d.j := by
        rw [hj]
        exact (window_hF_mono p K hK _ _ hPB).trans_lt above
      have stepGone : ¬ ∃ a ∈ (derive p K (.node P s r_s x rs)).W,
          a.j = d.j ∧ a.X = d.X := by simpa only [hj, hX] using hg
      have ev := window_evicted_has_K_newer p K hK P s r_s x rs d hd stepGone stepAbove
      rw [hj, hX] at ev
      exact Or.inr (Or.inr ⟨present, covered, above, P, s, r_s, x, rs, hAP, hPB,
        ⟨d, hd, hj, hX⟩, hg, ev⟩)

end AvailableChain.FGSA.Window
end
