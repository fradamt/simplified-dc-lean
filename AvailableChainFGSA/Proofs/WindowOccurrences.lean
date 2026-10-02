module
public import AvailableChainFGSA.Proofs.WindowRetention
public import AvailableChainFGSA.Statements.WindowEntries
public import AvailableChainFGSA.Model.WindowViews

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

/-- Exact finality rows add bits at the active parent view. Either R6W arm
has this effect; no height-match premise is required. -/
theorem entry_bit_insertW (p : Params) (P : FGBlock (Fin p.n))
    (s : Slot) (x : Nat) (rs : List (Row (Fin p.n))) (j : Height)
    (U : FGBlock (Fin p.n)) (hp : RetainedW p P j U)
    (hc : RetainedW p (.node P s x rs) j U)
    (a : Row (Fin p.n)) (ha : a ∈ rs)
    (matchRow : a.finality_pair = some ⟨j, U.root⟩) :
    EntryBitW p (.node P s x rs) j U a.signer := by
  obtain ⟨e, he, hej, heX⟩ := hp
  obtain ⟨d, hd, hdj, hdX⟩ := hc
  exact ⟨d, hd, hdj, hdX, window_bit_add_of_row p p.K_W p.kWLarge
    P s x rs e d he hd (hdj.trans hej.symm) (hdX.trans heX.symm) a ha
    (by simpa only [hej, heX] using matchRow)⟩

/-- Retention of the exact key preserves its bits at the active model view. -/
theorem entry_bit_persistW (p : Params) (A B : FGBlock (Fin p.n))
    (hAB : FGBlock.Preceq A B) (j : Height) (U : FGBlock (Fin p.n)) (i : Fin p.n)
    (bit : EntryBitW p A j U i) (retained : RetainedW p B j U) :
    EntryBitW p B j U i := by
  obtain ⟨e, he, hej, heX, hi⟩ := bit
  obtain ⟨d, hd, hdj, hdX⟩ := retained
  exact ⟨d, hd, hdj, hdX, window_bit_retained p p.K_W p.kWLarge
    A B hAB e d he hd (hej.trans hdj.symm) (heX.trans hdX.symm) hi⟩

/-- An occurrence strictly after a retained anchor contributes its bit when
the exact key is still retained at the endpoint. -/
theorem entry_bit_occurrenceW (p : Params) (A B C : FGBlock (Fin p.n))
    (hAC : FGBlock.Preceq A C) (hAB : StrictPrefix A B) (hBC : FGBlock.Preceq B C)
    (j : Height) (U : FGBlock (Fin p.n)) (ha : RetainedW p A j U)
    (hc : RetainedW p C j U) (a : Row (Fin p.n)) (hr : a ∈ B.rows)
    (matchRow : a.finality_pair = some ⟨j, U.root⟩) : EntryBitW p C j U a.signer := by
  obtain ⟨e, he, hej, heX⟩ := ha
  obtain ⟨d, hd, hdj, hdX⟩ := hc
  exact ⟨d, hd, hdj, hdX, (window_bits_accumulate p p.K_W p.kWLarge
    A C hAC e d he hd (hdj.trans hej.symm) (hdX.trans heX.symm)).2 B hAB hBC a hr
    (by simpa only [hej, heX] using matchRow)⟩

/-- The model history keeps all three cases. Eviction has an actual removal
step with K newer entries. A later endpoint can instead cover an evicted key. -/
theorem entry_historyW (p : Params) (A B : FGBlock (Fin p.n))
    (hAB : FGBlock.Preceq A B) (j : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A j U) :
    RetainedW p B j U ∨
    (¬ RetainedW p B j U ∧ CoveredW p B j U) ∨
    (¬ RetainedW p B j U ∧ ¬ CoveredW p B j U ∧
      (derive p p.K_W B).h_F < j ∧
      ∃ P s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s x rs) B ∧
        RetainedW p P j U ∧ ¬ RetainedW p (.node P s x rs) j U ∧
        (derive p p.K_W (.node P s x rs)).W.length = p.K_W ∧
        ∃ C, FGBlock.Preceq C P ∧
          JustificationBirth p.E (certificateHeight p p.K_W) C j U ∧
          ∀ d ∈ (derive p p.K_W (.node P s x rs)).W, j < d.j ∧
            ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s x rs) ∧
              JustificationBirth p.E (certificateHeight p p.K_W) D d.j d.X) := by
  obtain ⟨e, he, hej, heX⟩ := retained
  have history := window_entry_history p p.K_W p.kWLarge A B hAB e he
  rw [hej, heX] at history
  rcases history with ⟨d, hd, hj, hX, _⟩ | covered | evicted
  · exact Or.inl ⟨d, hd, hj, hX⟩
  · exact Or.inr (Or.inl covered)
  · exact Or.inr (Or.inr evicted)

end AvailableChain.FGSA.Window
end
