module
public import AvailableChainFGSA.Proofs.WindowRetention
public import AvailableChainFGSA.Statements.WindowEntries
public import AvailableChainFGSA.Statements.FinalityView

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

/-- Terminal scalar bounds at the active finality and height views preserve
the key. The supplier uses the bounds at each intermediate child. -/
theorem terminal_retained_scalarW (p : Params) (A P : FGBlock (Fin p.n))
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A y U) (above : (finalityView p P).h_F < y)
    (near : (heightView p P).h_j < y + p.K_W) : RetainedW p P y U := by
  obtain ⟨e, he, hej, heX⟩ := retained
  obtain ⟨d, hd, hdj, hdX, _⟩ := window_retained_of_scalar p p.K_W p.kWLarge
    A P hAP e he
    (by simpa only [finalityView_def, certificateFinality_def,
      projectFinality_def, hej] using above)
    (by simpa only [heightView_def, projectHeight_def, hej] using near)
  exact ⟨d, hd, hdj.trans hej, hdX.trans heX⟩

/-- Fewer than K newer births up to the terminal parent preserve the key.
The finite set can overestimate the births; certificate heights need no gap bound. -/
theorem terminal_retained_birthsW (p : Params) (A P : FGBlock (Fin p.n))
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A y U) (above : (finalityView p P).h_F < y)
    (births : Finset (FGBlock (Fin p.n))) (few : births.card < p.K_W)
    (cover : ∀ C j X, FGBlock.Preceq C P → y < j →
      JustificationBirth p.E (certificateHeight p p.K_W) C j X → C ∈ births) :
    RetainedW p P y U := by
  obtain ⟨e, he, hej, heX⟩ := retained
  obtain ⟨d, hd, hdj, hdX, _⟩ := window_retained_of_few_births p p.K_W p.kWLarge
    A P hAP e he
    (by simpa only [finalityView_def, certificateFinality_def,
      projectFinality_def, hej] using above)
    births few
    (by simpa only [hej] using cover)
  exact ⟨d, hd, hdj.trans hej, hdX.trans heX⟩

/-- A finality deletion covers the key. The same scalar bound also excludes
capacity eviction, without a premise that finality stays below the key. -/
theorem terminal_retained_or_coveredW (p : Params) (A P : FGBlock (Fin p.n))
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock (Fin p.n))
    (retained : RetainedW p A y U) (near : (heightView p P).h_j < y + p.K_W) :
    RetainedW p P y U ∨ CoveredW p P y U := by
  obtain ⟨e, he, hej, heX⟩ := retained
  have result := window_retained_or_covered p p.K_W p.kWLarge A P hAP e he
    (by simpa only [heightView_def, projectHeight_def, hej] using near)
  rw [hej, heX] at result
  rcases result with ⟨d, hd, hdj, hdX, _⟩ | covered
  · exact Or.inl ⟨d, hd, hdj, hdX⟩
  · exact Or.inr covered

/-- The paper causal cap permits at most one greater certificate height.
The active window's capacity and retained-or-covered supplier close F8-W. -/
theorem terminalRetentionW (p : Params) :
    ∀ (A P : FGBlock (Fin p.n)) (d : Nat) (U : FGBlock (Fin p.n))
      (q : Nat) (terminal : Time),
      FGBlock.Preceq A P → RetainedW p A (d + 1) U →
      ((heightView p A).h_j, (heightView p A).J) = (d + 1, U) →
      terminal < p.actionTime (q + 1) →
      (terminal < p.actionTime (q + 1) → (heightView p P).h ≤ d + 3) →
      RetainedW p P (d + 1) U ∨ CoveredW p P (d + 1) U := by
  intro A P d U q terminal ancestry retained latest noNext causal
  have cap := causal noNext
  have below := (windowHeightLaws p p.K_W p.kWLarge).justified_below_height P
  have latestHeight := congrArg Prod.fst latest
  simp only [heightView_def, projectHeight_def] at cap latestHeight
  change (Window.derive p p.K_W P).h_j < (Window.derive p p.K_W P).h at below
  have one : (Window.derive p p.K_W P).h_j ≤ (Window.derive p p.K_W A).h_j + 1 := by
    rw [latestHeight]
    exact Nat.le_of_lt_succ (below.trans_le cap)
  apply terminal_retained_or_coveredW p A P ancestry (d + 1) U retained
  simp only [heightView_def, projectHeight_def]
  rw [latestHeight] at one
  exact one.trans_lt (Nat.add_lt_add_left
    (Nat.lt_of_lt_of_le (by decide : 1 < 2) p.kWLarge) (d + 1))

end AvailableChain.FGSA.Window
end
