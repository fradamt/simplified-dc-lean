module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationPC
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank
public import AvailableChainKitFG.FrameSelection

public section

/-! Formation-to-source selector (pcsa34-r4.3a §5.7).
BLOCKED: Tests.FormationCounterexample checks FormationPrem at opening
rR = 4, with no ack or PC and fgSource = none at a_2 = 22.
Thus FormationSourceClaim fails on the same run as FormationClaim.
The selector below remains valid with explicit snapshot membership,
own-slot target identity, opening read, and unique active FG lift.
The source window uses snapshot label rR, not rR+1. -/

namespace AvailableChain.PCSA

private theorem formation_preferPC_slot {n : Nat} (old : Option (PC n)) (a C : PC n)
    (h : preferPC old a = some C) :
    a.slot ≤ C.slot ∧ ∀ B, old = some B → B.slot ≤ C.slot := by
  cases old with
  | none =>
    change some a = some C at h
    cases h
    exact ⟨le_refl _, by intro B hB; cases hB⟩
  | some B =>
    change (if pcBelow B a then some a else some B) = some C at h
    split at h
    · rename_i hlt
      cases h
      have hb : B.slot < a.slot ∨ B.slot = a.slot := by
        change ((_ || _) : Bool) = true at hlt
        rcases Bool.or_eq_true_iff.mp hlt with hs | hs
        · exact Or.inl (of_decide_eq_true hs)
        · exact Or.inr (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hs).1)
      refine ⟨le_refl _, ?_⟩
      intro D hD
      cases hD
      exact hb.elim Nat.le_of_lt le_of_eq
    · rename_i hlt
      have he : C = B := (Option.some.inj h).symm
      subst C
      have ha : a.slot ≤ B.slot := by
        by_contra hn
        have hs : B.slot < a.slot := Nat.lt_of_not_ge hn
        apply hlt
        change ((_ || _) : Bool) = true
        exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hs))
      exact ⟨ha, by intro D hD; cases hD; exact le_refl _⟩

private theorem formation_fold_top {n : Nat} (cs : List (PC n)) (old : Option (PC n))
    (s : Slot) (hOld : ∀ C, old = some C → C.slot ≤ s)
    (hCs : ∀ C ∈ cs, C.slot ≤ s)
    (hTop : (∃ C, old = some C ∧ C.slot = s) ∨ ∃ C ∈ cs, C.slot = s) :
    ∃ C, cs.foldl preferPC old = some C ∧ C.slot = s := by
  induction cs generalizing old with
  | nil =>
    rcases hTop with hTop | ⟨C, hC, _⟩
    · exact hTop
    · exact (List.not_mem_nil hC).elim
  | cons a cs ih =>
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (pcsa_preferPC_isSome old a)
    have hDs : D.slot ≤ s := by
      rcases pcsa_preferPC_eq_or old a D hD with hd | hd
      · exact hOld D hd
      · exact hd ▸ hCs a (List.mem_cons_self)
    have hge := formation_preferPC_slot old a D hD
    apply ih (preferPC old a) (fun C hC => by
      have he := Option.some.inj (hD.symm.trans hC)
      exact he ▸ hDs) (fun C hC => hCs C (List.mem_cons_of_mem _ hC))
    rcases hTop with ⟨C, hC, hs⟩ | ⟨C, hC, hs⟩
    · exact Or.inl ⟨D, hD, le_antisymm hDs (hs ▸ hge.2 C hC)⟩
    · rcases List.mem_cons.mp hC with he | hm
      · subst C
        exact Or.inl ⟨D, hD, le_antisymm hDs (hs ▸ hge.1)⟩
      · exact Or.inr ⟨C, hm, hs⟩

/-- A top-slot member makes the best PC choose that slot and its unique target. -/
theorem pcsa_formation_bestPC_target {n : Nat} (cs : List (PC n)) (s : Slot) (P : Block)
    (hBound : ∀ C ∈ cs, C.slot ≤ s) (hTop : ∃ C ∈ cs, C.slot = s)
    (hTarget : ∀ C ∈ cs, C.slot = s → C.target = P) :
    ∃ C, bestPC cs = some C ∧ C.slot = s ∧ C.target = P := by
  obtain ⟨C, hC, hs⟩ := formation_fold_top cs none s (by intro C hC; cases hC)
    hBound (Or.inr hTop)
  exact ⟨C, hC, hs, hTarget C (bestPC_mem cs C hC) hs⟩

/-- An active own-slot snapshot PC fixes the R8′ source at the opening. -/
theorem pcsa_formation_fgSource (p : Params) (st : State p.n) (r : Nat) (P : Block)
    (B : SimplexFG.FGBlock (Fin p.n))
    (hOpening : p.round (st.slot p) * p.R = r * p.R)
    (hPC : ∃ C ∈ pcSnapshotAt st (r * p.R), C.slot = r * p.R ∧ frameActive p st C = true)
    (hTarget : ∀ C ∈ pcSnapshotAt st (r * p.R), C.slot = r * p.R → C.target = P)
    (hB : B ∈ fullTree p st) (hErase : eraseFG B = P)
    (hUnique : ∀ A ∈ fullTree p st, eraseFG A = P → A = B) : fgSource p st = some B := by
  let candidates := (pcSnapshotAt st (r * p.R)).filter (fun C =>
    r * p.R < C.slot + p.R && C.slot ≤ r * p.R && frameActive p st C)
  have hBound : ∀ C ∈ candidates, C.slot ≤ r * p.R := by
    intro C hC
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (List.mem_filter.mp hC).2).1).2
  have hTop : ∃ C ∈ candidates, C.slot = r * p.R := by
    obtain ⟨C, hm, hs, ha⟩ := hPC
    refine ⟨C, List.mem_filter.mpr ⟨hm, ?_⟩, hs⟩
    have hR : 0 < p.R := lt_of_lt_of_le (by decide : 0 < 2) p.RLarge
    simp only [hs, ha, Bool.and_true]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (by omega), decide_eq_true (le_refl _)⟩
  obtain ⟨C, hC, _, ht⟩ := pcsa_formation_bestPC_target candidates (r * p.R) P hBound hTop
    (fun C hC hs => hTarget C (List.mem_filter.mp hC).1 hs)
  delta fgSource
  rw [hOpening]
  change (match bestPC candidates with
    | some C => SimplexFG.pickPair (fullTree p st) (fun A => decide (eraseFG A = C.target))
    | none => none) = some B
  rw [hC]
  change SimplexFG.pickPair (fullTree p st) (fun A => decide (eraseFG A = C.target)) = some B
  rw [ht]
  exact KitFG.pickPair_eq_of_unique _ _ B hB (decide_eq_true hErase)
    (fun A hA he => hUnique A hA (of_decide_eq_true he))

end AvailableChain.PCSA
end
