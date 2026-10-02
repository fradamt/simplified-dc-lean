module
public import AvailableChainFGSAClaims.Statements.Phases
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainKitFG.HeightConsumeTransfer
public import AvailableChainKitFG.HeightHistoryTransfer

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The active height bridge supplies the shared height laws. -/
private theorem kheight_laws (p : Params) : FGHeightLaws p.E (heightView p) :=
  heightLaws_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)

/-- Equal heights on the entry path keep the entry block. -/
private theorem kheight_entry (p : Params) {U P : FGBlock (Fin p.n)} {y : Nat}
    (hU : EntryAt p U y) (hUP : FGBlock.Preceq U P)
    (hP : (heightView p P).h = y) : (heightView p P).T_h = U :=
  ((kheight_laws p).entry_plateau hUP (hU.1.trans hP.symm)).symm.trans hU.2

/-- Target coverage writes the entry through the height bridge. -/
private theorem kheight_target (p : Params) {U X : FGBlock (Fin p.n)} {y : Nat}
    (hX : X ≠ .genesis) (hU : EntryAt p U y) (hUX : FGBlock.Preceq U X.parent)
    (hP : (heightView p X.parent).h = y) (hc : CoveredByChild p .target X U y) :
    JustifiedCross p X U y := by
  have hT := kheight_entry p hU hUX hP
  obtain ⟨S, hS, hc⟩ := hc
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s x rs =>
      change (heightView p P).h = y at hP
      change (heightView p P).T_h = U at hT
      obtain ⟨hh, hJ, hj⟩ := derive_target_of_cover_of_bridge p.E p.cfg
        (heightView p) (heightView_bridge p) P s x rs S hS (by
          simpa only [hP, hT] using
            (show ∀ i ∈ S, i ∈ (heightView p P).target_participation ∨
              ∃ a ∈ rs, a.signer = i ∧ a.height_pair = .vote y U.root false from hc))
      exact ⟨hP, hh.trans (congrArg (· + 1) hP), hJ.trans hT, hj.trans hP⟩

/-- Mature progress coverage advances through the height bridge. -/
private theorem kheight_progress (p : Params) {U X : FGBlock (Fin p.n)} {y : Nat}
    (hX : X ≠ .genesis) (hU : EntryAt p U y) (hUX : FGBlock.Preceq U X.parent)
    (hP : (heightView p X.parent).h = y) (hc : CoveredByChild p .progress X U y)
    (hm : U.slot + p.δt ≤ X.slot) : (heightView p X).h = y + 1 := by
  have hT := kheight_entry p hU hUX hP
  obtain ⟨S, hS, hc⟩ := hc
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s x rs =>
      change (heightView p P).h = y at hP
      change (heightView p P).T_h = U at hT
      have hh := derive_progress_of_cover_of_bridge p.E p.cfg
        (heightView p) (heightView_bridge p) P s x rs S hS (by
          intro i hi
          rcases hc i hi with hb | ⟨a, ha, hs, timeout, hp⟩
          · exact Or.inl hb
          · refine Or.inr ⟨a, ha, hs, ?_⟩
            rw [hp]
            change decide (y = (heightView p P).h ∧
              U.root = (heightView p P).T_h.root) = true
            simp only [hP, hT, and_self, decide_true, eq_self]) (by
          rw [hT]
          exact hm)
      exact hh.trans (congrArg (· + 1) hP)

/-- A crossing either writes this entry or keeps a lower justification. -/
private theorem kheight_cross_cases (p : Params) {U W : FGBlock (Fin p.n)} {y : Nat}
    (hU : EntryAt p U y) (hUW : FGBlock.Preceq U W.parent)
    (hP : (heightView p W.parent).h = y) (hW : (heightView p W).h = y + 1) :
    JustifiedCross p W U y ∨ MixedCross p W y := by
  have laws := kheight_laws p
  have hj := laws.justified_below_height W
  rw [hW] at hj
  by_cases heq : (heightView p W).h_j = y
  · left
    have hy : y ≠ 0 := by
      have := laws.one_le_h U
      rw [hU.1] at this
      simp only [Height] at *
      omega
    have jlaws := FGJustificationLaws.of_bridge (heightView_bridge p)
    have hJh := jlaws.J_height W (heq ▸ hy)
    rw [heq] at hJh
    have hJW := preceq_trans (laws.justified_preceq_entry W) (laws.entry_preceq W)
    have hPW : FGBlock.Preceq W.parent W := by
      cases W with
      | genesis => exact preceq_refl _
      | node P s x rs => exact preceq_parent_node P s x rs
    have hUW' := preceq_trans hUW hPW
    have hJ : (heightView p W).J = U := by
      rcases preceq_total_of_common hJW hUW' with hJU | hUJ
      · have ht := laws.entry_plateau hJU (hJh.trans hU.1.symm)
        rw [jlaws.J_entry W, hU.2] at ht
        exact ht
      · have ht := laws.entry_plateau hUJ (hU.1.trans hJh.symm)
        rw [hU.2, jlaws.J_entry W] at ht
        exact ht.symm
    exact ⟨hP, hW, hJ, heq⟩
  · right
    exact ⟨hP, hW, by simp only [Height] at *; omega⟩

/-- FINAL 22:710–737,1213–1223. The first target edge supplies the trichotomy.
DC: W4FKChainJustification.lean:185; FG-SA also names a mixed ancestor. -/
theorem fgsa_foldTrichotomy_target (p : Params) : foldTrichotomy p .target := by
  rw [foldTrichotomy_def]
  intro y U X hX hU hUX hc _hm
  have laws := kheight_laws p
  have hlow := laws.h_mono hUX
  rw [hU.1] at hlow
  by_cases hP : (heightView p X.parent).h = y
  · have hj := kheight_target p hX hU hUX hP (hc hP)
    exact ⟨by rw [hj.2.1], fun _ => Or.inl ⟨X, preceq_refl _, hj⟩⟩
  · have hhigh : y < (heightView p X.parent).h := by simp only [Height] at *; omega
    obtain ⟨W, _hne, hUW, hWP, hp, hw⟩ := first_height_crossing_edge_of_bridge
      p.E p.cfg (heightView p) (heightView_bridge p) y hUX hU.1 hhigh
    have hPX : FGBlock.Preceq X.parent X := by
      cases X with
      | genesis => exact (hX rfl).elim
      | node P s x rs => exact preceq_parent_node P s x rs
    have hmono := laws.h_mono hPX
    refine ⟨by simp only [Height] at *; omega, fun _ => ?_⟩
    rcases kheight_cross_cases p hU hUW hp hw with hj | hm
    · exact Or.inl ⟨W, preceq_trans hWP hPX, hj⟩
    · exact Or.inr ⟨W, hWP, hm⟩

/-- FINAL 22:710–737,1213–1223. Mature progress crosses or has already crossed.
DC: ProgressQuorumCore.lean:39; height monotonicity handles earlier crossings. -/
theorem fgsa_foldTrichotomy_progress (p : Params) : foldTrichotomy p .progress := by
  rw [foldTrichotomy_def]
  intro y U X hX hU hUX hc hm
  have laws := kheight_laws p
  have hlow := laws.h_mono hUX
  rw [hU.1] at hlow
  constructor
  · by_cases hP : (heightView p X.parent).h = y
    · rw [kheight_progress p hX hU hUX hP (hc hP) (hm rfl)]
    · have hPX : FGBlock.Preceq X.parent X := by
        cases X with
        | genesis => exact (hX rfl).elim
        | node P s x rs => exact preceq_parent_node P s x rs
      have := laws.h_mono hPX
      simp only [Height] at *
      omega
  · intro hk
    cases hk

/-- Increasing slots give a slot bound on every ancestor. -/
private theorem kheight_slot_le (p : Params) {W X : FGBlock (Fin p.n)}
    (hs : SlotChain X) (hWX : FGBlock.Preceq W X) : W.slot ≤ X.slot := by
  induction X with
  | genesis => obtain rfl := preceq_genesis.mp hWX; exact le_refl _
  | node P s x rs ih =>
      by_cases heq : W = .node P s x rs
      · subst W; exact le_refl _
      · have hWP := preceq_parent_of_preceq_node hWX heq
        have hslot := hs (.node P s x rs) (preceq_refl _) (by simp)
        have hp : SlotChain P := fun A hA hne =>
          hs A (preceq_node_of_preceq s x rs hA) hne
        exact le_trans (ih hp hWP) (Nat.le_of_lt hslot)

/-- FINAL 22:1213–1216. Every parent ancestor is strictly before maturity.
DC: CarrierTimeoutGate.lean:121; FG-SA takes the slot gate and slot order as premises. -/
theorem fgsa_noMixedMaturity (p : Params) : NoMixedMaturity p := by
  intro y U X hs hU hUX hearly W hWP hm
  have laws := kheight_laws p
  obtain ⟨hP, hW, hj⟩ := hm
  have hne : W ≠ .genesis := by
    intro heq
    subst W
    change (heightView p .genesis).h = y at hP
    rw [hP] at hW
    simp only [Height] at hW
    omega
  have hUW : FGBlock.Preceq U W := by
    rcases preceq_total_of_common hUX hWP with h | h
    · exact h
    · have hh := laws.h_mono h
      rw [hU.1, hW] at hh
      simp only [Height] at hh
      omega
  have hUWp : FGBlock.Preceq U W.parent := by
    cases W with
    | genesis => exact (hne rfl).elim
    | node D s x rs =>
        apply preceq_parent_of_preceq_node hUW
        intro heq
        rw [← heq, hU.1] at hW
        simp only [Height] at hW
        omega
  have hPX : X.parent.slot < X.slot := hs X (preceq_refl _) (by
    intro heq
    subst X
    obtain rfl := preceq_genesis.mp hWP
    exact hne rfl)
  have hslots := kheight_slot_le p (X := X.parent)
    (fun A hA hAne => hs A (preceq_trans hA (by
      cases X with
      | genesis => exact preceq_refl _
      | node D s x rs => exact preceq_parent_node D s x rs)) hAne) hWP
  have hwEarly : W.slot < U.slot + p.cfg.timeoutDelay := by
    change X.slot < U.slot + p.cfg.timeoutDelay + 1 at hearly
    simp only [Slot] at *
    omega
  have hjust := no_mixed_cross_before_maturity_of_bridge p.E p.cfg
    (heightView p) (heightView_bridge p) y hne hUWp hU.1 hU.2 hP hwEarly hW
  rw [hjust.2] at hj
  exact (Nat.lt_irrefl y hj)

/-- FINAL 22:1218–1223. No mixed predecessor leaves a justified first crossing.
DC: W4FKChainJustification.lean:185; FG-SA uses the explicit ancestor path. -/
theorem fgsa_justifyAt (p : Params) : JustifyAt p := by
  rw [JustifyAt_def]
  intro y U X hX hU hUX hc hn
  obtain ⟨_hh, hcross⟩ := fgsa_foldTrichotomy_target p y U X hX hU hUX hc
    (by intro hk; cases hk)
  rcases hcross rfl with hj | ⟨W, hWP, hm⟩
  · exact hj
  · exact (hn W hWP hm).elim

end AvailableChain.FGSA.Run
end
