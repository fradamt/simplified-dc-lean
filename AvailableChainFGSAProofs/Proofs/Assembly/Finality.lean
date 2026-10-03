module
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (L42 export boundary)

public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (B34 lane join)

public section

/-! Frozen Finality claims, exposed through the L42 assembly boundary (ruling B30). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Paper 22:1985–2009 (FT-Tail-W): close every tail supplier from Recovery₂
and HealingInput. DC: INTENTIONAL W Tail, with local receipt guards. -/
theorem fgsa_tailKernel_W (p : Params) : TailKernelClaim_W p := by
  apply fgsa_tailKernel_W_of p
  · intro V _ _ In c E rho G ΔF pt hT
    exact held_chain_row_origin_before p c E rho
      hT.set.base.valid.toUnforgeableSignatures hT.set.base.valid.toScheduleWellFormed
  · intro V _ _ In c E rho G ΔF pt hT
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF pt hT
    have hqc := sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hT.set.base, hT.set.faultQ⟩ (fgsa_rStore p c E rho)
    have hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
          e = ((heightView p C).h, (heightView p C).T_h.root) := by
      intro j x r a e ha he
      have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hT.set.base⟩
      obtain ⟨e', C, _, hn, hsrc, hentry, _, _⟩ := hb.2.2 j x r a ha
      exact ⟨C, hsrc, (Option.some.inj (he.symm.trans hn)).trans hentry⟩
    exact high_target_row_covered p c E rho pt.w hT.input.t.h1 hqc hnames
      hT.set.base.linked hT.set.base.valid.toScheduleWellFormed
  · intro V _ _ In c E rho G ΔF pt hT
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hT.set.base, hT.set.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF pt hT hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF pt hT
    have hs := sourceDiscipline_strat p c E rho
      (pt := pt) ⟨hT.set.base, hT.set.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF pt hT j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hT.set.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF pt hT cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hT.set.base.linked hT.set.base.valid
        hT.set.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hT.set.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)
  · intro V _ _ In c E rho G ΔF pt hT
    exact fgsa_rMono p c E rho
  · intro V _ _ In c E rho G ΔF pt hT
    exact fgsa_apiFinalLockClaim_body p c E rho () ⟨hT.set.base, hT.set.fault⟩

end AvailableChain.FGSA.Run
end
