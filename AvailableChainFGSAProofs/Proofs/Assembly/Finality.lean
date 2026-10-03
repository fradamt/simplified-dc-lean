module
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (L42 export boundary)

public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (B34 lane join)

public section

/-! Frozen Finality claims, exposed through the L42 assembly boundary (ruling B30). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1171–1305 (F1–F9), lead ruling B34: close the W kernel suppliers.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention, exact signed
rows and actual receipt guards. Recovery₂ supplies every Foundations premise. -/
theorem fgsa_finalityKernel_W (p : Params) : FinalityKernelClaim_W p := by
  apply fgsa_finalityKernel_W_of p
  · intro V _ _ In c E rho hv
    exact fgsa_tRowsSelect p c E rho hv
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed
  · intro ΔF
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF pt hK
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF pt hK
    exact fgsa_rXing p c E rho hK.set.base.linked
      hK.set.faultX_count_rec hK.set.base.valid.toUnforgeableSignatures
  · intro V _ _ In c E rho G ΔF pt _ hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF pt hK
    have hs := sourceDiscipline_strat p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF pt hK j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hK.set.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF pt hK cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hK.set.base.linked hK.set.base.valid
        hK.set.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hK.set.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

/-- Paper 00:1119–1134, 22:1171–1305; plan §4: close the joined W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention and receipt.
Recovery₂ in the joined premise supplies every Foundations premise. -/
theorem fgsa_finalityKernelJoined_W (p : Params) : FinalityKernelJoinedClaim_W p := by
  apply fgsa_finalityKernelJoined_W_of p
  · intro V _ _ In c E rho hv
    exact fgsa_tRowsSelect p c E rho hv
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed
  · intro ΔF
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF pt hK
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF pt hK
    exact fgsa_rXing p c E rho hK.set.base.linked
      hK.set.faultX_count_rec hK.set.base.valid.toUnforgeableSignatures
  · intro V _ _ In c E rho G ΔF pt _ hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF pt hK
    have hs := sourceDiscipline_strat p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF pt hK j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hK.set.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF pt hK cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hK.set.base.linked hK.set.base.valid
        hK.set.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hK.set.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

end AvailableChain.FGSA.Run
end
