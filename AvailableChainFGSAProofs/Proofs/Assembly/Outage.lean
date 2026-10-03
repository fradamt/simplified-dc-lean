module
public import AvailableChainFGSAProofs.Proofs.Outage.Export -- shake: keep (Outage claim boundary)
public import AvailableChainFGSAProofs.Proofs.Clean.Export -- shake: keep (Clean supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (foundation supplier boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

/-- Blueprint 03 §4. The Clean claims supply the history projections.
Foundation Exports supply store, frame, and source discipline. -/
theorem fgsa_exactProposalClaim_of_clean
    (hcut : CleanCutClaim p) : ExactProposalClaim p := by
  exact outage_exactProposalClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.2.2.1)

/-- Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen post-gate inclusion claim. -/
theorem fgsa_cleanInclusionPostGateClaim_of_clean
    (hcut : CleanCutClaim p) :
    CleanInclusionPostGateClaim p := by
  exact outage_cleanInclusionPostGateClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.2.2.1)
    (hmono := by
      intro V _ _ In c E rho ΔF pt hc
      exact (cleanSafety_of_cut p hcut c E rho (ΔF := ΔF) pt hc).2.1)

/-- Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen inclusion claim. -/
theorem fgsa_cleanInclusionClaim_of_clean
    (hcut : CleanCutClaim p) : CleanInclusionClaim p := by
  exact outage_cleanInclusionClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.2.2.1)
    (hmono := by
      intro V _ _ In c E rho ΔF pt hc
      exact (cleanSafety_of_cut p hcut c E rho (ΔF := ΔF) pt hc).2.1)

/-- Blueprint 03 §5. The Clean claims supply history and monotonicity.
The Outage Export proves the frozen growth claim. -/
theorem fgsa_cleanGrowthClaim_of_clean
    (hcut : CleanCutClaim p) : CleanGrowthClaim p := by
  exact outage_cleanGrowthClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (hcut c E rho (ΔF := ΔF) pt hc).1.2.2.2.2.2.1)
    (hmono := by
      intro V _ _ In c E rho ΔF pt hc
      exact (cleanSafety_of_cut p hcut c E rho (ΔF := ΔF) pt hc).2.1)

/-- Blueprint 03 §9. Foundation Exports supply the source facts.
One Clean cut result supplies all nine Clean inputs at b₀. -/
theorem fgsa_outageCompatClaim_of_clean
    (hcut : CleanCutClaim p) : OutageCompatClaim p := by
  intro V _ _ In c E rho fast pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hs := fgsa_sourceDisciplineBaseClaim p c E rho () hb
  exact outage_compat_body_of_cut p
    (hstore := (fgsa_activeViewAt p c E rho).1)
    (hframe := (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (htsrc := hs.1) (hnamed := hs.2.2)
    (hcut := hcut c E rho (ΔF := ΔF) ⟨pt.b₀⟩ ⟨h.set.pre⟩) h

/-- Blueprint 03 §9.1. The fast claim uses the P1 part of the cut wrapper. -/
theorem fgsa_fastP1Claim_of_clean
    (hcut : CleanCutClaim p) : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hs := fgsa_sourceDisciplineBaseClaim p c E rho () hb
  exact (outage_compat_body_of_cut p
    (hstore := (fgsa_activeViewAt p c E rho).1)
    (hframe := (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (htsrc := hs.1) (hnamed := hs.2.2)
    (hcut := hcut c E rho (ΔF := ΔF) ⟨pt.b₀⟩ ⟨h.set.pre⟩) h).1

/-- Blueprint 03 §9.2. The slow claim also keeps the pending-gate lease clause. -/
theorem fgsa_slowP1Claim_of_clean
    (hcut : CleanCutClaim p) : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hs := fgsa_sourceDisciplineBaseClaim p c E rho () hb
  exact outage_compat_body_of_cut p
    (hstore := (fgsa_activeViewAt p c E rho).1)
    (hframe := (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (htsrc := hs.1) (hnamed := hs.2.2)
    (hcut := hcut c E rho (ΔF := ΔF) ⟨pt.b₀⟩ ⟨h.set.pre⟩) h

end AvailableChain.FGSA.Run
end
