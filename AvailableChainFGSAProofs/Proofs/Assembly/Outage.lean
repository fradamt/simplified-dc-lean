module
public import AvailableChainFGSAProofs.Proofs.Outage.Export -- shake: keep (Outage claim boundary)
public import AvailableChainFGSAProofs.Proofs.Clean.Export -- shake: keep (Clean supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (foundation supplier boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

-- The lead requires hsafe in this signature; the exact claim uses only hcut.
set_option linter.unusedVariables false in
/-- Blueprint 03 §4. The Clean claims supply the history projections.
Foundation Exports supply store, frame, and source discipline. -/
theorem fgsa_exactProposalClaim_of_clean
    (hcut : CleanCutClaim p) (hsafe : CleanSafetyClaim p) : ExactProposalClaim p := by
  clear hsafe
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
    (hcut : CleanCutClaim p) (hsafe : CleanSafetyClaim p) :
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
      exact (hsafe c E rho (ΔF := ΔF) pt hc).2.1)

/-- Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen inclusion claim. -/
theorem fgsa_cleanInclusionClaim_of_clean
    (hcut : CleanCutClaim p) (hsafe : CleanSafetyClaim p) : CleanInclusionClaim p := by
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
      exact (hsafe c E rho (ΔF := ΔF) pt hc).2.1)

end AvailableChain.FGSA.Run
end
