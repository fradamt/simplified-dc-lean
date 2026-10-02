module
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Finality.CoreServices

public section

namespace AvailableChain.FGSA.Run

/-- Blueprint 01:126–129, plan item 18; lead ruling B30. DC: INTENTIONAL: AC service contract.
The Finality lane Export restores the frozen Claims conclusion from the composition
services; Recovery supplies Base₂. The other inputs are not used. -/
theorem fgsa_kernelACSide_W (p : Params) : KernelACSideClaim_W p := by
  intro _ _ _ _ _ _ _ c E rho w hr _ _
  exact fgsa_coreServices E rho hr.base w

end AvailableChain.FGSA.Run
end
