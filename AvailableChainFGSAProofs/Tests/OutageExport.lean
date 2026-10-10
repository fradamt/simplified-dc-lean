module
public import AvailableChainFGSAProofs.Proofs.Assembly.OutagePublicInputs

public section

namespace AvailableChain.FGSA.Run.Tests.OutageExport

variable (p : Params)

/-- The actual finite Clean and foundation suppliers close the unchanged outage claim. -/
theorem compat_of_sleep_cut : OutageCompatClaim p := outage_public_suppliers p

/-- The fast projection uses the same public confirmed-reader and duty scopes. -/
example : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact (compat_of_sleep_cut p c E rho true pt ΔF h).1

/-- The slow projection keeps its covered-receiver lease guarantee. -/
example : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact compat_of_sleep_cut p c E rho false pt ΔF h

#print axioms compat_of_sleep_cut

end AvailableChain.FGSA.Run.Tests.OutageExport
end
