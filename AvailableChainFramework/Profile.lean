module
public import AvailableChainFramework.Cert

@[expose] public section

namespace AvailableChain.Framework

/-- A named set of catalog claims (design §4, profiles). -/
structure Profile where
  id : Lean.Name
  claims : List ClaimSpec

/-- One certificate per claim of the profile, all for one instance. Shared
constant names are Phase 1 (`ac-4.3` needs them).

`Type 1`, not `Type`: `ClaimSpec` carries `Type`-valued fields (`Const`,
`Point`), so `ClaimSpec : Type 1`, and quantifying over it lands one universe
higher (controller ruling 2026-09-28: plan defect, fix by widening the
ascription, change nothing else). -/
def ProfileCert (p : Profile) (I : Instance) : Type 1 :=
  ∀ c ∈ p.claims, Cert c I

end AvailableChain.Framework

end
