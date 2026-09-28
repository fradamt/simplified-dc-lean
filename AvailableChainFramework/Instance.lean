module
public import AvailableChainFramework.Hooks
public import AvailableChainStatements.Generic.Interface

@[expose] public section

namespace AvailableChain.Framework

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A finite validator type, bundled so that claims can quantify over it. -/
structure Validators where
  V : Type
  dec : DecidableEq V
  fin : Fintype V

attribute [instance] Validators.dec Validators.fin

/-- A protocol instance (design §3): the protocol, its protocol parameters,
and its facets, bound once. Claim constants are not here; they belong to
certificates. Phase 0 carries the v1 `Interface` as the one field facet;
other facets are type classes over `Instance`. -/
structure Instance where
  n : Nat
  P : ProtocolSpec n
  /-- Every certified environment has this Δ. -/
  Δ : Time
  iface : Interface P
  hooks : HooksSound P

end AvailableChain.Framework

end
