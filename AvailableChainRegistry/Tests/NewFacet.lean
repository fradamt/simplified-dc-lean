module
public import AvailableChainFramework

@[expose] public section

namespace AvailableChain.Registry.Tests

open AvailableChain AvailableChain.Generic AvailableChain.Framework

/-- A new facet: a third output. Adding it changes no existing declaration. -/
class HasStrong (I : Instance) where
  strong : I.P.State → Block

def safeStrong (I : Instance) [HasStrong I] : Prop :=
  ∀ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (t₀ : Time),
    Catalog.sleepy I W E rho t₀ →
    AvailableChain.Statements.Generic.SafeFrom I.P rho (HasStrong.strong (I := I)) t₀

end AvailableChain.Registry.Tests

end
