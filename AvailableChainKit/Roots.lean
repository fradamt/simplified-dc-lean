module
public import AvailableChainStatements.Generic.Conditions

@[expose] public section

namespace AvailableChain.Framework.Kit

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} {n : Nat} {P : ProtocolSpec n} [DecidableEq V]

/-- Every run has injective roots: roots are computed from block content, and
`Block.root_injective` holds on the whole `Block` type. -/
theorem rootInjective_all (E : Env V) (I : Interface P) (rho : Run V P) :
    RootInjective E I rho :=
  fun _ _ _ _ h => Block.root_injective h

end AvailableChain.Framework.Kit
end
