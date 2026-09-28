module
public import AvailableChainFramework
public import AvailableChainWitnesses.Sanity

@[expose] public section

namespace AvailableChain.Registry.Sanity

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Witnesses.Sanity

theorem hooks : HooksSound (alwaysGenesis 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro st o _; rfl
  · intro V _ _ E rho _ v o i j _ _; rfl
  · intro V _ _ E rho _ v o i j _ h; exact h
  · intro st o o' h; exact Or.inl h

end AvailableChain.Registry.Sanity

end
