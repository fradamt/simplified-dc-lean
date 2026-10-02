module
public import AvailableChainFGSA.Model.WindowViews

-- The fixtures and examples are local to this test module.
set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Window.ViewTests

open AvailableChain.SimplexFG

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

private def block : FGBlock (Fin 1) :=
  .node .genesis 1 0 [⟨0, .vote 1 genesisRoot false, none⟩]

example : heightView params block =
    KitFG.heightOf (SimplexFG.derive params.E params.cfg block) := rfl

example : headFields params 2 block = ⟨1, genesisRoot, 0⟩ := by decide +kernel

end AvailableChain.FGSA.Window.ViewTests
end
