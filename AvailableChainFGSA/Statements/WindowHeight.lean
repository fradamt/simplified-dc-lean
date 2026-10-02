module
public import AvailableChainFGSA.Model.Window
public import AvailableChainKitFG.HeightCoreDef

@[expose] public section

namespace AvailableChain.FGSA.Window

/-- [bp.heightBridge.v1] The eight height fields, in `heightOf` order. -/
def projectHeight {V : Type} (σ : State V) : KitFG.FGHeight V :=
  ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩

theorem projectHeight_def {V : Type} (σ : State V) :
    projectHeight σ =
      ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩ := rfl

end AvailableChain.FGSA.Window
end
