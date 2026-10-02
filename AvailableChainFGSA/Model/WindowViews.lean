module
public import AvailableChainFGSA.Model.Window
public import AvailableChainKitFG.FrameBridgeDef

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

namespace Window

/-- [bp.heightBridge.v1] The eight height fields, in `heightOf` order. -/
def projectHeight {V : Type} (σ : State V) : KitFG.FGHeight V :=
  ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩

theorem projectHeight_def {V : Type} (σ : State V) :
    projectHeight σ =
      ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩ := rfl

/-- [spec 1186–1200] The window parent state with the child slot. -/
def parentState (p : Params) (K : Nat) (P : FGBlock (Fin p.n)) (s : Slot) :
    State (Fin p.n) :=
  { derive p K P with s := s }

theorem parentState_def (p : Params) (K : Nat) (P : FGBlock (Fin p.n)) (s : Slot) :
    parentState p K P s = { derive p K P with s := s } := rfl

/-- [spec 1603–1604] The head fields read directly from the window state. -/
def headFields (p : Params) (K : Nat) (Hd : FGBlock (Fin p.n)) : HeadFields :=
  ⟨(derive p K Hd).h_j, (derive p K Hd).J.root, (derive p K Hd).h_F⟩

theorem headFields_def (p : Params) (K : Nat) (Hd : FGBlock (Fin p.n)) :
    headFields p K Hd =
      ⟨(derive p K Hd).h_j, (derive p K Hd).J.root, (derive p K Hd).h_F⟩ := rfl

end Window

/-- The active height view still uses the old fold in FG5a.
J4 changes its body to `Window.projectHeight (Window.derive p p.K_W B)`. -/
def heightView (p : Params) (B : FGBlock (Fin p.n)) : FGHeight (Fin p.n) :=
  heightOf (SimplexFG.derive p.E p.cfg B)

theorem heightView_def (p : Params) (B : FGBlock (Fin p.n)) :
    heightView p B = heightOf (SimplexFG.derive p.E p.cfg B) := rfl

end AvailableChain.FGSA
end
