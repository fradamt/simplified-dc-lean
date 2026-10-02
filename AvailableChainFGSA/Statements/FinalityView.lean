module
public import AvailableChainFGSA.Model.WindowViews
public import AvailableChainKitFG.CertificateCoreDef

@[expose] public section

namespace AvailableChain.FGSA

/-- The active finality view is the old simplex view. J4 changes its body to the window view. -/
def finalityView (p : Params) : KitFG.FGFinalityView (Fin p.n) :=
  KitFG.simplexFinalityView p.E p.cfg

theorem finalityView_def (p : Params) :
    finalityView p = KitFG.simplexFinalityView p.E p.cfg := rfl

end AvailableChain.FGSA
end
