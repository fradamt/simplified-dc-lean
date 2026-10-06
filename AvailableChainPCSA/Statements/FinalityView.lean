module
public import AvailableChainFGSA.Model.WindowViews
public import AvailableChainPCSA.Statements.WindowCertificate
public import AvailableChainKitFG.CertificateCoreDef

@[expose] public section

namespace AvailableChain.PCSA

/-- [PC-SA M1; FG-SA Statements/FinalityView.lean] The active finality view
reads the window certificate. -/
def finalityView (p : Params) : KitFG.FGFinalityView (Fin p.n) :=
  Window.certificateFinality p p.K_W

theorem finalityView_def (p : Params) :
    finalityView p = Window.certificateFinality p p.K_W := rfl

end AvailableChain.PCSA
end
