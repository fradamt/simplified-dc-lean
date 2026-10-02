module
public import AvailableChainFGSA.Proofs.WindowHeightBridge
public import AvailableChainFGSA.Statements.WindowCertificate
public import AvailableChainKitFG.FrameBridge
public import AvailableChainKitFG.ProvenanceCoreDef

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

variable (p : Params) (K : Nat)

/-- The window hOf read equals the old read on the same arguments. -/
theorem window_hOf_eq (hK : 2 ≤ K) (B : FGBlock (Fin p.n)) :
    (projectHeight (derive p K B)).h =
      hOf p.E p.cfg B :=
  (hOf_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) B).symm

/-- The window frontier read equals the old read on the same arguments. -/
theorem window_frontier_eq (hK : 2 ≤ K) (blocks : View (Fin p.n)) :
    frontierView (fun B => projectHeight (derive p K B)) blocks =
      frontier p.E p.cfg blocks :=
  (frontier_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) blocks).symm

/-- The window lexMax read equals the old read on the same arguments. -/
theorem window_lexMax_eq (hK : 2 ≤ K) (F : FGBlock (Fin p.n)) (blocks : View (Fin p.n)) :
    lexMaxView (fun B => projectHeight (derive p K B)) F blocks =
      lexMax p.E p.cfg F blocks :=
  (lexMax_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) F blocks).symm

/-- The window filteredFrom read equals the old read on the same arguments. -/
theorem window_filteredFrom_eq (hK : 2 ≤ K) (c : Controls (Fin p.n))
    (blocks : Finset (FGBlock (Fin p.n))) :
    filteredFromView (fun B => projectHeight (derive p K B)) c blocks =
      filteredFrom p.E p.cfg c blocks :=
  (filteredFrom_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) c blocks).symm

/-- The window storeControls read equals the old read on the same arguments. -/
theorem window_storeControls_eq (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n)) :
    storeControlsView (fun B => projectHeight (derive p K B)) st =
      storeControls p.E p.cfg st :=
  (storeControls_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) st).symm

/-- The window storeFrame read equals the old read on the same arguments. -/
theorem window_storeFrame_eq (hK : 2 ≤ K) (st : SimplexFG.Store (Fin p.n))
    (blocks : Finset (FGBlock (Fin p.n))) :
    storeFrameView (fun B => projectHeight (derive p K B)) st blocks =
      storeFrame p.E p.cfg st blocks :=
  (storeFrame_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) st blocks).symm

/-- The window fjControls read equals the old read on the same arguments. -/
theorem window_fjControls_eq (hK : 2 ≤ K) (F : FGBlock (Fin p.n)) (blocks : View (Fin p.n)) :
    fjControlsView (fun B => projectHeight (derive p K B)) F blocks =
      fjControls p.E p.cfg F blocks :=
  (fjControls_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) F blocks).symm

/-- The window fjFrame read equals the old read on the same arguments. -/
theorem window_fjFrame_eq (hK : 2 ≤ K) (F : FGBlock (Fin p.n)) (blocks : View (Fin p.n)) :
    fjFrameView (fun B => projectHeight (derive p K B)) F blocks =
      fjFrame p.E p.cfg F blocks :=
  (fjFrame_of_bridge p.E p.cfg _ (windowHeightBridge p K hK) F blocks).symm

/-- The direct window head fields equal the certificate head fields. -/
theorem headFields_eq_certificateHeadFields (Hd : FGBlock (Fin p.n)) :
    headFields p K Hd =
      certificateHeadFields (certificateHeight p K) (certificateFinality p K) Hd := rfl

end AvailableChain.FGSA.Window
end
