module
public import AvailableChainFGSARun.Proofs.Readiness
public import AvailableChainGeneric.Proofs.V2.Receipt

public section

namespace AvailableChain.FGSA.Run.Tests

open AvailableChain.SimplexFG

/-- The proposal producer is passed directly to the frozen generic receipt boundary. -/
theorem fgsa_parentStored_receipt_test
    {p : Params} {In : Type} {c : AppCodec In} {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    {Timely : (fgsa p c).State → (fgsa p c).Object → Prop}
    {Inv : (fgsa p c).State → Prop}
    (dl : Time → Time) (cut : Time) (o : Obj p) (t : Time) (w : V)
    {s : Slot} {b : Block} {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hBlock : (toWire p o).decode = some (.block s b raw sup rows))
    (hWF : ∀ i t', i < V2.Run.idxBefore rho (dl t) → V2.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true)
    (hParent : ∀ i t', i < V2.Run.idxBefore rho (dl t) →
      V2.Run.handlesAt E rho i w o t' →
      (parentFG (V2.Run.stateBefore E rho i w).st b).isSome = true)
    (hD : Gen.V2.DeliveryWithin E rho dl cut)
    (hT : Gen.V2.Trigger E rho o t)
    (hw : w ∈ rho.honest) (hcut : dl t ≤ cut) (hlt : t < dl t)
    (hS : V2.ScheduleWellFormed E rho)
    (hES : ∀ v o i j, i ≤ j → V2.restartFree rho v i j →
      (fgsa p c).excludes (V2.Run.stateBefore E rho i v) o = true →
      (fgsa p c).excludes (V2.Run.stateBefore E rho j v) o = true)
    (hPS : ∀ v o i j, i ≤ j → V2.restartFree rho v i j →
      (fgsa p c).processed (V2.Run.stateBefore E rho i v) o = true →
      (fgsa p c).processed (V2.Run.stateBefore E rho j v) o = true)
    (hA : Gen.V2.AcceptanceLaw (fgsa p c) Timely Inv)
    (C : Gen.V2.TimelyClock (fgsa p c) Timely)
    (hInv : ∀ i, Inv (V2.Run.stateBefore E rho i w))
    (hAdm : C.actTime o ≤ Gen.V2.pubFloor E t)
    (j : Nat) (hj : rho.events[j]? = some (.tick w (Gen.V2.pubFloor E t)))
    (hrf : V2.restartFree rho w j (V2.Run.idxBefore rho (dl t)))
    (hNX : (fgsa p c).excludes (V2.Run.stateBeforeTime E rho (dl t) w) o = false) :
    (fgsa p c).processed (V2.Run.stateBeforeTime E rho (dl t) w) o = true :=
  Gen.V2.accepted_by_deadline (P := fgsa p c) E rho dl cut o t w hD hT hw hcut hlt
    hS hES hPS (hReady := fgsa_hReady_of_parentStored hBlock hWF hParent)
    hA C hInv hAdm j hj hrf hNX

end AvailableChain.FGSA.Run.Tests
end
