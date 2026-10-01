module
public import AvailableChainFGSA.Model.RowStore
public import AvailableChainFGSA.Model.RowValidity

@[expose] public section

namespace AvailableChain.FGSA

/-- [R7] Keep the first copy of each held row, then apply R6 and exact chain
exclusion. The pool precedes the admitted-block rows. There is no row limit. -/
def proposalRowsFor (p : Params) (st : State p.n) (s : Slot) (H : Block) :
    List (RowWire p.n) :=
  match fgBlockOf st H with
  | none => []
  | some P =>
      (st.rowPool ++ allBlockRows st).eraseDups.filter (fun a =>
        rowValidFor (parentFoldState p s P) a && !decide (a ∈ chainWireRows st H))

end AvailableChain.FGSA
end
