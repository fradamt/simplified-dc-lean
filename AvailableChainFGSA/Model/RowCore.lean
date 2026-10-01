module
public import AvailableChainFGSA.Model.Store

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [R7] All signed rows of admitted proposals, in stored order. -/
def allBlockRows {n : Nat} (st : State n) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ _ _ _ rows) => some rows
    | _ => none)).flatten

/-- [R6] The parent's post-state with the child's slot, before the row fold. -/
def parentFoldState (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    ChainState (Fin p.n) :=
  { derive p.E p.cfg P with s := s }

/-- [R6] Decode the row and check its height and entry. Finality is independent. -/
def rowValidFor {n : Nat} (σ : ChainState (Fin n)) (a : RowWire n) : Bool :=
  match a.toRow? with
  | some a => a.height_pair.matchesEntry σ.h σ.T_h.root
  | none => false

/-- [R6] Check every row against the same state before any row is folded. -/
def rowsValidForParent (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    (rows : List (RowWire p.n)) : Bool :=
  rows.all (rowValidFor (parentFoldState p s P))

/-- [R7] Select held rows with the supplied chain and parent lookup functions.
This core does not depend on Frame. -/
def proposalRowsCore (p : Params)
    (chainRows : State p.n → Block → List (RowWire p.n))
    (blockOf : State p.n → Block → Option (FGBlock (Fin p.n)))
    (blockRows : State p.n → List (RowWire p.n))
    (st : State p.n) (s : Slot) (H : Block) : List (RowWire p.n) :=
  match blockOf st H with
  | none => []
  | some P =>
      (st.rowPool ++ blockRows st).eraseDups.filter (fun a =>
        rowValidFor (parentFoldState p s P) a && !decide (a ∈ chainRows st H))

end AvailableChain.FGSA
end
