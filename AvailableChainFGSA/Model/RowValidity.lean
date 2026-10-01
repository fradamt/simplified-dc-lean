module
public import AvailableChainFGSA.Model.RowStore

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

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

/-- [R6] A separate store obligation for activation. StoreBundle is unchanged. -/
def RowsValidStored (p : Params) (st : State p.n) : Prop :=
  ∀ o ∈ st.proposals, ∀ s b raw sup rows,
    o.decode = some (.block s b raw sup rows) →
    ∃ P, fgBlockOf st b.parent = some P ∧ rowsValidForParent p P b.slot rows = true

end AvailableChain.FGSA
end
