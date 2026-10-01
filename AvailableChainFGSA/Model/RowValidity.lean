module
public import AvailableChainFGSA.Model.RowStore
public import AvailableChainFGSA.Model.RowCore

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [R6] A separate store obligation for activation. StoreBundle is unchanged. -/
def RowsValidStored (p : Params) (st : State p.n) : Prop :=
  ∀ o ∈ st.proposals, ∀ s b raw sup rows,
    o.decode = some (.block s b raw sup rows) →
    ∃ P, fgBlockOf st b.parent = some P ∧ rowsValidForParent p P b.slot rows = true

end AvailableChain.FGSA
end
