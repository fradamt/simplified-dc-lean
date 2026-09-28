module
public import AvailableChainFGSA.Statements.Invariants

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [bp comp.outputNesting.v2; K2] At every reachable state, `F ⪯ S`, and both
available accessors return S; for every `a`, without synchrony, including
empty and vetoed gates (spec 563–568). -/
def OutputNestingStored (p : Params) : Prop :=
  ∀ st, Reachable p st → NestOK st ∧ confirmed st = st.base.stableRecord ∧ stable st = confirmed st

/-- [bp bp.store.v1; K4 core] Every reachable state satisfies the composite invariant. -/
def StoreInvariant (p : Params) : Prop := ∀ st, Reachable p st → CStoreInv p st
/-- [bp bp.store.v1] Local F moves only to a descendant, at every step. -/
def FMonotone (p : Params) : Prop :=
  ∀ st : State p.n, (∀ o, FGBlock.Preceq st.fg.F (process p st o).fg.F) ∧
    (∀ t, (clock p st t).fg.F = st.fg.F)

end AvailableChain.FGSA
end
