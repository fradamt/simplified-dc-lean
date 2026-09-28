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

end AvailableChain.FGSA
end
