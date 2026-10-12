module
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- The actual reachable store supplies the root premise for the generic batch draft. -/
private theorem p0d7a3_reachable_root_leaf (p : Params) (st : State p.n)
    (hr : Reachable p st) : ViewRootInj st.fg.TF :=
  viewRootInj_TF p st (storeInvariant p st hr)

#print axioms p0d7a3_reachable_root_leaf

private def p0d7a3_lookup_parent : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def p0d7a3_lookup_opening : FGBlock (Fin 1) := .node p0d7a3_lookup_parent 2 ⟨2⟩ 0 []
private def p0d7a3_lookup_store : State 1 :=
  { initial 1 with fg := { (initial 1).fg with TF := {.genesis, p0d7a3_lookup_parent} } }

-- The actual lookup operations agree after exactly one parent step.
private theorem p0d7a3_parent_lookup_eq (st : State 1) (Q : Block) :
    parentFG st Q = fgBlockOf st Q.parent := rfl

-- Two non-genesis blocks expose both incorrect specializations.
-- This is a lookup fixture, not an ExecutionValid run.
private theorem p0d7a3_non_genesis_lookup :
    parentFG p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening) = some p0d7a3_lookup_parent ∧
    fgBlockOf p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening).parent =
      some p0d7a3_lookup_parent ∧
    fgBlockOf p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening) = none ∧
    parentFG p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening).parent =
      some .genesis := by
  decide

private theorem p0d7a3_carrier_lookup :
    (fun nd Q => fgBlockOf nd Q.parent) p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening) =
      some p0d7a3_lookup_parent := by decide

#print axioms p0d7a3_parent_lookup_eq
#print axioms p0d7a3_non_genesis_lookup
#print axioms p0d7a3_carrier_lookup

end AvailableChain.FGSA.Run
end
