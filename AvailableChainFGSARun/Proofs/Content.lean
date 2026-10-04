module
public import AvailableChainFGSARun.Proofs.Roots
public import AvailableChainFGSA.Proofs.CrossNode

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2. Scoped bodies and checked content give the two equalities. -/
theorem contentAgree_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (v w : V) (i j : Nat) :
    ContentAgree (V2.D.Run.stateBefore E rho i v).st (V2.D.Run.stateBefore E rho j w).st := by
  intro s b raw sup rows ho s' b' raw' sup' rows' ho' he
  have check := (metaInv_stateBefore E rho i v).wireTree _ ho
  have check' := (metaInv_stateBefore E rho j w).wireTree _ ho'
  obtain ⟨_, _, _, _, _, eq, hc, _⟩ := check
  obtain ⟨_, _, _, _, _, eq', hc', _⟩ := check'
  cases eq
  cases eq'
  exact stored_content_eq E rho hr
    (rootBlockInRun_stored_proposal E rho i v ho)
    (rootBlockInRun_stored_proposal E rho j w ho') hc hc' he

end AvailableChain.FGSA.Run
