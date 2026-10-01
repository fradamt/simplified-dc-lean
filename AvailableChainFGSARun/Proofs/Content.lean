module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSA.Proofs.CrossNode

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Any two indexed run stores agree on content; no schedule premise. -/
theorem contentAgree_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (v w : V) (i j : Nat) :
    ContentAgree (V2.D.Run.stateBefore E rho i v).st (V2.D.Run.stateBefore E rho j w).st := by
  exact contentAgree_reachable p
    (reachable_stateBefore E rho i v) (reachable_stateBefore E rho j w)

end AvailableChain.FGSA.Run
