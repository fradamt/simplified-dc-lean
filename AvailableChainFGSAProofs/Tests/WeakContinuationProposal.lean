module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Proposal

public section

/-! WC J3, plan §6.9; DC first proposal comparison prefix.
At s=u+2, the cutoff is u. No pending suffix result enters the maximum. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationProposal

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC J3, plan §6.9; DC first eligible proposal: its maximum is exactly the seed. -/
theorem firstEligibleMaximum (hi : WCInv p c E rho w iStar rho.events.length) :
    ∃ D, D = w.QStar ∧ Block.Preceq w.QStar D := by
  obtain ⟨D, hD, hQD, _⟩ := wc_historyMax hi ((w.u + 2) - 2)
  refine ⟨D, ?_, hQD⟩
  rcases hD with h | ⟨j, x, s, hresult, hs⟩
  · exact h
  · have hu := hresult.label
    simp only [Slot] at hu hs
    omega

/-- WC J3, plan §6.9; DC first HEAD batch: the seed supplies the previous-label read. -/
theorem firstEligibleHeads
    (hs : V2.D.ScheduleWellFormed E rho) (hdelta : E.Δ = p.Δ)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (hgate : SA.gateTime p.toParams (w.u + 2) ≤ rho.horizon) :
    ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y ((w.u + 2) - 1) w.QStar :=
  wc_history_previousHeads hs hdelta hseed hi (w.u + 2) w.QStar le_rfl hgate (Or.inl rfl)

/-- WC J3, plan §6.9; DC pivot contract: all path and walk fields are present. -/
theorem pivotContract [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframe : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCProposalPivotStatement p c E rho ΔF w iStar :=
  wc_proposalPivot ΔF w iStar hframe

end AvailableChain.FGSA.Run.Tests.WeakContinuationProposal
end
