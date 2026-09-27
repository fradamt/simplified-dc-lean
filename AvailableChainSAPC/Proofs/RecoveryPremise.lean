module
public import AvailableChainSAPC.Proofs.Basic

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The unchanged Recovery regime derives the cap from its declared
constants. The base bundle needs no additional fault-bound premise. -/
theorem recovery_faultBound {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) (rho : Run V (sapc p))
    (hG : 0 < G)
    (hr : RecoveryRegime (sapc p) E (sapcInterface p).toInterface
      (sapcConstants p G) rho) : FaultBound (sapc p) (pcFaultCap p) rho := by
  have hbound := (sapcConstants_valid p G hG).recoveryBound_nonneg
  have htime : E.t_GST ≤ rho.horizon := by linarith [hr.horizon]
  have hfull := hr.full rfl
  have hawake : awakeAt E rho.honest E.t_GST = rho.honest := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact hfull v hv E.t_GST (le_refl _) htime
  have hcount := hr.participation E.t_GST (le_refl _) htime
  rw [hawake] at hcount
  have htotal : rho.honest.card + (faulty rho).card = p.n := by
    have hc : Fintype.card V = p.n := by
      simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
    dsimp [faulty]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have := Finset.card_le_univ rho.honest
    omega
  exact recovery_count_implies_cap p _ _ htotal hcount

end AvailableChain.SAPC
end
