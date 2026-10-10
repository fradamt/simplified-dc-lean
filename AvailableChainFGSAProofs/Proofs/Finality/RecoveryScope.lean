module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainFGSAClaims.Statements.Regimes

public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Recovery permits a wake at GST, but no later honest restart. -/
theorem finality_recovery_restart_bound {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {t : Time} (ht : V2.Event.restart x t ∈ rho.events) : t ≤ E.t_GST := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
  exact V2.D.Engine.noRestartAfter_of_awakeOnClosed h.base.valid.toScheduleWellFormed
    h.base.restartsAtWakes (fun u ha hb => h.awake x hx u ha hb) i t hi

/-- A receiver interval that starts after GST contains no local restart. -/
theorem finality_recovery_restartFree {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {i j : Nat} (hcut : ∀ k t, i ≤ k → k < j →
      rho.events[k]? = some (.restart x t) → E.t_GST < t) :
    V2.D.restartFree rho x i j := by
  intro k t hik hkj hk
  exact (not_lt_of_ge (finality_recovery_restart_bound p c E rho h hx
    (List.mem_of_getElem? hk))) (hcut k t hik hkj hk)

/-- The inclusive join cutoff, with the required receiver and time. -/
theorem finality_recovery_joined {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {s : Slot} {t : Time} (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hGST : E.t_GST ≤ t) (hhor : t ≤ rho.horizon) : joinedAt p E rho x s t := by
  refine ⟨h.awake x hx t hGST hhor, ?_, ?_⟩
  · intro u hu hut hw
    exact (finality_recovery_restart_bound p c E rho h hx
      (h.base.valid.wake_restart x hx u hu (hut.trans hhor) hw)).trans hcut
  · intro u _ _ hu
    exact (finality_recovery_restart_bound p c E rho h hx hu).trans hcut

end AvailableChain.FGSA.Run
end
