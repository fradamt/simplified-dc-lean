module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Replay
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Statements.WeakContinuation

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Local store replay uses the completed-gate index of each run. -/
theorem wcg_cut_storeReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    storeAt p c E' rho (afterTicksIdx rho t) x =
      storeAt p c E source (afterTicksIdx source t) x := by
  have he := wcg_afterTicksReplay ha x hx ht
  rw [afterTicks_eq_stateBefore E' rho hr, afterTicks_eq_stateBefore E source hs] at he
  exact congrArg (fun st => st.st) he

/-- Retained validators keep the seed's state fields at their own cut.
Historical origin fields of WCSeed require separate index and quorum proofs. -/
theorem wcg_seed_state (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hsource : V2.D.ScheduleWellFormed E source)
    (hrho : V2.D.ScheduleWellFormed E' rho) {w : HealingWitness} {iSource : Nat}
    (hs : WCSeed p c E source w iSource)
    (hend : SA.gateTime p.toParams w.u ≤ source.horizon) :
    let iRho := afterTicksIdx rho (SA.gateTime p.toParams w.u)
    ∀ x ∈ rho.honest,
      S_at p c E' rho iRho x = w.QStar ∧
      w.M + 1 ≤ (storeAt p c E' rho iRho x).fg.h_max ∧
      Block.Preceq (F_at p c E' rho iRho x) w.QStar ∧
      ∀ row ∈ (storeAt p c E' rho iRho x).base.obligations,
        (storeAt p c E' rho iRho x).base.now < row.2.2 → Block.Preceq row.1 w.QStar := by
  intro iRho x hx
  have he : storeAt p c E' rho iRho x = storeAt p c E source iSource x := by
    rw [hs.cut]
    exact wcg_cut_storeReplay ha hsource hrho x hx hend
  have hm := ha.honest hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (storeAt p c E' rho iRho x).base.stableRecord = w.QStar
    rw [he]
    exact hs.refreshed x hm
  · rw [he]
    exact hs.height x hm
  · change Block.Preceq (eraseFG (storeAt p c E' rho iRho x).fg.F) w.QStar
    rw [he]
    exact hs.finalBelow x hm
  · rw [he]
    exact hs.liveTargets x hm

end AvailableChain.FGSA.Run
end
