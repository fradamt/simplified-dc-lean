module
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch
public import AvailableChainFGSAProofs.Proofs.Outage.GoodVotes
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDeadlines
public import AvailableChainFGSAProofs.Proofs.Clean.Closure

public section

namespace AvailableChain.FGSA.Run.Tests.OutageServices

open AvailableChain.SimplexFG Gen.Pure

/-- The public receipt consumer needs no assumed restored service or NoRestart.
P-Ar supplies the separate healthy-prefix field. Receivers in W are included. -/
theorem restored_receipt_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hPrefix : OutagePrefixReceipt p c E rho fast T b₀) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ :=
  outage_continuation_receipt_of_prefix h hPrefix

/-- The actual opponent release bound consumes E's strict good-set count. -/
theorem good_release_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hBase : Base₂ p c E rho) (fast : Bool) (b₀ : Time) (r s : Slot) (B : Block)
    (i : Nat) (x : V)
    (hCount : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      (outageH p E rho s \ outageW p E rho fast b₀ r).card)
    (hheads : ∀ y ∈ outageH p E rho s \ outageW p E rho fast b₀ r,
      ∀ o t, V2.D.Run.emits E rho y o t →
      ∀ q K, o.auth = .seat (.base (.head s)) q →
        HeadTargetAtEmission p c E rho y o t K → Block.Compatible K B) :
    GridCO.releaseCount p.toParams.engine (actView (storeAt p c E rho i x)) s B <
      SA.releaseThreshold p.toParams :=
  (outage_good_release_bound E rho hBase.valid hBase.cstar hBase.idealization
    fast b₀ r s B i x hheads).trans_lt (outage_opponents_lt_release hBase hCount)

/-- A row expires at equality; a later row remains in the same model view. -/
theorem handover_expiry_equality :
    let st : GridCO.State 1 .root :=
      { GridCO.initial 1 .root with obligations := [(.genesis, 1, 25), (.genesis, 2, 26)] }
    (GridCO.expire { st with now := 25 } 25).obligations = [(.genesis, 2, 26)] := by
  rfl

/-- The real prefix producers close the pending seed without a pending-source input.
The result includes all honest actions, even actions by receivers in W. -/
theorem pending_seed_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {T b₀ ΔF : Time} (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF)
    (htsrc : TSrc p c E rho) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) :=
  outage_arming_sources_from_prefix h htsrc hc htransfer

/-- The checked P-Cl1 Clean history supplies the exact transfer projection.
This test derives the pending seed without a separate transfer or source premise. -/
theorem pending_seed_of_clean_history {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {T b₀ ΔF : Time} (h : CleanCutSet p c E rho b₀ ΔF)
    (hq : FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) := by
  have hTransfer := (cleanHistoryAt_body p c E rho h hq hf hsrc).2.2.1
  exact outage_arming_sources_from_prefix h htsrc hc
    (fun y z s C H hy hz hJ hcut hC hH => hTransfer y z s C H hy hz hcut hC hJ hH)

/-- The handover consumer uses actual gate origins in all receiver epochs.
It needs only the late-result projection of the joint invariant. -/
theorem handover_rows_consumer {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (r : Slot) (B : Block) {i : Nat} {x : V}
    (hi : rho.events[i]? = some (.tick x (OutageEnd p r)))
    (hResults : ∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
      gateResultAt p c E rho j = some (some C) → Block.Compatible C B) :
    ∀ row ∈ (storeAt p c E rho (i + 1) x).base.obligations, Block.Compatible row.1 B :=
  outage_handover_tick_rows hs r B hi hResults

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.restored_receipt_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.good_release_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.handover_expiry_equality
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.pending_seed_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.pending_seed_of_clean_history
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.handover_rows_consumer

end AvailableChain.FGSA.Run.Tests.OutageServices
end
