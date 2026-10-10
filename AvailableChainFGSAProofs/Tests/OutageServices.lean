module
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch
public import AvailableChainFGSAProofs.Proofs.Outage.GoodVotes
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming

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

#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.restored_receipt_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.good_release_consumer
#print axioms AvailableChain.FGSA.Run.Tests.OutageServices.handover_expiry_equality

end AvailableChain.FGSA.Run.Tests.OutageServices
end
