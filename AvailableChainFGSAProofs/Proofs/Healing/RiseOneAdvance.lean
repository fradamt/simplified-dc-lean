module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAdvance
public import AvailableChainFGSAProofs.Proofs.Healing.SupportPerm

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1385–1410, 1467–1468; S5 M5b B1.
DC: SAME apply r3 at height one to the actual later proposal.
Assembly supplies the exact r3 INLINE ports. Healing supplies TPerm from
RMono, RXing and the existing last-write port. -/
theorem healing_rise_one_advance (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (hServices : SupportPermanenceServices E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {u : Time} {r : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r 1) (hcovered : OpeningCovered p c E rho r Q)
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) 1
      (some .genesis) false)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s) :
    2 ≤ (heightView p X).h := by
  exact healing_promotion_advance E rho hrec.toRecovery₂ hδ hbound
    (healing_tPerm E rho hrec mono crossing hServices writes) rowsReceipt progressCoverage
    hfold faultQ honestQuorum hentry hcovered hgst hphase hu hs hnew hslot

end AvailableChain.FGSA.Run
end
