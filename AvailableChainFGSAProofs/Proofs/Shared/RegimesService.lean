module
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService
public import AvailableChainFGSAClaims.Statements.Regimes

public section

namespace AvailableChain.FGSA.Run

open Gen.V2.Duty (faulty)
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
variable {ΔF : Time}

/-- Exact service on a Clean prefix uses joined participation and local gate receipts. -/
theorem exactService_of_head_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hcut : SA.gateTime p.toParams v ≤ b₀)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (faulty rho).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    h.base.cstar v Q hne hhead
    (fun _ => Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2)
    (fun _ => exactService_participation_of_card_joined E rho h.base.cstar v
      hbatch hfast) hgeometry hScopes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9 and blueprint 21 H.22 H3, conditional Recovery exact service.
DC: Generic/Conditions.lean:110–132; UserConfirmationRecovery.lean:235.
INTENTIONAL: post-GST waking and the one-third fault bound supply the SA
fast count. Cardinality uses only the fresh HEAD-seat bijection.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_of_head_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams v)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (faulty rho).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    h.base.cstar v Q hne hhead
    (fun hh => Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hh)
    (fun _ => exactService_participation_of_card_joined E rho h.base.cstar v
      hbatch hfast) hgeometry hScopes

end AvailableChain.FGSA.Run
end
