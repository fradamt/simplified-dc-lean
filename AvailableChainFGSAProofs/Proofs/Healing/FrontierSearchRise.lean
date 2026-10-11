module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTail
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne

public section

/-! Blueprint 21 HG.4:1695–1720; S5 F2.
The saved entry and first opening give the frozen rise guard.
INLINE writes and rowCoverage are the same inputs as healing_frontierTail_row. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1695–1720; S5 F2, saved-seed rise tail.
DC: SAME use capped HG.2a_F with the actual saved entry and first opening.
No phase after the saved gate or horizon beyond the frozen rise guard is assumed. -/
theorem healing_frontierTail_rise_of_seed [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) (frontier : TFrontier p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {t : Time}
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hserved : StrongServed p c E rho m t)
    (hhor : t + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m (t + (2 * P p + Γ p G - 9 * p.Δ)) := by
  classical
  obtain ⟨u, J, contested, q, Q, Qfg, hgst, hQ, he, hQm, hexact,
    hseed, hu, hp, hqt, hth, _⟩ := (strongServed_iff p c E rho m t).mp hserved
  have hex : ∃ r, q ≤ r * p.R := ⟨q, by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
      (show 1 ≤ p.R by have := p.RLarge; omega)⟩
  let r := Nat.find hex
  have hqr : q ≤ r * p.R := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨_, har⟩ := common_first_time_bound (p := p) q r hqr hfirst
  have ha : p.actionTime r ≤ t + P p - 4 * p.Δ := by linarith
  let U := (heightView p Qfg).T_h
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨iq, W, _, hW, hWe⟩ := healing_rise_one_gate_copy p c E rho hs hexact
    (hqt.trans hth) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 ((by
      have := healing_recovery_start_lower (p := p) E
      linarith [p.deltaPos] : E.t_GST ≤ u).trans hu) (hqt.trans hth))
  have hWQ : W = Qfg := eraseFG_injective (hWe.trans he.symm)
  subst W
  have hQbase : Q ∈
      (rho.stateBefore E iq (V2.D.proposerOf rho (fgsaInterface p c) q)).st.base.blocks :=
    (cstoreInv_stateBefore E rho iq _).baseTree Q |>.mpr ⟨Qfg, hW, he⟩
  have hUslot : U.slot ≤ q := by
    have ht := repair_stored_slot_le E rho hrec.base.valid iq _ Q hQbase (eraseFG U)
      (he ▸ eraseFG_preceq ((fgCertificateLaws p).height.entry_preceq Qfg))
    rw [eraseFG_slot, repair_proposal_slot E rho hQ] at ht
    exact ht
  have hUage : SA.proposalTime p.toParams U.slot ≤ t - 6 * p.Δ := by
    have hc : (U.slot : Time) ≤ q := by exact_mod_cast hUslot
    change SA.proposalTime p.toParams q + 6 * p.Δ ≤ t at hqt
    change 4 * p.Δ * (U.slot : Time) ≤ t - 6 * p.Δ
    change 4 * p.Δ * (q : Time) + 6 * p.Δ ≤ t at hqt
    nlinarith [p.deltaPos]
  have hD := frontierSearch_hg2a_bound p G ΔF t (p.actionTime r)
    (SA.proposalTime p.toParams U.slot) hbound ha hUage
  have hresult := frontier_hg2a_receipt E rho hrec hδ hbound mono crossing frontier
    rowsReceipt progressCoverage hfold faultQ honestQuorum hgst hQ he hQm hexact hseed
    hu hp hqr (show U = (heightView p Qfg).T_h from rfl) hstart (hD.trans hhor)
  rcases (frontierHG2aResult_iff E rho G ΔF i m r U).mp hresult with
      hrise | ⟨s, X, _, _, hh, y, hy, hheld⟩
  · exact frontierSearch_rise_mono p c E rho hD hrise
  · exact frontierSearch_rise_of_receipt p c E rho hs mono hstart
      hy hh hheld hD

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1695–1720; S5 F2, HG.4 rise.
DC: SAME use capped HG.2a_F with the actual saved entry and first opening.
No phase after the saved gate or horizon beyond the frozen rise guard is assumed. -/
theorem healing_frontierTail_rise [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) (frontier : TFrontier p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hserved : StrongServed p c E rho m ev.time)
    (hhor : ev.time + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m (ev.time + (2 * P p + Γ p G - 9 * p.Δ)) := by
  have hf := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.1
  exact healing_frontierTail_rise_of_seed E rho hrec hδ hbound mono crossing
    frontier
    rowsReceipt progressCoverage hfold faultQ honestQuorum hf.le hserved hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1695–1720; S5 F2, full HG.4.
DC: SAME combine the capped rise and run-1 exact-height row under their separate guards. -/
theorem healing_frontierTail [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    : FrontierTailStatement p c E rho G ΔF := by
  apply (frontierTailStatement_iff p c E rho G ΔF).mpr
  intro hδ hbound i ev m kind hstart hserved
  exact ⟨fun hhor => healing_frontierTail_rise E rho hrec hδ hbound mono crossing
      (frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage)
      rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hserved hhor,
    fun hhor => healing_frontierTail_row E rho hrec mono crossing cap scopeProducer writes
      rowCoverage
      hserved hhor⟩

end AvailableChain.FGSA.Run
end
