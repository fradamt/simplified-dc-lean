module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAge
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchStop

public section

/-! Blueprint 21 HG.2a_F:1592--1640 and HG.4:1695--1720; HG4-RISE F1.
The result contract stops at a rise. Same-frontier events do not stop it.
The gap adapter reuses the existing slot producer. S5 H2 proves the
height and strict receipt fields from the saved rows and frontier cap.
HG.1 source preservation: `frontier_service` (FrontierService:307).
No fixed phase after the saved gate is assumed by the result contract. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 21:1592--1640; HG4-RISE F1.
DC: SAME the saved entry's terminal result: a first rise or a strict honest
high receipt. The producer is frontier_hg2a_receipt. -/
def FrontierHG2aResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin p.n)) : Prop :=
  let D := max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
    (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ)
  FrontierRiseBy p c E rho i m D ∨
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      m + 1 ≤ (heightView p X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) D y

/-- Blueprint 21:1592–1640; S5 F2.
DC: SAME expose the capped receipt result for the frozen rise tail. -/
theorem frontierHG2aResult_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin p.n)) :
    FrontierHG2aResult E rho G ΔF i m r U ↔
  let D := max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
    (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ)
  FrontierRiseBy p c E rho i m D ∨
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      m + 1 ≤ (heightView p X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) D y := Iff.rfl

omit [DecidableEq V] in
/-- Blueprint 21:1695--1720; HG4-RISE F1/F2.
DC: SAME the capped entry and first-opening bounds fit the fixed HG.4 guard.
The epsF bound follows from the frozen LivenessBoundW field. -/
theorem frontierSearch_hg2a_bound (p : Params) (G ΔF d a tU : Time)
    (hbound : LivenessBoundW p ΔF) (ha : a ≤ d + P p - 4 * p.Δ)
    (hU : tU ≤ d - 6 * p.Δ) :
    max (a + Γ p G - p.Δ + epsF p ΔF)
      (tU + 2 * P p + Γ p G - 3 * p.Δ) ≤ d + (2 * P p + Γ p G - 9 * p.Δ) := by
  have he : epsF p ΔF ≤ P p - 8 * p.Δ := by
    rw [epsF_def]
    exact sub_le_sub_right (betaF_le_period p ΔF hbound) _
  apply max_le <;> linarith [p.deltaPos]

omit [DecidableEq V] in
/-- Blueprint 21:1592--1640; HG4-RISE F1 STOP evidence.
DC: SAME the existing service budget is 5Δ after the terminal budget.
This identity does not give a larger horizon to the terminal task. -/
theorem frontierSearch_hg2a_gate_cost (p : Params) (G ΔF a tU : Time) :
    max (a + Γ p G + 4 * p.Δ + epsF p ΔF)
      (tU + 2 * P p + Γ p G + 2 * p.Δ) =
    max (a + Γ p G - p.Δ + epsF p ΔF)
      (tU + 2 * P p + Γ p G - 3 * p.Δ) + 5 * p.Δ := by
  rw [← max_add_add_right]
  congr 1 <;> ring

/-- Blueprint 21:1592--1640; HG4-RISE F1, slot component only.
DC: SAME reuse healing_promotion_age_gap (PromotionArithmetic:257).
GUP r2: the rounded bound supplies the full G window from the terminal guard.
This produces an honest slot; it does not assert promotion or receipt. -/
theorem frontierSearch_hg2a_gap [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (r : Nat) (U : FGBlock (Fin p.n)) (hgst : E.t_GST ≤ (r : Time) * P p)
    (hhor : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.proposalTime p.toParams s + p.Δ ≤
        max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ∧
      SA.gateTime p.toParams s ≤
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) := by
  have hwin : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon := by
    have := (fgsa_gamma_bounds p G).1
    rw [← max_add_add_right]
    obtain ⟨ha, hU⟩ := max_le_iff.mp hhor
    rw [actionTime_periodW, epsF_def] at ha
    apply max_le <;> linarith [p.deltaPos]
  exact healing_promotion_age_gap E rho hrec.toRecovery₂ r U.slot hgst hwin

/-- ROOT-DIGEST W2b. Blueprint 21:1592–1640; S5 H2, route steps 1–8.
DC: SAME the saved seed supplies source transfer only through the proposal read.
The strict cap supplies receipt compatibility through t_X+Δ.
The seed binders are the frozen StrongServed fields; r is an opening after q. -/
theorem frontier_hg2a_receipt [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho)
    (proposalServices : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
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
    {u : Time} {i m r q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg U : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (he : eraseFG Qfg = Q) (hQm : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hseed : FrontierSeedQualification p E u q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hp : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqr : q ≤ r * p.R) (hU : U = (heightView p Qfg).T_h)
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hhor : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ rho.horizon) :
    FrontierHG2aResult E rho G ΔF i m r U := by
  classical
  let D := max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
    (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ)
  have hs := hrec.base.valid.toScheduleWellFormed
  rcases frontierSearch_strict_cap_or_rise p c E rho hs mono i m D hstart
      with hrise | hcap
  · exact Or.inl hrise
  · right
    have hqT : SA.proposalTime p.toParams q ≤ (r : Time) * P p := by
      have hc : (q : Time) ≤ (r : Time) * p.R := by exact_mod_cast hqr
      change 4 * p.Δ * (q : Time) ≤ (r : Time) * (4 * (p.R : Time) * p.Δ)
      nlinarith [p.deltaPos]
    have hsync : E.t_GST ≤ (r : Time) * P p := hgst.trans (hu.trans hqT)
    obtain ⟨_, s, hlo, hhi, hslot, hterminal, _⟩ :=
      frontierSearch_hg2a_gap E rho hrec r U hsync hhor
    have htD : SA.proposalTime p.toParams s < D := by linarith [p.deltaPos]
    have hshor : SA.proposalTime p.toParams s ≤ rho.horizon := htD.le.trans hhor
    obtain ⟨hc, hage⟩ := promotion_age_grid r s U ΔF hlo
    have hF : 0 ≤ ΔF := by
      have := hrec.deltaF
      rw [hrec.base.delta] at this
      linarith [p.deltaPos]
    have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
    have hat : p.actionTime r ≤ SA.proposalTime p.toParams s := by
      apply le_trans (b := carrierTimeW p ΔF r) _ hc
      rw [actionTime_periodW, carrierTimeW_def, betaF_def]
      nlinarith [p.deltaPos]
    have hqgate : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s := by
      change SA.proposalTime p.toParams q + 6 * p.Δ ≤ _
      rw [actionTime_periodW] at hat
      linarith only [hqT, hat]
    have hstartAction : E.t_GST ≤ p.actionTime r := by
      rw [actionTime_periodW]
      linarith [p.deltaPos]
    have hgsts : E.t_GST ≤ SA.proposalTime p.toParams s := hstartAction.trans hat
    have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
      have hcs := hc
      rw [carrierTimeW_def, betaF_def] at hcs
      change (r : Time) * P p + 4 * (kappaF p ΔF : Time) * p.Δ ≤
        4 * p.Δ * (s : Int) at hcs
      change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
      nlinarith [p.deltaPos]
    have hjoin := healing_recovery_restart_cutoff hrec hslot.2 hshor hcut
    obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
      hslot hgsts hshor hjoin
    have hf := frontier u (SA.proposalTime p.toParams s) m J contested q Q Qfg
      hgst hQ he hQm hexact ((frontierSeedQualification_iff p E u q).mp hseed) hu hp
      hqgate hshor (fun k x _ hkt hx => hcap k x
        (hkt.trans (frontierSearch_timeIdx_le_idxBefore p c rho htD)) hx)
    obtain ⟨hcovered, hentry, hentryEq, _⟩ := hf.2.2 r hqr hat
    obtain ⟨U0, hU0, _, hrows⟩ := healing_promotion_bounded_rows E rho hrec.toRecovery₂
      hentry hcovered
    have hU0U : U0 = U := by
      obtain ⟨K, _, _, _, _, _, hK, _, _, _, _, _, hKU0, _⟩ := hrows _ hQ.1.2
      exact hKU0.symm.trans ((hentryEq _ K hQ.1.2 hK).trans hU.symm)
    subst U0
    have hqs : q + 2 ≤ s := by
      obtain ⟨_, _, _, _, _, hafter⟩ :=
        healing_promotion_row_deadline E rho hrec.toRecovery₂ hbound (rSent := r) le_rfl
          hstartAction hc
      omega
    have hQX : FGBlock.Preceq Qfg X.parent := by
      have hb := hf.1.2.1 s (eraseFG X) hqs le_rfl hnew
      rw [← he, eraseFG_parent] at hb
      exact eraseFG_preceq_iff.mp hb
    have hUP : FGBlock.Preceq U X.parent := by
      rw [hU]
      exact KitFG.preceq_trans ((fgCertificateLaws p).height.entry_preceq Qfg) hQX
    have src : PromotionSourceAt p c E rho ΔF r m U s X := by
      refine ⟨hU0, hUP, hnew, hXslot, ?_, hc, hage, hshor, ?_⟩
      · rw [actionTime_periodW]
        linarith [p.deltaPos]
      · intro x hx
        obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn⟩ := hrows x hx
        exact ⟨j, rSent, a, hr, ha, hn⟩
    have hh := promotion_age_advance_of_source E rho hrec.toRecovery₂ src hδ hbound
      rowsReceipt progressCoverage hfold faultQ honestQuorum
    obtain ⟨y, hy, hheld⟩ := healing_promotion_first_receipt_of_frontierCap E rho hrec.toRecovery₂
      crossing (proposalServices s) hnew hgsts hQX
      (fun k x hk hx => hcap k x
        (hk.trans (healing_phase_idxBefore_mono p c rho hterminal)) hx)
      hQm (hterminal.trans hhor)
    have heldMono {d d' : Time} (hdd : d ≤ d')
        (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ nd.st.fg.TF) d y) :
        Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ nd.st.fg.TF) d' y := by
      rw [Gen.V2.Duty.HoldsBefore_def,
        ← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
      rw [Gen.V2.Duty.HoldsBefore_def,
        ← Gen.V2.Duty.stateBefore_idxBefore E rho d' hs]
      exact (fgsa_store_durable p c E rho
        (healing_phase_idxBefore_mono p c rho hdd) y).1 hheld
    exact ⟨s, X, hnew, hXslot, hh, y, hy, heldMono hterminal hheld⟩

end AvailableChain.FGSA.Run
end
