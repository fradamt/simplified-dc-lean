module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRenewed
public import AvailableChainFGSAProofs.Proofs.Healing.SupportGate -- shake: keep (Recovery₂.gamma_eq supplier)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem promotion_terminal_grid_upper (p : Params) (G z : Time) (s : Slot)
    (hs : SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + G) :
    SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + Γ p G := by
  have hd : 0 < 4 * p.Δ := by have := p.deltaPos; linarith
  change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * z + G at hs
  have hdiv : (s : Time) - z ≤ G / (4 * p.Δ) :=
    (Int.le_ediv_iff_mul_le hd).mpr (by nlinarith)
  change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * z + 4 * p.Δ * (G / (4 * p.Δ))
  nlinarith

private theorem promotion_terminal_gap (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.gateTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
  have hclass0 : G = Γ p G := hrec.gamma_eq.symm
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ; nlinarith [p.deltaPos]
  have ha := actionTime_periodW p r
  have hwindow : (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon := by
    rw [hclass0]
    linarith [p.deltaPos]
  have hstart : E.t_GST ≤ (r : Time) * P p + 2 * P p - 4 * p.Δ := by
    linarith [p.deltaPos]
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap _ hstart hwindow
  rw [proposalTime_fgsa] at hlo hhi
  have hgrid : (r : Time) * P p + 2 * P p - 4 * p.Δ =
      4 * p.Δ * ((r : Time) * p.R + 2 * p.R - 1) := by
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      2 * (4 * (p.R : Time) * p.Δ) - 4 * p.Δ = _
    ring
  have hup := promotion_terminal_grid_upper p G ((r : Time) * p.R + 2 * p.R - 1) s
    (by rw [← hgrid]; exact hhi)
  rw [← hgrid] at hup
  have hlow : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s := by
    rw [hgrid] at hlo
    change 4 * p.Δ * ((r : Time) * p.R + 2 * p.R - 1) < 4 * p.Δ * (s : Time) at hlo
    have hc : (r : Time) * p.R + 2 * p.R ≤ s := by
      have := p.deltaPos
      have : (r : Time) * p.R + 2 * p.R - 1 < s := by nlinarith
      linarith only [Int.add_one_le_iff.mpr this]
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      2 * (4 * (p.R : Time) * p.Δ) ≤ 4 * p.Δ * (s : Time)
    nlinarith [p.deltaPos]
  refine ⟨hwindow, s, hlow, by linarith, hs, ?_⟩
  change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
  linarith

/-- Blueprint 21:1356–1419, terminal carrier for an aligned recovery gap.
DC: INTENTIONAL the terminal horizon supplies promotion and the strict first
receipt. Recovery₂.gamma_eq supplies alignment. Assembly supplies RMono, RXing,
TPerm, the progress fold, and the standing INLINE row/coverage/quorum facts. -/
theorem healing_renewedPromotion_terminal (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    (r : Nat)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon) :
    ∀ u m J contested l q Q height,
      E.t_GST ≤ u → PhaseInterval p c E rho u (p.actionTime r) m J contested →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
      SA.proposalTime p.toParams l < SA.proposalTime p.toParams q →
      HonestProposal E rho (fgsaInterface p c) q Q → ExactService p c E rho q Q →
      OpeningEntry p c E rho r height → OpeningCovered p c E rho r Q →
      (∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) →
      (∃ i ev, afterTicksIdx rho (p.actionTime r) ≤ i ∧
        rho.events[i]? = some ev ∧ EffectiveEvent p c E rho i ∧
        ev.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ) ∨
      (∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
        ↑r * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
        SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
        height + 1 ≤ (heightView p X).h ∧
        (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y)) := by
  intro u m J contested l q Q height hgst hp hu hq hl _hQ _hservice hentry hcovered _hrepair
  have hsched := hrec.base.valid.toScheduleWellFormed
  let D := p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ
  rcases healing_promotion_event_split p c E rho hsched (p.actionTime r) D with
    ⟨i, ev, hi, hev, heff, htime, _⟩ | hquiet
  · exact Or.inl ⟨i, ev, hi, hev, heff, htime⟩
  have har : E.t_GST ≤ p.actionTime r := hgst.trans hp.1
  obtain ⟨_, s, hlo, hhi, hslot0, _hgate⟩ :=
    promotion_terminal_gap E rho hrec r har hhor
  have hproposalHor : SA.proposalTime p.toParams s ≤ rho.horizon := by
    linarith [p.deltaPos]
  have hproposalGST : E.t_GST ≤ SA.proposalTime p.toParams s := by
    have ha := actionTime_periodW p r
    have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
    have hP : 8 * p.Δ ≤ P p := by
      change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
      nlinarith [p.deltaPos]
    linarith [p.deltaPos]
  obtain ⟨X, hnew, hslot, _⟩ := healing_promotion_slot_proposal E rho hrec hslot0
    hproposalGST hproposalHor
  have ha := actionTime_periodW p r
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hats : p.actionTime r ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
  have hdD : SA.proposalTime p.toParams s + p.Δ ≤ D := by dsimp only [D]; linarith
  have hdhor : SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon := hdD.trans hhor
  have hpD : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) m J contested := by
    apply healing_phase_extend_of_no_effective p c E rho hrec mono crossing hp
      (by linarith [p.deltaPos]) hdhor
    intro j hj hjd
    apply hquiet j
      ((preIdx_le_afterTicksIdx E rho hsched (p.actionTime r)).2.trans hj)
    apply hjd.trans_le
    change (rho.events.filter (fun e =>
      decide (e.time ≤ SA.proposalTime p.toParams s + p.Δ))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ D))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      ((of_decide_eq_true he).trans hdD))
  have hpts : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested := by
    refine ⟨hp.1.trans hats, le_trans (by linarith [p.deltaPos]) hdhor, hp.2.2.1, ?_⟩
    intro i x hui hits hx
    apply hpD.2.2.2 i x hui _ hx
    apply hits.trans
    change (rho.events.filter (fun e => decide (e.time ≤ SA.proposalTime p.toParams s))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ SA.proposalTime p.toParams s + p.Δ))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      (by have := of_decide_eq_true he; linarith [p.deltaPos]))
  have huvote : u ≤ SA.voteTime p.toParams (r * p.R) := by
    have hqt : SA.proposalTime p.toParams q ≤ SA.proposalTime p.toParams (r * p.R) := by
      change 4 * p.Δ * (q : Time) ≤ 4 * p.Δ * ((r * p.R : Nat) : Time)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by linarith [p.deltaPos])
    change u ≤ SA.proposalTime p.toParams (r * p.R) + p.Δ
    linarith [p.deltaPos]
  have hh := healing_promotion_advance E rho hrec hδ hbound perm rowsReceipt progressCoverage
    hfold faultQ honestQuorum hentry hcovered hgst hpts huvote hlo hnew hslot
  have hreceipt := healing_promotion_first_receipt E rho hrec crossing hnew (hp.1.trans hats)
    hgst hpD
  exact Or.inr ⟨s, X, hnew, hslot, hlo, hhi, hh, hreceipt⟩

end AvailableChain.FGSA.Run
end
