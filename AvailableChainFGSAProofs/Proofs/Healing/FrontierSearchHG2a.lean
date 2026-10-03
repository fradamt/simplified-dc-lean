module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic

public section

/-! Blueprint 21 HG.2a_F:1592--1640 and HG.4:1695--1720; HG4-RISE F1.
The result contract stops at a rise. Same-frontier events do not stop it.
The gap adapter reuses the existing slot producer. It does not prove the
height or receipt fields of the result contract. F1 remains stopped there.
HG.1 source preservation: `frontier_service` (FrontierService:307).
No fixed phase after the saved gate is assumed by the result contract. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 21:1592--1640; HG4-RISE F1.
DC: SAME the saved entry's terminal result: a first rise or a strict honest
high receipt. This is a conclusion contract, with no producer yet. -/
def FrontierHG2aResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (i m r : Nat) (U : FGBlock (Fin p.n)) : Prop :=
  let D := max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
    (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ)
  FrontierRiseBy p c E rho i m D ∨
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      m + 1 ≤ (heightView p X).h ∧
      ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) D y

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
Recovery₂.gamma_eq supplies the full G window from the terminal guard.
This produces an honest slot; it does not assert promotion or receipt. -/
theorem frontierSearch_hg2a_gap [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
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
    rw [← hrec.gamma_eq, ← max_add_add_right]
    obtain ⟨ha, hU⟩ := max_le_iff.mp hhor
    rw [actionTime_periodW, epsF_def] at ha
    apply max_le <;> linarith [p.deltaPos]
  exact healing_promotion_age_gap E rho hrec r U.slot hgst hwin

end AvailableChain.FGSA.Run
end
