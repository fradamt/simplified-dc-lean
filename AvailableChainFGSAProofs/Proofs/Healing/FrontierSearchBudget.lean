module
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW

public section

/-! Blueprint 21 HG.4/HG.5 and H.11. Keep the frozen budgets.
The terminal fact has an action-relative horizon. It does not state the
entry-age bound from HG.2a_F or continuation through same-frontier events. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Blueprint 21 HG.5. DC: SAME one contest repair plus the seed-gate rise tail. -/
theorem frontierSearch_contest_rise_cost (p : Params) (G ΔF ρbar : Time)
    (hbound : LivenessBoundW p ΔF) :
    (ρbar + 3 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) = B_cF p ΔF G ρbar := by
  rw [B_cF_eq p ΔF G ρbar hbound]
  change _ = ρbar + 2 * P p + Γ p G - 6 * p.Δ
  ring

/-- Blueprint 21 HG.5. DC: SAME one contest repair plus the exact-height row tail. -/
theorem frontierSearch_contest_row_cost (p : Params) (ρbar : Time) :
    (ρbar + 3 * p.Δ) + (P p - 4 * p.Δ) = D_cF p ρbar := by
  change _ = ρbar + P p - p.Δ
  ring

/-- Blueprint 21 HG.4. DC: SAME the opening-relative terminal bound
composes to 3P+Γ-13Δ, which is longer than the requested seed-gate tail. -/
theorem frontierSearch_terminal_opening_cost (p : Params) (G d a t : Time)
    (hopening : a ≤ d + (P p - 4 * p.Δ))
    (hterminal : t ≤ a + 2 * P p + Γ p G - 9 * p.Δ) :
    t ≤ d + (3 * P p + Γ p G - 13 * p.Δ) := by
  linarith only [hopening, hterminal]

/-- Run 2 R2-c STOP evidence. DC: SAME aligned G=8Δ, Δ=1, R=2.
This refutes only the horizon implication needed to call the terminal fact.
It does not refute HG.4 for valid executions. -/
theorem frontierSearch_terminal_horizon_gap8 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 8 - 9) ≤ horizon → a + 2 * 8 + 8 - 9 ≤ horizon) := by
  intro h
  have hb := h 0 4 15 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb

/-- Run 2 R2-c STOP evidence. DC: SAME aligned G=12Δ, Δ=1, R=2. -/
theorem frontierSearch_terminal_horizon_gap12 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 12 - 9) ≤ horizon → a + 2 * 8 + 12 - 9 ≤ horizon) := by
  intro h
  have hb := h 0 4 19 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb

end AvailableChain.FGSA.Run
end
