module
public import AvailableChainFGSA.Model.Objects
public import Mathlib.Tactic.Ring.RingNF

public section

namespace AvailableChain.FGSA.Run

/-- Paper 22:217–220,1228–1234,1985–1989: bound the HEAD read at an action.
DC: INTENTIONAL: SA clocks use Δ; the action read is at label qR+1. -/
theorem finality_action_time_bounds (p : Params) (r q : Nat) (hrq : r ≤ q)
    (G Δ horizon : Time) (hGST : G ≤ SA.proposalTime p.toParams (r * p.R))
    (hΔ : Δ = p.Δ) (hhor : p.actionTime q ≤ horizon) :
    G ≤ SA.voteTime p.toParams (q * p.R + 1) ∧
      SA.voteTime p.toParams (q * p.R + 1) + Δ ≤ SA.earlyTime p.toParams (q * p.R + 1) ∧
      SA.earlyTime p.toParams (q * p.R + 1) ≤ horizon ∧
      SA.voteTime p.toParams (q * p.R + 1) ≤ horizon := by
  have hearly : SA.earlyTime p.toParams (q * p.R + 1) = p.actionTime q := by
    change 4 * p.Δ * ((q * p.R + 1 : Nat) : Int) + 2 * p.Δ =
      4 * p.Δ * ((q * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have hvte : SA.voteTime p.toParams (q * p.R + 1) + Δ ≤
      SA.earlyTime p.toParams (q * p.R + 1) := by
    rw [hΔ]
    change 4 * p.Δ * ((q * p.R + 1 : Nat) : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * ((q * p.R + 1 : Nat) : Int) + 2 * p.Δ
    linarith
  have heh : SA.earlyTime p.toParams (q * p.R + 1) ≤ horizon := hearly ▸ hhor
  have hd := p.deltaPos
  refine ⟨hGST.trans ?_, hvte, heh, ?_⟩
  · have hs : r * p.R ≤ q * p.R + 1 :=
      (Nat.mul_le_mul_right p.R hrq).trans (Nat.le_succ _)
    have hcast : ((r * p.R : Nat) : Time) ≤ ((q * p.R + 1 : Nat) : Time) := by
      exact_mod_cast hs
    change 4 * p.Δ * ((r * p.R : Nat) : Time) ≤
      4 * p.Δ * ((q * p.R + 1 : Nat) : Time) + p.Δ
    nlinarith
  · rw [hΔ] at hvte
    linarith

end AvailableChain.FGSA.Run
end
