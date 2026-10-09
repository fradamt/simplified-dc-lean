module
public import AvailableChainFGSA.Model.Spec.Transitions
public import Mathlib.Tactic.Ring

public section

namespace AvailableChain.FGSA.Spec

/-- Revocation of s occurs at the vote time of s+1, before that vote. -/
theorem revoke_vote_time (Δ : Time) (s : Int) :
    phaseTime Δ s 5 = phaseTime Δ (s + 1) 1 := by
  unfold phaseTime slotTime
  ring

/-- Confirmation of s occurs at the support cutoff of s+1. -/
theorem confirmation_cutoff_time (Δ : Time) (s : Int) :
    phaseTime Δ s 6 = phaseTime Δ (s + 1) 2 := by
  unfold phaseTime slotTime
  ring

theorem phaseTime_strict (Δ : Time) (hΔ : 0 < Δ) (s a b : Int) (hab : a < b) :
    phaseTime Δ s a < phaseTime Δ s b := by
  unfold phaseTime
  exact Int.add_lt_add_left (mul_lt_mul_of_pos_right hab hΔ) _

/-- Every represented public phase has the unchanged Lean schedule time. -/
theorem schedule_embedding (p : Params) (s : Slot) :
    slotTime p.Δ s = SA.proposalTime p.toParams s ∧
    phaseTime p.Δ s 1 = SA.voteTime p.toParams s ∧
    phaseTime p.Δ s 2 = SA.earlyTime p.toParams s ∧
    phaseTime p.Δ s 3 = SA.freezeTime p.toParams s ∧
    phaseTime p.Δ s 5 = SA.releaseTime p.toParams s ∧
    phaseTime p.Δ s 6 = SA.gateTime p.toParams s := by
  dsimp only [slotTime, phaseTime, SA.proposalTime, SA.voteTime, SA.earlyTime,
    SA.freezeTime, SA.releaseTime, SA.gateTime, GridCO.proposalTime,
    GridCO.voteTime, GridCO.earlyTime, GridCO.freezeTime, GridCO.releaseTime,
    GridCO.gateTime, SA.Params.engine]
  simp only [one_mul, and_self]

theorem actionTime_embedding (p : Params) (r : Nat) :
    p.actionTime r = phaseTime p.Δ (r * p.R) 6 := rfl

/-- A pure composition fact, not a scheduled-run theorem. -/
theorem tick_order {σ : Type} (clock ac proposal attest : σ → σ) (state : σ) :
    tick clock ac proposal attest state = attest (proposal (ac (clock state))) := rfl

end AvailableChain.FGSA.Spec
end
