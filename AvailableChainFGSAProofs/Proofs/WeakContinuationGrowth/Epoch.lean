module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A nonempty executed read supplies the enabled gate at the same tick. -/
theorem wcg_gate_enabled_of_result {j : Nat} {v : V} {s : Slot} {C : Block}
    (hS : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C)) :
    enabledGateAt p c E rho j v s := by
  have h := fgsa_gate_raw_of_nonempty p c E rho hS ht
    ((gateResultAt_eq_gateResult p c E rho hS ht).symm.trans hC)
  have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j v) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho j v) s)
  have hg : joinedAtTime p (storeAt p c E rho j v).restartTime
      (SA.gateTime p.toParams s) = true := h.1
  refine ⟨ht, ?_⟩
  change (match (storeAt p c E rho j v).restartTime with
    | none => True | some w => w ≤ slotStartZ p (s : Int))
  cases hr : (storeAt p c E rho j v).restartTime with
  | none => trivial
  | some w =>
    rw [hr] at hg
    change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) =
      true at hg
    change w ≤ 4 * p.Δ * (s : Int)
    simpa only [hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      decide_eq_true_eq] using hg

/-- W3-J supplies the stored pre-gate test for the gate-write law. -/
theorem wcg_gate_pre_joined {j : Nat} {x : V} {s : Slot}
    (hG : enabledGateAt p c E rho j x s) :
    joinedNow p (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)) = true := by
  rw [clockPre_joined]
  exact fgsa_gate_joined_of_enabled E rho hG

end AvailableChain.FGSA.Run
end
