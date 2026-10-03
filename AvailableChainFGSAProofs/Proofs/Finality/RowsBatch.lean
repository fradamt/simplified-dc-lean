module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSARun.Proofs.Schedule

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Paper 22:1228–1234,1251–1254: the action uses the full label-(z+1) HEAD pool.
DC: INTENTIONAL: this read identity supplies no vote admission or batch premise. -/
theorem rowsPrem_action_pools (q : Nat) (x : V) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime q) = some nd) :
    nd.st.slot p = q * p.R + 1 ∧
    (let raw := GridCO.votesAt nd.st.base (q * p.R + 1)
     let support := raw.filter (fun o => match GridCO.headTarget? o with
       | some H => GridCO.blockKnown (FGSA.actView nd.st) H && decide (H.slot ≤ q * p.R + 1)
       | none => false)
     FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support) := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
  | none => rw [hi] at hnd; cases hnd
  | some i =>
    rw [hi] at hnd
    have he := Option.some.inj hnd
    have hs : nd.st.slot p = q * p.R + 1 := by
      rw [← he]
      exact (fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho i x) q).1
    refine ⟨hs, ?_⟩
    dsimp only [FGSA.fgHead]
    rw [hs]
    rfl

end AvailableChain.FGSA.Run
end
