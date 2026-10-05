module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Growth

public section

/-! WC J3, plan §§6.12–7; DC joint growth contract.
These tests retain the exact deadline and the inclusive read at the cut. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J3, plan §7; DC AvailableChainGrowth.afterGST: match the reviewed growth type. -/
theorem growthContract (ΔF : Time) (u : Slot) (Q : Block) (iStar : Nat) :
    WCGrowthStatement p c E rho ΔF u Q iStar :=
  wc_growth_of_safety_inclusion ΔF u Q iStar

omit [DecidableEq V] in
/-- WC J3, plan §6.12; DC cut reads: match the reviewed public-read type. -/
theorem readContract (w : HealingWitness) (iStar : Nat) :
    WCCutPublicReadStatement p c E rho w iStar := by
  intro hs hcut t ht
  exact wc_cut_publicRead hs hcut t ht

omit [DecidableEq V] in
/-- WC J3, plan §6.12; DC cut reads: include same-time deliveries at the trigger. -/
theorem readAtCut {u : Slot} {iStar : Nat}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hcut : iStar = afterTicksIdx rho (SA.gateTime p.toParams u)) :
    iStar ≤ timeIdx rho (SA.gateTime p.toParams u) ∧
      timeIdx rho (SA.gateTime p.toParams u) ≤ rho.events.length :=
  wc_cut_publicRead hs hcut _ le_rfl

end AvailableChain.FGSA.Run.Tests.WeakContinuationGrowth
end
