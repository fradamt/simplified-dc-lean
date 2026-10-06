module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep (companion components)
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Export -- shake: keep (permitted WC reuse route)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Reuse the exact one-quorum causal theorem through the existing lane Export.
Assembly is the permitted home for cross-lane theorem composition. -/
theorem wcg_finalityTargetEarlier [Fintype V] :
    WCFinalityTargetEarlierStatement p c E rho := wc_finalityTargetEarlier

/-- Reuse the existing invariant-to-safety and safety/inclusion-to-growth proofs.
This is an internal assembly step. Its invariant and inclusion producers remain
open; they are not premises of WeakContinuationGrowthClaim. -/
theorem wcg_live_of_invariant_inclusion {ΔF : Time}
    {w : HealingWitness} {iStar : Nat}
    (hb : Base₂ p c E rho) (hs : WCSeed p c E rho w iStar)
    (hi : ∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i)
    (hf : ∀ i x y, iStar ≤ i → i ≤ rho.events.length →
      x ∈ rho.honest → y ∈ rho.honest →
      Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y))
    (hincl : ∀ pt : PtSP, w.u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon → ServedFromGateAt p c E rho pt) :
    WeakContinuationLiveAt₂ p c E rho w.u w.QStar iStar ΔF := by
  obtain ⟨hc, hm, hseed, ho⟩ := wc_seededSafety hb.valid.toScheduleWellFormed hs hi
  have hsafe : SSafeFromCut₂ p c E rho iStar w.QStar ΔF := ⟨hc, hm, hseed, hf, ho⟩
  exact ⟨fun _ => hsafe, fun _ => hincl,
    wc_growth_of_safety_inclusion ΔF w.u w.QStar iStar hb hs.cut hsafe hincl⟩

end AvailableChain.FGSA.Run
end
