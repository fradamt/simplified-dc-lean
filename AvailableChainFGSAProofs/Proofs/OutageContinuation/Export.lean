module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationJoint
public import AvailableChainFGSAProofs.Proofs.Shared.Claims

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The scoped exporter preserves the public continuation claim.
The finite Clean supplier has named producers. The exact W seed is still open. -/
theorem outageContinuation_claim_of (p : Params)
    (hfoundation : FGFoundationClaim p) (hsrc : SrcFrameAboveClaim p)
    (hdisc : SourceDisciplineClaim p)
    (hClean : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      {b₀ ΔF : Time}, HealthyPrefixSleep₂ p c E rho b₀ ΔF →
      FaultQ p.n (Gen.V2.Duty.faulty rho).card →
      FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
      OutageCleanCutInputs (p := p) (c := c) E rho b₀)
    (hWSeed : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      {fast : Bool} {T b₀ b₁ ΔF : Time},
      OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
      ∀ x B, confirmedReader p c E rho x T →
      Block.Preceq B (S_at p c E rho (timeIdx rho T) x) → B ≠ .genesis →
      OutageWSeed (p := p) (c := c) (E := E) (rho := rho) fast b₀ b₁ B) :
    OutageContinuationClaim p := by
  intro V _ _ In c E rho fast T b₀ b₁ ΔF h
  have hq := h.pre.faultQ_of_pos
    (outage_cut_pos (outageV_arming_prem h.toOutageContinuationPrem))
  have hp : SourceDisciplinePrem p c E rho () := ⟨h.pre.base, hq⟩
  have hf0 := hfoundation c E rho () hp
  have hf : FGFoundation p c E rho :=
    ⟨hf0.store, hf0.cumul, hf0.mono, hf0.frame, hf0.geo, hf0.strat, hf0.reconcile⟩
  have hs := hsrc c E rho () hp
  have hd := hdisc c E rho () hp
  apply outage_continuation_scoped_body hf hs hd.1.1 _
    (hClean c E rho h.sleepPre hq hf hs) h hd.2.2 (hWSeed c E rho h)
  intro k x r a e ha he
  obtain ⟨e', C, G, he', hC, hn, hTC, hG, hCG, hfast⟩ := hd.1.2.2 k x r a ha
  exact ⟨C, G, hC, (Option.some.inj (he.symm.trans he')).trans hn, hTC, hG, hCG, hfast⟩

end AvailableChain.FGSA.Run
end
