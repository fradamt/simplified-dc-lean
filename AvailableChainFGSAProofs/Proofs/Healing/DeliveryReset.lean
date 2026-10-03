module
public import AvailableChainFGSAProofs.Proofs.Healing.SourceTiming

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem reset_delivery_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  preceq_of_eraseFG_preceq (KitFG.viewRootInj_all {A, B})
    ⟨A, by simp, KitFG.preceq_refl A⟩ ⟨B, by simp, KitFG.preceq_refl B⟩ h

/-- Blueprint 21:2652–2660 (H.12 reset, IF.3(c)); B13, B17, B26; hint 2.
DC: CONDITIONAL reset-only core. `hCStarAboveLow` is the IF.3(c) floor at
the release cut; `healing_low_finality_at_reset_reset` (ResetTransfer.lean)
supplies it, and `healing_tDelReset_of_reset` closes frozen TDelReset.
Assembly supplies `sourceDiscipline_tSrc` and `fgsa_rMono`. -/
theorem healing_tDelReset_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMono p c E rho) (w : HealingWitness)
    (h0r : H0Reset p c E rho w) (hhor : SA.releaseTime p.toParams w.sStar ≤ rho.horizon)
    (hCStarAboveLow : ∀ x ∈ rho.honest, Block.Preceq
        (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.releaseTime p.toParams w.sStar) x).st.fg.F)
        w.CStar) :
    ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∃ C ∈ nd.st.fg.TF, eraseFG C = w.CStar)
      (SA.releaseTime p.toParams w.sStar) x := by
  intro x hx
  obtain ⟨j, y, a, C, ha, _, hC, hCS, _⟩ := h0r.fresh
  have hF := hCStarAboveLow x hx
  rw [← hCS] at hF
  have hFC := reset_delivery_lift hF
  have hgst : E.t_GST ≤ SA.voteTime p.toParams (w.rStar * p.R) :=
    h0r.label ▸ h0r.synchronous
  have heD : SA.earlyTime p.toParams (w.rStar * p.R) ≤
      SA.releaseTime p.toParams w.sStar := by
    rw [h0r.label]
    change 4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + 2 * p.Δ ≤
      4 * p.Δ * ((w.rStar * p.R : Nat) : Int) + 5 * p.Δ
    linarith [p.deltaPos]
  have hp := healing_source_body_relay E rho hrec source mono ha.1 hx hC hgst heD hhor hFC
  rw [Gen.V2.Duty.HoldsBefore_def] at hp ⊢
  exact ⟨C, hp C (KitFG.preceq_refl C), hCS⟩

/-- Blueprint 21:2652–2660; B13, B17; hint 2.
DC: CONDITIONAL thin adapter from H0 to the reset-only core.
`hCStarAboveLow` has no producer on base 115fb30; it states IF.3(c) at release.
The other named inputs are `sourceDiscipline_tSrc` and `fgsa_rMono`. -/
theorem healing_tDelReset [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMono p c E rho) (w : HealingWitness)
    (hCStarAboveLow : H0Reset p c E rho w →
      SA.releaseTime p.toParams w.sStar ≤ rho.horizon →
      ∀ x ∈ rho.honest, Block.Preceq
        (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.releaseTime p.toParams w.sStar) x).st.fg.F)
        w.CStar) : TDelReset p c E rho w := by
  intro h0 hhor
  exact healing_tDelReset_core E rho hrec source mono w h0.toH0Reset hhor
    (hCStarAboveLow h0.toH0Reset hhor)

end AvailableChain.FGSA.Run
end
