module
public import AvailableChainFGSAProofs.Proofs.Healing.SourceTiming

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem delivery_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- Blueprint 21:550–567 (IF.5), 2646–2652 (H.12); B13, B15, B17, B26.
DC: SAME admission or coverage at the exact strict-before freeze read.
Assembly supplies `sourceDiscipline_tSrc` as `source` and `fgsa_rMono` as `mono`.
The consumers prove compatibility; this producer keeps its frozen antecedent. -/
theorem healing_tDel [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMono p c E rho) : TDel p c E rho := by
  intro y r K hy hK hgst hhor x hx
  rw [Gen.V2.Duty.HoldsBefore_def]
  intro hcompat
  change (Block.preceq (eraseFG K) _ || Block.preceq _ (eraseFG K)) = true at hcompat
  rcases Bool.or_eq_true_iff.mp hcompat with hKF | hFK
  · exact Or.inr (delivery_lift hKF)
  · left
    have heD : SA.earlyTime p.toParams (r * p.R) ≤
        SA.freezeTime p.toParams (r * p.R) := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 2 * p.Δ ≤
        4 * p.Δ * ((r * p.R : Nat) : Int) + 3 * p.Δ
      linarith [p.deltaPos]
    exact healing_source_body_relay E rho hrec source mono hy hx hK hgst heD hhor
      (delivery_lift hFK)

end AvailableChain.FGSA.Run
end
