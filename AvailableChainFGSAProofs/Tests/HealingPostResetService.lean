module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetService -- shake: keep (J6 applications)

set_option linter.privateModule false

public section

/-! S5 J6 tests. The short-horizon example inhabits only the cone. The
applications below use an actual honest proposal and consume the exact
HEAD and retained-carrier conclusions. Full gate service remains stopped. -/

namespace AvailableChain.FGSA.Run.Tests.HealingPostResetService
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- A1: only a HEAD horizon below the first relevant label makes this trivial.
example (w : HealingWitness) (hshort : rho.horizon < SA.voteTime p.toParams w.sStar) :
    PostResetRetainedCone p c E rho w :=
  postResetRetainedCone_of_horizon_lt p c E rho w hshort

-- A1: apply the definition without asking for a walk or service field.
example (w : HealingWitness) (hcone : PostResetRetainedCone p c E rho w)
    (s : Slot) (hs : w.sStar ≤ s)
    (hHeadHorizon : SA.voteTime p.toParams s ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (Q : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal Q raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip) :
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D := by
  rw [postResetRetainedCone_iff] at hcone
  exact hcone s hs hHeadHorizon hx hip hseat Q raw sup rows hem

-- Risk 6: the exact boundary has a source bound of v - 2 and uses q_(sStar).
example (w : HealingWitness) :
    w.sStar ≤ (w.sStar + 2) - 2 ∧
    SA.releaseTime p.toParams w.sStar ≤ SA.proposalTime p.toParams (w.sStar + 2) - p.Δ :=
  ⟨postReset_source_label_le_sub_two w le_rfl, postReset_release_before_proposal p w le_rfl⟩

-- H0Reset supplies synchrony at the boundary; no QStar data are needed.
example (w : HealingWitness) (hreset : H0Reset p c E rho w) :
    E.t_GST ≤ SA.proposalTime p.toParams (w.sStar + 2) - p.Δ :=
  postReset_synchronous_window p c E rho w hreset le_rfl

variable [Fintype V]

-- A3: consume the HEAD conclusion as equality of a supplied HEAD with Q.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q H : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {y : V} (hy : y ∈ rho.honest) (hH : headAtLabel p c E rho y v = some H) : H = Q := by
  have hQ := healing_postReset_exactHead E rho hrec w hreset hcone v Q hp hv hHeadHorizon y hy
  exact Option.some.inj (hH.symm.trans hQ)

-- T: at v = sStar + 2, consume both exact HEAD and its retained carrier.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) (w.sStar + 2) Q)
    (hHeadHorizon : SA.voteTime p.toParams (w.sStar + 2) ≤ rho.horizon)
    {y : V} {ih : Nat} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (w.sStar + 2)))) :
    headAtLabel p c E rho y (w.sStar + 2) = some Q ∧
    ∃ C : FGBlock (Fin p.n), eraseFG C = Q ∧
      C ∈ domainR p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (w.sStar + 2)))
        (voterBlocks p (clock p (rho.stateBefore E ih y).st
          (SA.voteTime p.toParams (w.sStar + 2))) (w.sStar + 2)) :=
  ⟨healing_postReset_exactHead E rho hrec w hreset hcone _ Q hp le_rfl hHeadHorizon y hy,
    healing_postReset_headCarrier E rho hrec w hreset hcone hp le_rfl hHeadHorizon hy hih⟩

-- Risk 4: a closed HEAD deadline still works when the later gate is outside.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) {v : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hAtHead : rho.horizon = SA.voteTime p.toParams v) :
    rho.horizon < SA.gateTime p.toParams v ∧
      ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q := by
  refine ⟨?_, healing_postReset_exactHead E rho hrec w hreset hcone v Q hp hv hAtHead.ge⟩
  rw [hAtHead]
  change 4 * p.Δ * (v : Int) + p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
  linarith [p.deltaPos]

-- Risk 4: use the named gate-to-HEAD guard when the gate is in the horizon.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) {v : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hGateHorizon : SA.gateTime p.toParams v ≤ rho.horizon) :
    ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q :=
  healing_postReset_exactHead E rho hrec w hreset hcone v Q hp hv
    (postReset_head_horizon p c rho hGateHorizon)

end AvailableChain.FGSA.Run.Tests.HealingPostResetService
end
