module
public import AvailableChainFGSAProofs.Proofs.Healing.Delivery -- shake: keep (TDel fixture)

public section

namespace AvailableChain.FGSA.Run.Tests.HealingDelivery
open AvailableChain.SimplexFG

-- Pure/model fixture: s = u−1 acts after both slot-u duty reads.
example (p : Params) (s : Slot) :
    SA.gateTime p.toParams s = SA.proposalTime p.toParams (s + 1) + 2 * p.Δ ∧
      SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
  change 4 * p.Δ * (s : Int) + 6 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ ∧
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
  push_cast
  constructor
  · ring
  · linarith [p.deltaPos]

-- Pure/model fixture: finality above K discharges the coverage arm.
example (p : Params) (st : State p.n) (K : FGBlock (Fin p.n))
    (hKF : FGBlock.Preceq K st.fg.F) :
    (∀ B, FGBlock.Preceq B K → B ∈ st.fg.TF) ∨ FGBlock.Preceq K st.fg.F :=
  Or.inr hKF

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- Conditional package fixture: receiver F changes between e_s and the freeze.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (source : TSrc p c E rho) (mono : RMono p c E rho)
    {x y : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams (r * p.R))
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon)
    (_hchange : (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F ≠
      (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F)
    (hcompat : Block.Compatible (eraseFG K)
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F)) :
    (∀ B, FGBlock.Preceq B K →
      B ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.TF) ∨
      FGBlock.Preceq K
        (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F :=
  healing_tDel E rho hrec source mono y r K hy hK hgst hhor x hx hcompat

-- Conditional package fixture: an actual honest pre-GST body acceptance.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    {j : Nat} {y x : V} {t D : Time} {s : Slot} {b : Block}
    {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (ha : V2.D.Run.acceptsAt E rho j y (ofWire p ⟨.proposer s, .proposal b raw sup rows⟩) t)
    (ht : t < E.t_GST) (hKb : eraseFG K = b)
    (hd : E.t_GST + p.Δ ≤ D) (hhor : D ≤ rho.horizon)
    (hF : FGBlock.Preceq (V2.D.Run.stateBeforeTime E rho D x).st.fg.F K) :
    Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) D x :=
  healing_source_old_body E rho hrec mono hy hx ha ht hKb hd hhor hF

end AvailableChain.FGSA.Run.Tests.HealingDelivery
end
