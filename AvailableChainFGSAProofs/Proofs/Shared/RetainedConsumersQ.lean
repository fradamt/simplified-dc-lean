module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Blueprint 21 L4-R:2200–2222,2280–2292. Class (iii).
DC: INTENTIONAL; use the Q cone only in d_q ≤ e < min(w_a,w_b).
The later proposal's gate is strictly before both stops. The lane input is
scoped to both actual reads in that interval. No property of Q at w_a is assumed. -/
theorem fgsa_retainedReads_L4R
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (w_a w_b : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < min w_a w_b)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < min w_a w_b) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q b Kc := by
  have hhead : SA.voteTime p.toParams s < min w_a w_b := by
    have hd := p.deltaPos
    change GridCO.proposalTime p.engine s + p.Δ < _
    change GridCO.proposalTime p.engine s + 6 * p.Δ < _ at hstop
    linarith
  exact fgsa_retainedReads_H17 (hroots := hroots)
    E rho hE hN hDelta s hSync hx hip hseat b raw sup rows hem Q
    (fun y hy ih hih => hinput y hy ih hih ⟨hafter, hhead⟩)

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1500–1574. Class (iii).
DC: INTENTIONAL; stop is the first honest frontier rise above m.
The lane input describes reads after d_q and before that stop. Slot q+1's
proposal and HEAD precede d_q (1570–1574), so they use H.6/H.6-S instead. -/
theorem fgsa_retainedReads_HG1
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (stop : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < stop) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q b Kc := by
  have hhead : SA.voteTime p.toParams s < stop := by
    have hd := p.deltaPos
    change GridCO.proposalTime p.engine s + p.Δ < _
    change GridCO.proposalTime p.engine s + 6 * p.Δ < _ at hstop
    linarith
  exact fgsa_retainedReads_H17 (hroots := hroots)
    E rho hE hN hDelta s hSync hx hip hseat b raw sup rows hem Q
    (fun y hy ih hih => hinput y hy ih hih ⟨hafter, hhead⟩)

end AvailableChain.FGSA.Run
end
