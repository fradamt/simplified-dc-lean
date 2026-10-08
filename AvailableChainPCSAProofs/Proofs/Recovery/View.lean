module
public import AvailableChainPCSAProofs.Proofs.Shared.VoterView
public import AvailableChainPCSAProofs.Proofs.Recovery.Exclusions

public section

/-! F3 under RECOVERY (pcsa34-r4.3b §5.6.1 step 1): the common view field of
the Formation premise at a slot whose proposal time is at least `t_GST + Δ`,
from the RECOVERY delivery premise and the Shared voter view. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- [pcsa34-r4.3b §5.6.1 step 1 (F3)] Under RECOVERY, at a slot `s` with
`t_GST + Δ ≤ t_s`, every honest voter awake at `v_s` has the view target of the
honest slot-`s` proposal's PC. -/
theorem recovery_commonView (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s)
    (ha : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon)
    (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
      (viewAt p c E rho y s).map (Option.map PC.target) = some (N.pc.map PC.target) := by
  have hd := p.deltaPos
  have hvg : SA.voteTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  exact pcsa_commonView_of_delivery E rho h.base hF s hs N hN
    (recovery_delivery_from_run E rho h s hs ha hh) hvg (hvg.trans hh)

end AvailableChain.PCSA.Run
end
