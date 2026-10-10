module
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}

/-- An original proposal acceptance gives receiver service in the recovery epoch.
The acceptance keeps its source index and time. The local anchor can be later.
Proposal history is durable; the receiver epoch extends through its freeze. -/
theorem healing_accepted_proposal_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {k : Nat} {v x : V} {s : Slot} {N : NamedProposal p.n} {send a freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hacc : V2.D.Run.acceptsAt E rho k v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (ha : 0 ≤ a) (hpub : V2.PublicTime E a)
    (hgst : E.t_GST ≤ a) (haf : a + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hexclude : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send freeze x) := by
  have hd : (toWire p (ofWire p ⟨.proposer s, .proposal N⟩)).decode = some (.block s N) := by
    rw [toWire_ofWire]
    rfl
  have had : a < a + p.Δ := lt_add_of_pos_right a p.deltaPos
  have hh : a + p.Δ ≤ rho.horizon := haf.trans hfh
  have handlers := fgsa_proposal_handlers_at_anchor hrec.base.valid hrec.base.delta hx
    hd hacc hsa ha hpub (hrec.awake x hx a hgst (had.le.trans hh)) had hh
    (healing_recovery_action_epoch hrec hx hgst _)
  exact healing_recovery_receiverService E rho hrec _ send a freeze x hx hgst ha hsa haf hfh
    (Or.inr ⟨v, hv, k, hacc⟩) (fgsa_historySafeAt_of_proposal x _ a hd) handlers hexclude

/-- Accepted proposal service supplies the exact target, with its original acceptance. -/
theorem healing_accepted_target_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {k : Nat} {v x : V} {s : Slot} {N : NamedProposal p.n} {send a freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hacc : V2.D.Run.acceptsAt E rho k v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (ha : 0 ≤ a) (hpub : V2.PublicTime E a)
    (hgst : E.t_GST ≤ a) (haf : a + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hexclude : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    TargetReceiptService E rho N.erase freeze x :=
  fgsa_target_service_of_proposal E rho s N send freeze x
    (healing_accepted_proposal_service hrec hv hx hacc hsa ha hpub hgst haf hfh hexclude)

end AvailableChain.FGSA.Run
end
