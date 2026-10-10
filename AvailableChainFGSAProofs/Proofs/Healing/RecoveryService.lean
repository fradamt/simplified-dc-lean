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

/-- Original emission supplies proposal transport without an acceptance-time rewrite.
The caller keeps the exact handler window and the receiver's finality exclusion. -/
theorem healing_emitted_proposal_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {v x : V} {s : Slot} {N : NamedProposal p.n} {freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s)))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E i)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s)
    (haf : SA.proposalTime p.toParams s + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hhandlers : ∀ j t, SA.proposalTime p.toParams s ≤ t →
      t < SA.proposalTime p.toParams s + p.Δ →
      rho.handlesAt E j x (ofWire p ⟨.proposer s, .proposal N⟩) t →
      (fgsa p c).wellFormed (ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      (fgsa p c).depsPresent (rho.stateBefore E j x)
        (ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      fgsaTimely p (rho.stateBefore E j x) (ofWire p ⟨.proposer s, .proposal N⟩))
    (hexclude : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.proposalTime p.toParams s + p.Δ) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      (SA.proposalTime p.toParams s) freeze x) := by
  have hd : (toWire p (ofWire p ⟨.proposer s, .proposal N⟩)).decode = some (.block s N) := by
    rw [toWire_ofWire]
    rfl
  exact healing_recovery_receiverService E rho hrec _ _ _ freeze x hx hgst
    (hgst.trans' E.t_GST_nonneg) le_rfl haf hfh (Or.inl ⟨v, hv, i, hi, hem⟩)
    (fgsa_historySafeAt_of_proposal x _ _ hd) hhandlers hexclude

/-- A fresh HEAD uses its original vote time and the receiver's action-cut epoch.
Its receipt proof replays HistorySafeAt from this exact emission. -/
theorem healing_fresh_head_service (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {v x : V} {s : Slot} {q : Fin p.n} {b : BlockId} {freeze : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s)))
    (hem : ofHead p ⟨.seat (.head s) q, b⟩ ∈ rho.emitsAt E i)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (haf : SA.voteTime p.toParams s + p.Δ ≤ freeze) (hfh : freeze ≤ rho.horizon)
    (hhandlers : ∀ j t, SA.voteTime p.toParams s ≤ t →
      t < SA.voteTime p.toParams s + p.Δ →
      rho.handlesAt E j x (ofHead p ⟨.seat (.head s) q, b⟩) t →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (rho.stateBefore E j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (rho.stateBefore E j x) (ofHead p ⟨.seat (.head s) q, b⟩))
    (hexclude : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    Nonempty (FreshHeadService E rho s q b freeze x) := by
  let dl := fun t => max t E.t_GST + p.Δ
  have hd : dl (SA.voteTime p.toParams s) = SA.voteTime p.toParams s + p.Δ :=
    congrArg (· + p.Δ) (max_eq_left hgst)
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta]
  have within := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ delay
  have ready := healing_recovery_readyTrigger E rho hrec.toRecovery₂ _ _ _
    (SA.voteTime p.toParams s + p.Δ) x hx hgst (haf.trans hfh)
    (Or.inl ⟨v, hv, i, hi, hem⟩)
  refine ⟨⟨dl, rho.horizon, within, hd.symm ▸ ready,
    hd.symm ▸ lt_add_of_pos_right _ p.deltaPos, hd.symm ▸ haf.trans hfh,
    hd.symm ▸ haf.trans hfh, hd.symm ▸ haf,
    healing_recovery_action_epoch hrec hx hgst _, hd.symm ▸ hhandlers,
    hd.symm ▸ hexclude⟩⟩

end AvailableChain.FGSA.Run
end
