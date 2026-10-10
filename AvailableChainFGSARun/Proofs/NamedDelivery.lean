module
public import AvailableChainFGSARun.Proofs.NamedOrigins
public import AvailableChainFGSARun.Proofs.NamedHistory
public import AvailableChainFGSARun.Proofs.Reachable

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

-- W3 integration: these delivery-bound consumers retain their original contracts.
/-- [ROOT-DIGEST-2 W1; DC NamedReceiptCalls] Broadcast or source acceptance scopes a trigger.
This proof uses no root idealization or processed-to-body inference. -/
theorem proposal_trigger_in_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (_hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (_hw : w ∈ rho.honest)
    (_hcut : dl t ≤ cut)
    (_hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false)
    (hService : V2.D.DeliveryService E rho w o t (dl t))
    (hHistory : V2.D.ProcessedByActionCut E rho w o t → NamedProposalInRun p c E rho N) :
    NamedProposalInRun p c E rho N := by
  rcases hT with ⟨_, _, _⟩ | ⟨v, _, i, haccept⟩
  · rcases hService with hh | ⟨t', _, _, j, hh⟩
    · exact hHistory hh
    · exact proposal_handle_in_scope E rho o s N ho j w t' hh
  · exact proposal_handle_in_scope E rho o s N ho i v t haccept.1

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Trigger scope retains the Block projection. -/
theorem proposal_trigger_in_root_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (_hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (_hw : w ∈ rho.honest)
    (_hcut : dl t ≤ cut)
    (_hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false)
    (hService : V2.D.DeliveryService E rho w o t (dl t))
    (hHistory : V2.D.ProcessedByActionCut E rho w o t → NamedProposalInRun p c E rho N) :
    RootBlockInRun p c E rho N.erase :=
  ⟨N, proposal_trigger_in_scope E rho o s N ho dl cut t w _hD hT _hw _hcut _hNX
    hService hHistory, rfl⟩


end AvailableChain.FGSA.Run
end
