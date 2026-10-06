module
public import AvailableChainPCSAClaims.Claims.PC
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Foundations.Run

public section

/-! Small PC claim exports (pcsa34-r4.3 §3.2, A6; proof plan C2, C4). -/

namespace AvailableChain.PCSA.Run

/-- C2: an honest seat emits one ack root, at the slot's early time. -/
theorem pcsa_oneAckPerSlot (p : Params) : OneAckPerSlotClaim p := by
  intro V _ _ In c m E rho hv x _ s i r r' t t' h h'
  exact ack_emission_unique p c m E rho hv.nodup x s i r r' t t' h h'

/-- C4: strong and finalized outputs are below the available output. -/
theorem pcsa_outputNesting (p : Params) : OutputNestingClaim p := by
  intro V _ _ In c m E rho _ x _ t
  exact reachable_outputNesting p _ (reachable_storeAt E rho t x)

end AvailableChain.PCSA.Run
end
