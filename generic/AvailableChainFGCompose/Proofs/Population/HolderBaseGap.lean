module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchAge
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair

public section

/-! Blueprint 21 HG.3 gap. The repair allowance is the published local repair service.
The proposer floor, the held gate copy, the continuing local service and the common
opening of a seed-qualified proposal are explicit leaves; the age service is the
generic d5b consumer with its own leaves. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (Jst : Time) (leaseSlots : Nat)
variable (obs : FGObservationLaws R O) (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

/-- Blueprint 21 HG.3. DC: SAME period bound for the first opening. -/
theorem frontierSearch_period_bound_core (hT : FGTimingLaws T) : 8 * T.delta ≤ FGCompose.P T := by
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast hT.rounds
  change 8 * T.delta ≤ 4 * (T.roundSlots : Time) * T.delta
  nlinarith [hT.delta_pos]

end AvailableChain.FGCompose
end
