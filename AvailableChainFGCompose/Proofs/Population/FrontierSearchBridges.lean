module
public import AvailableChainFGCompose.Statements.Population.FrontierSearch
public import AvailableChainFGCompose.Proofs.Population.PromotionBridges

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair) (Jst : Time) (leaseSlots deltaT : Nat)
variable (e : Fin n ≃ V) (he : ∀ i, safetyHolder S rho i = e i)

include e he

/-- Iff: frozen all-holder coverage reindexes only the opening rows. -/
theorem frontierLocalServiceFG_frozen_iff (q : Slot) (Q : Block) (Qfg : FGBlock (Fin n))
    (m : Nat) (v : Time) :
    FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m v ↔
      FrontierLocalService R S E rho O T I pair q Q Qfg m v := by
  simp only [FrontierLocalServiceFG_def, FrontierLocalService,
    openingCoveredFG_frozen_iff R S E rho O.height T pair e he]

end AvailableChain.FGCompose
end
