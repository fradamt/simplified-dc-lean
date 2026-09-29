module
public import AvailableChainGeneric.Statements.V2.Receipt
public import AvailableChainEngineV2.Conditions.Delivery

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

-- GLY:1166–1167; Delivery.lean:25–38 supplies the same two fields.
theorem deliveryWithin_of_partialSynchrony (h : PartialSynchrony E rho) :
    DeliveryWithin E rho (fun t => max t E.t_GST + E.Δ) rho.horizon :=
  ⟨h.broadcast, h.relay⟩

-- GLY:1168–1169; Delivery.lean:43–56 supplies the same two fields.
theorem deliveryWithin_of_healthyPrefix (b₀ : Time) (h : HealthyPrefixDelivery E rho b₀) :
    DeliveryWithin E rho (fun t => t + E.Δ) b₀ :=
  ⟨h.broadcast, h.relay⟩

end AvailableChain.Gen.V2
