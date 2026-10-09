module
public import AvailableChainEngineV2.Conditions.DeliveryWindow

@[expose] public section

/-! Delivery conditions over v2 runs (plan 2a, Task 5). The texts of
`PartialSynchrony` and `HealthyPrefixDelivery` are the v1 texts
(`AvailableChainStatements/Generic/Conditions.lean`) over v2 runs: broadcast
of emitted objects, and relay of accepted objects (the receipt relay, plan 2a
D5), each with the exclusion exemption. There is no other forwarding rule. -/

namespace AvailableChain.V2

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- Broadcast and accepted-object relay complete after GST,
except for objects excluded by the receiver at the deadline.

The relay premise reads `processed` at the receiver after event `i`, and the
exemption reads `excludes` at the receiver at the deadline. With restarts,
both premises read the receiver's current epoch; restart regimes add a rejoin
condition (design E6). -/
structure PartialSynchrony (E : Generic.Env V) (rho : Run V P) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => max a E.t_GST + E.Δ) rho.horizon
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => max a E.t_GST + E.Δ) rho.horizon

/-- The same broadcast and relay guarantees on a finite healthy prefix, with the same exclusion.
With restarts, both premises read the receiver's current epoch; restart
regimes add a rejoin condition (design E6). -/
structure HealthyPrefixDelivery (E : Generic.Env V) (rho : Run V P) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => a + E.Δ) cut
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => a + E.Δ) cut

end AvailableChain.V2

end
