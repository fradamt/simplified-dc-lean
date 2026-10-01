module
public import AvailableChainEngineV2.Engine.Duty.Run

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

structure PartialSynchrony (E : Generic.Env V) (rho : Run V P) : Prop where
  broadcast_emitted : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
      max t E.t_GST + E.Δ ≤ rho.horizon →
        P.excludes (Run.stateBeforeTime E rho (max t E.t_GST + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
          ∃ j, Run.handlesAt E rho j w o t'
  relay_accepted : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
      P.processed (Run.stateBefore E rho (i + 1) w) o = false →
        max t E.t_GST + E.Δ ≤ rho.horizon →
        P.excludes (Run.stateBeforeTime E rho (max t E.t_GST + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
            ∃ j, Run.handlesAt E rho j w o t'

structure HealthyPrefixDelivery (E : Generic.Env V) (rho : Run V P) (cut : Time) : Prop where
  broadcast_emitted : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
      t + E.Δ ≤ cut →
        P.excludes (Run.stateBeforeTime E rho (t + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
          ∃ j, Run.handlesAt E rho j w o t'
  relay_accepted : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
      P.processed (Run.stateBefore E rho (i + 1) w) o = false →
        t + E.Δ ≤ cut →
        P.excludes (Run.stateBeforeTime E rho (t + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
            ∃ j, Run.handlesAt E rho j w o t'

end AvailableChain.V2.D

end
