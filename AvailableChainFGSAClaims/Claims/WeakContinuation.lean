module
public import AvailableChainFGSAClaims.Statements.WeakContinuation

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- Additive claim for DC NamedVoteConsumers:56-61, with the intentional
FG-SA differences stated in BoundedSafetyRecovery₂. Like HTimeStatement,
this claim quantifies the validator and input types and the application codec.
ΔF is universal and explicit, with no default.
It states safety only; it does not replace HealingInput or finality liveness. -/
def WeakContinuationClaim (p : Params) (G : Time) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In) (ΔF : Time),
    BoundedSafetyRecovery₂ p (V := V) c G ΔF

end AvailableChain.FGSA.Run
end
