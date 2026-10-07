module
public import AvailableChainFGSAClaims.Statements.OutageContinuation

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- OUTPUT-DIRECT §§1–10. DC: INTENTIONAL; additive continuation companion.
The frozen finite outage claims retain their original contracts. -/
def OutageContinuationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool)
    (T b₀ b₁ ΔF : Time),
    OutageContinuationPrem p c fast E rho T b₀ b₁ ΔF →
      OutageContinuationConcl p c E rho T b₀

end AvailableChain.FGSA.Run
end
