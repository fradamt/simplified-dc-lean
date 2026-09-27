module
public import AvailableChainSA.Model.Protocol
public import AvailableChainStatements.Generic.Claims

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic

def saInterface (p : Params) : Interface (sa p) where
  confirmed := confirmed
  stable := stable
  block := block
  opening := fun _ => True

def saConstants (p : Params) (G : Time) : Constants where
  θ := 1 / 2
  θrec := 1 / 2
  recoveryFull := false
  η := p.η
  D_c := 6 * p.Δ
  D_s := 6 * p.Δ
  D_f := 6 * p.Δ
  armingLag := 4 * ((p.k : Time) - 1) * p.Δ
  budget := min p.η (lifetime p)
  recoveryBound := 2 * lifetime p + G + 8 * p.Δ
  proposerGap := G

/-- The extra fast P1 claim changes only the arming lag. -/
def saFastConstants (p : Params) (G : Time) : Constants :=
  { saConstants p G with armingLag := 4 * p.Δ }

/-- The complete fixed Draft 4.2 bundle, with no extra run premises. -/
def SAContract {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) : Prop :=
  E.Δ = p.Δ ∧ AvailableChain (sa p) E (saInterface p) (saConstants p G)

/-- Honest awake counts are high throughout the healthy prefix, including
all times before the protected read. Received turnout is not this premise. -/
def HighParticipationBefore {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (b₀ : Time) : Prop :=
  ∀ t, 0 ≤ t → t < b₀ → releaseThreshold p ≤ (awakeAt E rho.honest t).card

/-- Extra public claim; the fixed contract has no field for fast P1. -/
def FastP1 {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) : Prop :=
  ∀ (rho : Run V (sa p)) T b₀ b₁,
    OutageRegime (sa p) E (saInterface p) (saFastConstants p G) rho T b₀ b₁ →
    HighParticipationBefore p E rho b₀ →
    PersistsThrough (sa p) rho (saInterface p).stable T b₀ b₁

end AvailableChain.SA
end
