module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.Reads

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- OUTPUT-DIRECT §1 (V). DC: INTENTIONAL; the pending lease must cover
restored HEADs. Time subtraction and remainder are integer operations. -/
def OutageLengthV (p : Params) (b₀ b₁ : Time) : Prop :=
  b₁ - b₀ + (b₀ - 6 * p.Δ) % (4 * p.Δ) ≤ L p

theorem OutageLengthV_def (p : Params) (b₀ b₁ : Time) :
    OutageLengthV p b₀ b₁ = (b₁ - b₀ + (b₀ - 6 * p.Δ) % (4 * p.Δ) ≤ L p) := rfl

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; Outage₂ with its budget replaced
by (V), plus full-run acceptance relay and restored participation.
There is no participation premise on [b₀,b₁). No slashing bound is assumed. -/
structure OutageContinuationPrem (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (fast : Bool) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (T b₀ b₁ ΔF : Time) : Prop where
  pre : HealthyPrefix₂ p c E rho b₀ ΔF
  sleepy : ∀ t, 0 ≤ t → t < b₀ →
    (awakeHonestIn E rho (t - p.η) t ∪ Gen.V2.Duty.faulty rho).card <
      2 * (Gen.V2.Duty.awakeHonest E rho t).card
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  lag : T + (if fast then 4 * p.Δ else L p - 3 * p.Δ) ≤ b₀
  lengthV : OutageLengthV p b₀ b₁
  fastPart : fast = true → ∀ t, 0 ≤ t → t < b₀ →
    (p.n + 1) / 2 ≤ (Gen.V2.Duty.awakeHonest E rho t).card
  sync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)
  gst : E.t_GST ≤ b₁
  partAfter : ∀ t, b₁ ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E rho t).card

/-- OUTPUT-DIRECT §§1,10. DC: INTENTIONAL; inclusive output persistence
through the horizon, including asleep receivers and horizon deliveries. -/
def OutageContinuationConcl (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (T b₀ : Time) : Prop :=
  ∀ x B, x ∈ rho.honest → Block.Preceq B (S_at p c E rho (timeIdx rho T) x) →
    ∀ y t, y ∈ rho.honest → b₀ ≤ t → t ≤ rho.horizon →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable y t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed y t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y)

end AvailableChain.FGSA.Run
end
