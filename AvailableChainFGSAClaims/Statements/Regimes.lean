module
public import AvailableChainFGSAClaims.Statements.Counts
public import AvailableChainGeneric.Statements.V2.Duty.Counts
public import AvailableChainFGSAClaims.Statements.Bounds
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

@[expose] public section

namespace AvailableChain.FGSA.Run

open Gen.Pure
open Gen.V2.Duty (faulty awakeHonest HonestSlot)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

structure Base₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  valid : V2.D.ExecutionValid E rho
  linked : V2.D.Linked (fgsaFamilies p c).linked rho
  cstar : V2.D.CStar (fgsaFamilies p c).fresh rho
  noRestart : V2.D.NoRestart rho
  delta : E.Δ = p.Δ

/-- Per-object delivery regime.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure HealthyPrefix₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop where
  base : Base₂ p c E rho
  cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon
  healthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀
  deltaF : E.Δ ≤ ΔF
  partBefore : ∀ t : Time, 0 ≤ t → t < b₀ → (faulty rho).card < (awakeHonest E rho t).card

/-- Per-object delivery regime.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure CleanPrefix₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop extends HealthyPrefix₂ p c E rho b₀ ΔF where
  partAt : (faulty rho).card < (awakeHonest E rho b₀).card

/-- The blueprint cut has no participation premise at the cut and no quorum field.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
abbrev CleanCut₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop :=
  HealthyPrefix₂ p c E rho b₀ ΔF

/-- Per-object delivery regime.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure Clean₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time := E.Δ) : Prop where
  pre : CleanPrefix₂ p c E rho rho.horizon ΔF
  gst : E.t_GST = 0

/-- Recovery has neither a delta-ratio premise nor a recurrence field.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure Recovery₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    (ΔF : Time := E.Δ) : Prop where
  sync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)
  deltaF : E.Δ ≤ ΔF
  gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
    ∃ s, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      V2.D.proposalTime (fgsaInterface p c) s ≤ t + G ∧
      HonestSlot rho (fgsaInterface p c) s
  base : Base₂ p c E rho
  fault : (faulty rho).card ≤ (p.n - 1) / 3
  awake : ∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake v t = true
  gapPos : 4 * p.Δ ≤ G

abbrev BaseSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop := Base₂ p c E rho
abbrev CleanSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time := E.Δ) : Prop := Clean₂ p c E rho ΔF
abbrev CleanCutSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop :=
  CleanCut₂ p c E rho b₀ ΔF
abbrev CleanPrefixSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop :=
  CleanPrefix₂ p c E rho b₀ ΔF
abbrev HealingSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) : Prop :=
  Recovery₂ p c E rho G

structure FinalitySet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (form : FinForm) (g : Nat) : Prop where
  core : Recovery₂ p c E rho G
  recur : form.holds (HonestSlot rho (fgsaInterface p c)) p.R (P p) p.Δ E.t_GST rho.horizon g

/-- Final outage fields for G-F0a. Participation is strict before the cut;
the sleep witness is in `outWin`. -/
structure Outage₂ (fast : Bool) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (T b₀ b₁ : Time) : Prop where
  pre : HealthyPrefix₂ p c E rho b₀
  sleepy : ∀ t, 0 ≤ t → t < b₀ →
    (awakeHonestIn E rho (t - p.η) t ∪ faulty rho).card < 2 * (awakeHonest E rho t).card
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  lag : T + (if fast then 4 * p.Δ else L p - 3 * p.Δ) ≤ b₀
  budget : b₁ - b₀ ≤ min p.η (L p)
  fastPart : fast = true → ∀ t, 0 ≤ t → t < b₀ →
    (p.n + 1) / 2 ≤ (awakeHonest E rho t).card

abbrev OutageSet (fast : Bool) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (T b₀ b₁ : Time) : Prop := Outage₂ p c fast E rho T b₀ b₁

end AvailableChain.FGSA.Run
end
