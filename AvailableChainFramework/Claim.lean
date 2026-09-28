module
public import AvailableChainFramework.Instance

@[expose] public section

namespace AvailableChain.Framework

open AvailableChain.Generic

/-- How a claim can be refuted. -/
inductive RefutationKind where
  /-- One finite run for one constant. -/
  | run
  /-- A parameterized family: no valid constant works. -/
  | family
  /-- The claim has no refutation form. -/
  | none
  deriving DecidableEq, Repr

/-- A catalog claim (design §4). `le k k'` means that `k'` is at least as
weak as `k`. `Point` holds the run parameters that the claim quantifies
over (for example `t₀`, or `T`, `b₀`, `b₁`). -/
structure ClaimSpec where
  id : Lean.Name
  Const : Type
  valid : Const → Prop
  le : Const → Const → Bool
  le_refl : ∀ k, le k k = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  Point : Type
  /-- The runs that the claim speaks about. -/
  regime : (I : Instance) → Const → (W : Validators) → Env W.V →
    Run W.V I.P → Point → Prop
  /-- What the claim states about such a run. -/
  conclusion : (I : Instance) → Const → (W : Validators) → Env W.V →
    Run W.V I.P → Point → Prop
  /-- The event that makes the claim non-vacuous in a run (design §5). -/
  trigger : (I : Instance) → Const → (W : Validators) → Env W.V →
    Run W.V I.P → Point → Prop
  /-- A weaker constant keeps the claim. A proof, not metadata. -/
  transport : ∀ (I : Instance) (k k' : Const), valid k → valid k' →
    le k k' = true →
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho x,
      regime I k W E rho x → conclusion I k W E rho x) →
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho x,
      regime I k' W E rho x → conclusion I k' W E rho x)
  refutable : RefutationKind

namespace ClaimSpec

/-- The claim holds for an instance at a constant. -/
def holds (c : ClaimSpec) (I : Instance) (k : c.Const) : Prop :=
  ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ rho x,
    c.regime I k W E rho x → c.conclusion I k W E rho x

/-- For every horizon bound, the regime has a run of the instance, with a
larger horizon, in which the trigger occurs (design §5). -/
def inhabited (c : ClaimSpec) (I : Instance) (k : c.Const) : Prop :=
  ∀ H : Time, ∃ (W : Validators) (E : Env W.V) (rho : Run W.V I.P) (x : c.Point),
    E.Δ = I.Δ ∧ H ≤ rho.horizon ∧ c.regime I k W E rho x ∧ c.trigger I k W E rho x

end ClaimSpec

end AvailableChain.Framework

end
