module
public import AvailableChainGeneric.Statements.V2.Receipt
public import AvailableChainGeneric.Statements.V2.Reads
public import AvailableChainGeneric.Statements.Pure.Quorum
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainEngineV2.Conditions.Interface
public import AvailableChainEngineV2.Conditions.Schedule
public import Mathlib.Order.Monotone.Basic

@[expose] public section

/-! Sources: GLY is `claude-files/a0/generic-layer.md` r3.13.
P3 is `fgsa-f0-f2-plan-r3.5-2a9a5877.md`.
Step-2 items I06 and the regime part of I25; rulings D05 and D17.
The core designs retain the V2 fields of the P3 regimes. -/

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- GLY:1558–1561, verbatim.
def LabelSync (E : Generic.Env V) (rho : Run V P) (vt dt : Time) : Prop :=
  ∃ dl cut, DeliveryWithin E rho dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧
    (∀ t, dl t ≤ max t vt + E.Δ) ∧          -- syncFrom: Δ-synchrony from vt
    vt + E.Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ rho.horizon

-- GLY:1558–1561; equation export required by BUILD §7.2 B3a.
theorem LabelSync_def (E : Generic.Env V) (rho : Run V P) (vt dt : Time) :
    LabelSync E rho vt dt =
      (∃ dl cut, DeliveryWithin E rho dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧
        (∀ t, dl t ≤ max t vt + E.Δ) ∧
        vt + E.Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ rho.horizon) := by
  rw [LabelSync]

-- GLY:1562–1564, verbatim; Batch is the D05 one-field structure.
structure LabelFacts (E : Generic.Env V) (rho : Run V P) (vt dt : Time) (h m : Nat) : Prop where
  sync  : LabelSync E rho vt dt
  batch : Batch h m          -- the honest count at vt (S3 §2.2)

/-- DESIGNED from P3:1581–1586 for `Base₂`.
The instance adds its seat conditions and its time-unit equation. -/
structure BaseCore (E : Generic.Env V) (rho : Run V P) : Prop where
  valid : ExecutionValid E rho
  noRestart : NoRestart rho

/-- DESIGNED from P3:1590–1594 for `HealthyPrefix₂`.
This record contains only the healthy delivery field. -/
structure HealthyCore (E : Generic.Env V) (rho : Run V P) (b₀ : Time) : Prop where
  healthy : HealthyPrefixDelivery E rho b₀

/-- DESIGNED from GLY:727–729 and P3:1590–1616 for `CleanCut₂`,
which is `HealthyPrefix₂`. The instance adds its base and participation.
There is no quorum field or participation premise at the cut. -/
structure CutCore (E : Generic.Env V) (rho : Run V P) (b₀ : Time) : Prop
    extends HealthyCore E rho b₀ where
  cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon

/-- DESIGNED from P3:1633–1641 for `Outage₂`.
The instance adds its healthy prefix, lag, budget and participation fields.
Its stronger `pre` field can retain its name when it extends this core. -/
structure OutageCore (rho : Run V P) (T b₀ b₁ : Time) : Prop where
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon

-- GLY:1641–1646; SYN docs/LEAN-ARCHITECTURE.md:631–637;
-- P3:1699–1710. Recovery₂ adds base, fault, awake and gapPos.
structure RecoveryCore {In : Type} (P : ProtocolSpec In) (I : Interface P)
    (E : Generic.Env V) (rho : Run V P) (G : Time) : Prop where
  sync : PartialSynchrony E rho
  gap  : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
           ∃ s, t < proposalTime I s ∧ proposalTime I s ≤ t + G ∧ HonestSlot rho I s

/-- DESIGNED from GLY:860–863,1022–1023,2165 (F-16).
At event index `start`, each honest node satisfies its state predicate.
The environment is implicit so the explicit arguments are `rho start Q`.
This record stores the start condition; preservation is a separate premise. -/
structure SeedAt {E : Generic.Env V} (rho : Run V P) (start : Nat)
    (Q : V → P.State → Prop) : Prop where
  holds : ∀ v ∈ rho.honest, Q v (Run.stateBefore E rho start v)

end AvailableChain.Gen.V2
