module
public import AvailableChainEngineV2.Conditions.Duty.Schedule
public import AvailableChainEngineV2.Conditions.Duty.Committees
public import AvailableChainGeneric.Statements.V2.Duty.Counts
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy
public import AvailableChainPCSARun.Model.Families

@[expose] public section

/-! [PC-SA claims; FG-SA Claims/Statements/Regimes.lean] The run regimes of
the PC-SA claims. `Base₂` has no `idealization` field yet: the PC-SA run
statement of root collision freedom (FG-SA `NamedRootCollisionFree`) is not
ported in M1. -/

namespace AvailableChain.PCSA.Run

open Gen.V2.Duty (faulty awakeHonest)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- [PC-SA claims; FG-SA Base₂] A valid execution with linked FG seats, fresh
HEAD and ack committees, no restart, and the model delay. -/
structure Base₂ (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) : Prop where
  valid : V2.D.ExecutionValid E rho
  linked : V2.D.Linked (pcsaFamilies p c).linked rho
  cstar : V2.D.CStar (pcsaFamilies p c).fresh rho
  noRestart : V2.D.NoRestart rho
  delta : E.Δ = p.Δ

/-- [PC-SA claims; FG-SA fgsaDelay] Per-object delivery delay: rows `ΔF`,
every other object (HEAD, proposal, ack, PC) `Δ`. -/
def pcsaDelay (Δ ΔF : Time) (o : Obj p) : Time :=
  match o.payload with
  | .row _ => ΔF
  | _ => Δ

theorem pcsaDelay_def (Δ ΔF : Time) (o : Obj p) :
    pcsaDelay p Δ ΔF o = (match o.payload with | .row _ => ΔF | _ => Δ) := rfl

/-- [PC-SA claims; FG-SA HealthyPrefix₂] Healthy delivery before the cut `b₀`
(rows within `ΔF`, other objects within `Δ`), with an honest awake majority
before the cut. -/
structure HealthyPrefix₂ (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop where
  base : Base₂ p c E rho
  cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon
  healthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) b₀
  deltaF : E.Δ ≤ ΔF
  partBefore : ∀ t : Time, 0 ≤ t → t < b₀ → (faulty rho).card < (awakeHonest E rho t).card

/-- [PC-SA claims; pcsa34-r3 5.1] The PC fault premise: fewer than `q_A`
faulty seats, so every PC has an honest acker. -/
def FaultsBelowQA (rho : V2.D.Run V (pcsa p c)) : Prop :=
  (faulty rho).card < pcQuorum p.n

theorem FaultsBelowQA_def (rho : V2.D.Run V (pcsa p c)) :
    FaultsBelowQA p c rho = ((faulty rho).card < pcQuorum p.n) := by
  rw [FaultsBelowQA]

end AvailableChain.PCSA.Run
end
