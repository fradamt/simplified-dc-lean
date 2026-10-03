module
public import AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival -- shake: keep (HTIME tests)

public section

/-! Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W2–W4.
DC: SAME HTimeClaim and its original run package, with four exact open inputs. -/

namespace AvailableChain.FGSA.Run.Tests.HealingHTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME claim type with only the statement producer as a hypothetical input. -/
example (p : Params) (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p :=
  healing_hTimeClaim_of_statement p hTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME witness and chained bound after the package is applied to a run. -/
example (p : Params) (hTime : ∀ G ΔF, HTimeStatement p G ΔF)
    (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_statement p hTime G ΔF hClock c E rho () h

#check healing_hTimeClaim_of_statement
#print axioms healing_hTimeClaim_of_statement

section OpenInputs
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (hcone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      PostResetRetainedCone p c E rho w)

include stepRL stepLease stepRaw hcone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W2.
DC: SAME full reset statement with the four future producers as hypotheses. -/
example (G ΔF : Time) : ResetArrivalFullStatement p G ΔF :=
  healing_resetArrivalFull_of_open p stepRL stepLease stepRaw hcone G ΔF

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W4.
DC: SAME literal HTimeClaim conclusion with only the four open inputs. -/
example : HTimeClaim p :=
  healing_hTimeClaim_of_open p stepRL stepLease stepRaw hcone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W4.
DC: SAME witness and both time bounds after W4 is applied to a healing run. -/
example (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_open p stepRL stepLease stepRaw hcone G ΔF hClock c E rho () h

end OpenInputs

#check healing_resetArrivalFull_of_open
#check healing_hTimeClaim_of_open
#print axioms healing_hTimeClaim_of_open

section OpenInputs₂
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (stepCone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetConeStep p c E rho w i)

include stepRL stepLease stepRaw stepCone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 T/W2.
DC: SAME full reset statement with the four future producers as hypotheses. -/
example (G ΔF : Time) : ResetArrivalFullStatement p G ΔF :=
  healing_resetArrivalFull_of_open₂ p stepRL stepLease stepRaw stepCone G ΔF

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 T/W4.
DC: SAME literal HTimeClaim conclusion with only the four open inputs. -/
example : HTimeClaim p :=
  healing_hTimeClaim_of_open₂ p stepRL stepLease stepRaw stepCone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 T/W4.
DC: SAME witness and both time bounds after W4 is applied to a healing run. -/
example (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_open₂ p stepRL stepLease stepRaw stepCone G ΔF hClock c E rho () h

end OpenInputs₂

#check healing_resetArrivalFull_of_open₂
#check healing_hTimeClaim_of_open₂
#print axioms healing_resetArrivalFull_of_open₂
#print axioms healing_hTimeClaim_of_open₂

end AvailableChain.FGSA.Run.Tests.HealingHTime
end
