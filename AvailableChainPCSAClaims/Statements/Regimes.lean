module
public import AvailableChainEngineV2.Conditions.Duty.Schedule
public import AvailableChainEngineV2.Conditions.Duty.Committees
public import AvailableChainGeneric.Statements.V2.Duty.Counts
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy
public import AvailableChainPCSARun.Model.Families
public import AvailableChainPCSARun.Statements.Roots
public import AvailableChainPCSARun.Statements.Interface

@[expose] public section

/-! [PC-SA claims; FG-SA Claims/Statements/Regimes.lean] The run regimes of
the PC-SA claims. `Base₂` carries the root collision freedom premise
(`NamedRootCollisionFree`, review C1); `FGSafetyBound` is the FG safety
fault bound `a ≤ (n − 1)/3` (review C2). -/

namespace AvailableChain.PCSA.Run

open Gen.V2.Duty (faulty awakeHonest)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- [PC-SA claims; FG-SA Base₂] A valid execution with linked FG seats, fresh
HEAD and ack committees, no restart, the model delay, and root collision
freedom. -/
structure Base₂ (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) : Prop where
  valid : V2.D.ExecutionValid E rho
  linked : V2.D.Linked (pcsaFamilies p c).linked rho
  cstar : V2.D.CStar (pcsaFamilies p c).fresh rho
  noRestart : V2.D.NoRestart rho
  delta : E.Δ = p.Δ
  /-- [review C1; DC NamedRootCollisionFree] Run body collision freedom: without
  it a constant digest lets two honest nodes hold different slot-`s` blocks
  with one root, and the acks on that root form PCs on different targets. -/
  idealization : NamedRootCollisionFree p c E rho

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
faulty seats, so every PC has an honest acker.
Implied by `FGSafetyBound` for n ≥ 1; kept for when the proof phase drops `FGSafetyBound`. -/
def FaultsBelowQA (rho : V2.D.Run V (pcsa p c)) : Prop :=
  (faulty rho).card < pcQuorum p.n

theorem FaultsBelowQA_def (rho : V2.D.Run V (pcsa p c)) :
    FaultsBelowQA p c rho = ((faulty rho).card < pcQuorum p.n) := by
  rw [FaultsBelowQA]

/-- [PC-SA claims; review C2; FG-SA AcceptPrem_W.faultBound] The FG safety
fault bound `a ≤ f = (n − 1)/3`.
a ≤ f is the stage-2 CLEAN premise of r4.2 §5.0; with it,
CI(vi) (reconcile drops no PC) gives F-compatibility of PC targets.
The proof phase may remove it (FG-SA's clean claims have no a ≤ f). -/
def FGSafetyBound (rho : V2.D.Run V (pcsa p c)) : Prop :=
  (faulty rho).card ≤ (p.n - 1) / 3

theorem FGSafetyBound_def (rho : V2.D.Run V (pcsa p c)) :
    FGSafetyBound p c rho = ((faulty rho).card ≤ (p.n - 1) / 3) := by
  rw [FGSafetyBound]

/-! ### Lane regimes (W0; pcsa34-r4 5.0, 1.1)

The stage-1 claims read `StageOneFrame`; the stage-2 claims drop it and add
their frame premises (pcsa-proof-plan §1, C15). The fault bounds are separate
premises, as r4.3 §1.1 states them per claim: `FaultsBelowQA` is
`a < ⌈n/2⌉`, `QuarterCap` is `a ≤ ⌊n/4⌋`, `FGSafetyBound` is `a ≤ f`. -/

/-- [PC-SA claims, W0; pcsa34-r4 1.1] The PC fault bound of formation,
inclusion into strong and PC healing: `a ≤ ⌊n/4⌋`, so `n − a ≥ q_N`
(`4a ≤ n`, as `PCIncludedRegime.quarterCap`). -/
def QuarterCap (rho : V2.D.Run V (pcsa p c)) : Prop :=
  4 * (faulty rho).card ≤ p.n

theorem QuarterCap_def (rho : V2.D.Run V (pcsa p c)) :
    QuarterCap p c rho = (4 * (faulty rho).card ≤ p.n) := by
  rw [QuarterCap]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.2 (vi), 5.3 (F6)/(F7)] The frame of a
store is vacuous: `F` and the FG root `Z` are genesis and the band floor `lo`
is `0`. Then the full filtered tree is the whole tree `Σ.T`, every usable PC
is frame-active, no block is below `lo`, and every block is `F`-compatible. -/
def FrameVacuous (st : State p.n) : Prop :=
  st.fg.F = .genesis ∧ (controls p st).Z = .genesis ∧ (controls p st).lo = 0

theorem FrameVacuous_def (st : State p.n) :
    FrameVacuous p st =
      (st.fg.F = .genesis ∧ (controls p st).Z = .genesis ∧ (controls p st).lo = 0) := by
  rw [FrameVacuous]

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa-proof-plan §1 (stage 1); pcsa34-r4 5.2.2 (vi),
5.3 (F6)/(F7), 5.4.1] The stage-1 frame premise: at every honest node and
every event state the frame is vacuous. r4.3 states the stage-1 claims for a
protocol whose frame items are vacuous; the Lean model computes the frame from
the FG store, so the stage-1 claims take this run premise. -/
def StageOneFrame (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) : Prop :=
  ∀ x ∈ rho.honest, ∀ i : Nat, FrameVacuous p (V2.D.Run.stateBefore E rho i x).st

omit [Fintype V] in
theorem StageOneFrame_def (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) :
    StageOneFrame p c E rho =
      (∀ x ∈ rho.honest, ∀ i : Nat, FrameVacuous p (V2.D.Run.stateBefore E rho i x).st) := by
  rw [StageOneFrame]

/-- [PC-SA claims, W0; pcsa34-r4 1.3] The slow lease lifetime `L = (4k − 1)Δ`. -/
def pcsaL (p : Params) : Time := (4 * (p.k : Time) - 1) * p.Δ

theorem pcsaL_def (p : Params) : pcsaL p = (4 * (p.k : Time) - 1) * p.Δ := rfl

omit [Fintype V] in
/-- [PC-SA claims, W0; FG-SA awakeHonestIn] The honest nodes awake at some
time in the closed interval `[a, b]`. -/
noncomputable def pcsa_awakeHonestIn (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))
    (a b : Time) : Finset V := by
  classical
  exact rho.honest.filter (fun v => ∃ t, a ≤ t ∧ t ≤ b ∧ E.awake v t = true)

/-- [PC-SA claims, W0; pcsa34-r4 5.0 OUTAGE(T, b₀, b₁); FG-SA Outage₂ with
`fast = false`] CLEAN(b₀) (`HealthyPrefix₂`), the η sleepiness condition
before the cut (FG-SA `Outage₂.sleepy`, the meaning of η), the slow arming lag
`T + 4(k − 1)Δ ≤ b₀`, and the budget `b₁ − b₀ ≤ min(η, L)`. Delivery in
`[b₀, b₁)` is arbitrary. There is no fast route. -/
structure Outage₂ (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))
    (T b₀ b₁ : Time) (ΔF : Time := E.Δ) : Prop where
  pre : HealthyPrefix₂ p c E rho b₀ ΔF
  sleepy : ∀ t, 0 ≤ t → t < b₀ →
    (pcsa_awakeHonestIn p c E rho (t - p.η) t ∪ faulty rho).card <
      2 * (awakeHonest E rho t).card
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  lag : T + 4 * ((p.k : Time) - 1) * p.Δ ≤ b₀
  budget : b₁ - b₀ ≤ min p.η (pcsaL p)

/-- [PC-SA claims, W0; pcsa34-r4 5.0 RECOVERY; FG-SA Recovery₂] Arbitrary
delivery before `t_GST`; after it strict delivery within `Δ` (rows `Δ_F`),
every honest node awake, an honest proposer in every window `(t, t + G]`
(`t ≥ t_GST`, awake by `awake`), `G ≥ 4Δ`, and the PC fault cap
`a ≤ ⌊n/4⌋` (stage 2 adds `a ≤ f`). -/
structure Recovery₂ (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (G : Time)
    (ΔF : Time := E.Δ) : Prop where
  base : Base₂ p c E rho
  sync : Gen.V2.Duty.PartialSynchronyBy E rho (pcsaDelay p E.Δ ΔF)
  deltaF : E.Δ ≤ ΔF
  awake : Gen.V2.Duty.FullParticipation E rho E.t_GST
  gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
    ∃ s, t < V2.D.proposalTime (pcsaInterface p c).toInterface s ∧
      V2.D.proposalTime (pcsaInterface p c).toInterface s ≤ t + G ∧
      Gen.V2.Duty.HonestSlot rho (pcsaInterface p c).toInterface s
  quarterCap : QuarterCap p c rho
  gapPos : 4 * p.Δ ≤ G

end AvailableChain.PCSA.Run
end
