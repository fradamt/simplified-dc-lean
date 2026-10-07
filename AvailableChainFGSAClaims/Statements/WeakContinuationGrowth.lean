module
public import AvailableChainFGSAClaims.Statements.WeakContinuationLive
public import AvailableChainFGSAClaims.Statements.FinalityApi

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- DC AgreesUntil, PrefixAgreement.lean:19–23: retained honest local traces.
INTENTIONAL: the endpoint is inclusive. Signed objects and local order agree.
The full seat map is fixed; input and awake agree only for retained validators.
Global event positions can differ between the two runs. -/
structure RetainedAgreesThrough₂ (E : Generic.Env V)
    (source : V2.D.Run V (fgsa p c)) (E' : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) : Prop where
  honest : rho.honest ⊆ source.honest
  gst : E'.t_GST = E.t_GST
  delta : E'.Δ = E.Δ
  seats : rho.seatOf = source.seatOf
  inputs : ∀ v ∈ rho.honest, ∀ t, t ≤ source.horizon →
    rho.input v t = source.input v t
  awake : ∀ v ∈ rho.honest, ∀ t, t ≤ source.horizon →
    E'.awake v t = E.awake v t
  events : ∀ v ∈ rho.honest,
    rho.events.filter (fun e => decide (e.node = v ∧ e.time ≤ source.horizon)) =
      source.events.filter (fun e => decide (e.node = v ∧ e.time ≤ source.horizon))

/-- DC fixed-prefix network duties; INTENTIONAL: keep source duties for
validators removed from the honest set. Broadcast and relay remain separate.
The relay guard reads the original source post-acceptance state, and both
obligations keep the original trigger and family deadline (review finding 1).
Earlier handling can satisfy either obligation. -/
structure PendingSourceDelivery₂ (E : Generic.Env V)
    (source : V2.D.Run V (fgsa p c)) (E' : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) : Prop where
  sourceBroadcast : ∀ v ∈ source.honest, ∀ o t,
    V2.D.Run.emits E source v o t → t ≤ source.horizon →
    ∀ w ∈ rho.honest,
    source.horizon < max t E.t_GST + fgsaDelay E'.Δ ΔF o →
    max t E.t_GST + fgsaDelay E'.Δ ΔF o ≤ rho.horizon →
    (fgsa p c).excludes
      (V2.D.Run.stateBeforeTime E' rho (max t E.t_GST + fgsaDelay E'.Δ ΔF o) w) o = false →
    ∃ t', t ≤ t' ∧ t' < max t E.t_GST + fgsaDelay E'.Δ ΔF o ∧
      ∃ j, V2.D.Run.handlesAt E' rho j w o t'
  sourceRelay : ∀ v ∈ source.honest, ∀ i o t,
    V2.D.Run.acceptsAt E source i v o t → t ≤ source.horizon →
    ∀ w ∈ rho.honest,
    (fgsa p c).processed (V2.D.Run.stateBefore E source (i + 1) w) o = false →
    source.horizon < max t E.t_GST + fgsaDelay E'.Δ ΔF o →
    max t E.t_GST + fgsaDelay E'.Δ ΔF o ≤ rho.horizon →
    (fgsa p c).excludes
      (V2.D.Run.stateBeforeTime E' rho (max t E.t_GST + fgsaDelay E'.Δ ΔF o) w) o = false →
    ∃ t', t ≤ t' ∧ t' < max t E.t_GST + fgsaDelay E'.Δ ΔF o ∧
      ∃ j, V2.D.Run.handlesAt E' rho j w o t'

/-- DC RecoveredBy.recovered: retained-set continuation with the existing
whole-run threshold-slashing premise. INTENTIONAL: pointwise SA participation
and family delays, as in CleanContinuation₂. There is no one-third bound,
finality-liveness premise, or assumed suffix invariant. An empty strict
suffix is permitted and needs a prefix-only proof. -/
structure CleanGrowthContinuation₂ (E : Generic.Env V)
    (source : V2.D.Run V (fgsa p c)) (E' : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) : Prop where
  base : Base₂ p c E' rho
  agrees : RetainedAgreesThrough₂ p c E source E' rho
  covered : source.horizon ≤ rho.horizon
  sync : Gen.V2.Duty.PartialSynchronyBy E' rho (fgsaDelay E'.Δ ΔF)
  pending : PendingSourceDelivery₂ p c E source E' rho ΔF
  deltaF : E'.Δ ≤ ΔF
  accountable : FinalitySlashableBound p c E' rho
  participation : ∀ t, source.horizon < t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E' rho t).card

/-- DC bounded safety recovery: one source witness precedes all continuations.
INTENTIONAL: each continuation has its own completed-gate index. The result
keeps compatibility, monotonicity, seed preservation, finalBelow, both outputs,
inclusion, and conditional available growth. It asserts no finality liveness.
The source keeps its original one-third bound. -/
def BoundedGrowthRecovery₂ (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R →
  ∀ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)),
    StrongRecoverySearchPrefix₂ p c E source G ΔF →
    ∃ (u : Slot) (Q : Block) (iSource : Nat),
      BoundedHealingCut₂ p c E source u Q iSource ΔF ∧
      ∀ (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        CleanGrowthContinuation₂ p c E source E' rho ΔF →
        WeakContinuationLiveAt₂ p c E' rho u Q
          (afterTicksIdx rho (SA.gateTime p.toParams u)) ΔF

/-- Home equation for the additive retained-set claim. -/
theorem BoundedGrowthRecovery₂_def (G ΔF : Time) :
    BoundedGrowthRecovery₂ p (V := V) c G ΔF =
      (p.δt = 2 * p.R →
      ∀ (E : Generic.Env V) (source : V2.D.Run V (fgsa p c)),
        StrongRecoverySearchPrefix₂ p c E source G ΔF →
        ∃ (u : Slot) (Q : Block) (iSource : Nat),
          BoundedHealingCut₂ p c E source u Q iSource ΔF ∧
          ∀ (E' : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
            CleanGrowthContinuation₂ p c E source E' rho ΔF →
            WeakContinuationLiveAt₂ p c E' rho u Q
              (afterTicksIdx rho (SA.gateTime p.toParams u)) ΔF) := rfl

end AvailableChain.FGSA.Run
end
