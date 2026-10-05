module
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptRows -- shake: keep (complete row lane)

public section

namespace AvailableChain.FGSA.Run

/-! Blueprint 21 H.10. AttemptSettle supplies settlement for either start arm.
AttemptRows supplies all four complete rows with standing ports and exact
INLINE facts. The conditional assembly keeps the four row facts as explicit
hypotheses. The lane assembly below applies the four proved rows. -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Conditional assembly of the four frozen attempt-budget rows. -/
theorem healing_progressAttempt_of (p : Params) (G ΔF : Time)
    (raise_contest : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .raise → k.phase = .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    (raise_other : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .raise → k.phase ≠ .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    (firstRow_contest : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .firstRow → k.phase = .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    (firstRow_other : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        ∀ k ev, AttemptValid p c E rho k → rho.events[k.start]? = some ev →
          ev.time + attemptBudget p G k ≤ rho.horizon →
          k.task = .firstRow → k.phase ≠ .contest →
          AttemptEndsBy p c E rho k (attemptBudget p G k))
    : ProgressAttemptStatement p G ΔF := by
  intro hδ V _ _ In c E rho hset hbound k ev hvalid hstart hhor
  cases ht : k.task with
  | raise =>
    by_cases hp : k.phase = .contest
    · exact raise_contest hδ c E rho hset hbound k ev hvalid hstart hhor ht hp
    · exact raise_other hδ c E rho hset hbound k ev hvalid hstart hhor ht hp
  | firstRow =>
    by_cases hp : k.phase = .contest
    · exact firstRow_contest hδ c E rho hset hbound k ev hvalid hstart hhor ht hp
    · exact firstRow_other hδ c E rho hset hbound k ev hvalid hstart hhor ht hp

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section Lane
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))


include hrec mono crossing qc writes rowCoverage

variable
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))

include hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 lane assembly from the four complete attempt-budget rows.
The standing ports are the ports of AttemptRows. -/
theorem healing_progressAttempt
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  cases ht : k.task with
  | raise =>
    by_cases hp : k.phase = .contest
    · exact healing_attempt_raise_contest E rho hrec mono crossing qc writes rowCoverage hδ
        hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor ht hp
    · exact healing_attempt_raise_other E rho hrec mono crossing qc writes rowCoverage hδ
        hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor ht hp
  | firstRow =>
    by_cases hp : k.phase = .contest
    · exact healing_attempt_firstRow_contest E rho hrec mono crossing qc writes rowCoverage
        hvalid hstart hhor ht hp
    · exact healing_attempt_firstRow_other E rho hrec mono crossing qc writes rowCoverage hδ
        hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hvalid hstart hhor ht hp

end Lane

end AvailableChain.FGSA.Run
end
