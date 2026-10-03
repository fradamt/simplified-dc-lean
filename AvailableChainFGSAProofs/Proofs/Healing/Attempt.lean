module
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run

/-! Blueprint 21 H.10. AttemptSettle supplies settlement for either start arm.
Complete rows still need the foundation and inline facts at the assembly
boundary. The raise rows also need terminal promotion within the frozen
horizon. This theorem keeps the four row facts as explicit hypotheses.
It does not prove any of those row facts. -/

/-- Conditional assembly of the four frozen attempt-budget rows. -/
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

end AvailableChain.FGSA.Run
end
