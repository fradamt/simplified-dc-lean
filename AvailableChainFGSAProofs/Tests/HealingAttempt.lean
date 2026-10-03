module
public import AvailableChainFGSAProofs.Proofs.Healing.Attempt -- shake: keep (conditional assembly)
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptBudget -- shake: keep (four budget rows)
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptStop -- shake: keep (event and cut tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot -- shake: keep (B21 boundary)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.HealingAttempt
open AvailableChain.SimplexFG

private def attemptParams : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide

-- The W bound permits a row delay greater than the block delay.
example : attemptParams.Δ < (6 : Time) ∧ LivenessBoundW attemptParams 6 :=
  ⟨by decide, ⟨by decide⟩⟩

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .contest) :
    attemptBudget attemptParams 10 k = 64 := by
  rw [healing_attempt_raise_contest_budget attemptParams 10 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .gap) :
    attemptBudget attemptParams 10 k = 100 := by
  rw [healing_attempt_raise_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

example (k : AttemptKey) (htask : k.task = .raise) (hphase : k.phase = .topJ) :
    attemptBudget attemptParams 10 k = 100 := by
  rw [healing_attempt_raise_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    attemptBudget attemptParams 10 k = 41 := by
  rw [healing_attempt_firstRow_contest_budget attemptParams 10 k htask hphase]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .gap) :
    attemptBudget attemptParams 10 k = 77 := by
  rw [healing_attempt_firstRow_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

example (k : AttemptKey) (htask : k.task = .firstRow) (hphase : k.phase = .topJ) :
    attemptBudget attemptParams 10 k = 77 := by
  rw [healing_attempt_firstRow_other_budget attemptParams 10 k htask
    (by rw [hphase]; intro h; cases h)]
  decide

-- The exact sums include settlement, the frozen repair, and each opening.
example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) =
      ρΓ p G + 3 * P p + Γ p G - 10 * p.Δ :=
  healing_attempt_raise_contest_cost p G

example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) +
      (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) =
      ρΓ p G + 6 * P p + 2 * Γ p G - 18 * p.Δ :=
  healing_attempt_raise_other_cost p G

example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) = ρΓ p G + P p - p.Δ :=
  healing_attempt_firstRow_contest_cost p G

example (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) +
      (P p - 4 * p.Δ) = ρΓ p G + 4 * P p + Γ p G - 9 * p.Δ :=
  healing_attempt_firstRow_other_cost p G

example (p : Params) (G : Time) (hG : 4 * p.Δ ≤ G) :
    4 * P p + Γ p G - 13 * p.Δ ≤ 6 * P p + 2 * Γ p G - 21 * p.Δ :=
  healing_attempt_high_source_cost p G hG

-- A terminal deadline alone does not give the existing promotion horizon.
example : (18 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 9 * attemptParams.Δ = 41 ∧
    ¬ ((18 : Time) + 2 * P attemptParams + Γ attemptParams 10 - 4 * attemptParams.Δ ≤ 41) := by
  decide

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

-- A strictly earlier effective event ends the attempt without later service.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    {k : AttemptKey} {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev')
    (htime : ev'.time < ev.time + attemptBudget p G k)
    (heff : EffectiveEvent p c E rho j) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_ends_of_event E rho hstart hj hnext htime.le heff

-- An event at the budget endpoint is included.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    {k : AttemptKey} {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev')
    (htime : ev'.time = ev.time + attemptBudget p G k)
    (heff : EffectiveEvent p c E rho j) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_ends_of_event E rho hstart hj hnext htime.le heff

-- One matching row is enough; all-reader common entry is not a premise.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    {k : AttemptKey} {ev ev' : V2.Event V (Obj p)} {j : Nat} {y : V} {r : Nat}
    {a : RowWire p.n} {e : BlockId}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + attemptBudget p G k)
    (htask : k.task = .firstRow) (hrow : HonestRowAt p c E rho j y r a)
    (hnamed : namedEntry a.payload.height_pair = some (k.frontier, e)) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) :=
  healing_attempt_ends_of_row E rho hstart hj hnext htime htask hrow hnamed

-- B21: a valid attempt at frontier one must use the inclusive-cut start.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hnr : V2.D.NoRestart rho) {k : AttemptKey}
    (hvalid : AttemptValid p c E rho k) (hk : k.frontier = 1) :
    ∃ ev rG, rho.events[k.start]? = some ev ∧ E.t_GST ≤ ev.time ∧
      E.t_GST ≤ p.actionTime rG ∧
      (∀ r, E.t_GST ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 := by
  have hf : frontierAtIdx p c E rho (k.start + 1) = 1 := by
    obtain ⟨_, _, _, _, hf, _⟩ := hvalid
    exact hf.symm.trans hk
  exact healing_attempt_inclusive_start E rho hvalid (boot_not_effective_one p c E rho hnr hf)

-- B21 also fixes the live phase at genesis top J.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {i : Nat} {x : V}
    (hx : x ∈ rho.honest) (hf : frontierAtIdx p c E rho i = 1) :
    (R_at p c E rho i x).J = .genesis ∧ (R_at p c E rho i x).contest = false := by
  have h := boot_height_one p c E rho hx hf
  exact ⟨h.2.2.1, h.2.2.2.1⟩

-- This application remains conditional on the four stopped row facts.
example (p : Params) (G ΔF : Time)
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
    : ProgressAttemptStatement p G ΔF :=
  healing_progressAttempt_of p G ΔF raise_contest raise_other firstRow_contest firstRow_other

end AvailableChain.FGSA.Run.Tests.HealingAttempt
end
