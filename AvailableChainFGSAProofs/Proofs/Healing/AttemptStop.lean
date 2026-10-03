module
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21 H.10:1428–1429, 1494–1498. An earlier event stops the attempt.
No service past that event is required. -/
theorem healing_attempt_ends_of_event {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget)
    (heff : EffectiveEvent p c E rho j) : AttemptEndsBy p c E rho k budget :=
  ⟨ev, hstart, j, ev', hj, hnext, htime, Or.inl heff⟩

/-- One later matching honest row completes the first-row task. -/
theorem healing_attempt_ends_of_row {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V (Obj p)} {j : Nat} {y : V} {r : Nat}
    {a : RowWire p.n} {e : BlockId}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget)
    (htask : k.task = .firstRow) (hrow : HonestRowAt p c E rho j y r a)
    (hnamed : namedEntry a.payload.height_pair = some (k.frontier, e)) :
    AttemptEndsBy p c E rho k budget :=
  ⟨ev, hstart, j, ev', hj, hnext, htime, Or.inr (Or.inr ⟨htask, y, r, a, e, hrow, hnamed⟩)⟩

theorem healing_attempt_ends_mono {k : AttemptKey} {budget budget' : Time}
    (hends : AttemptEndsBy p c E rho k budget) (hbudget : budget ≤ budget') :
    AttemptEndsBy p c E rho k budget' := by
  obtain ⟨ev, hstart, j, ev', hj, hnext, ht, hend⟩ := hends
  exact ⟨ev, hstart, j, ev', hj, hnext, by linarith, hend⟩

/-- A failed stopped-task bound excludes every effective event within its budget. -/
theorem healing_attempt_no_event {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V (Obj p)} {j : Nat}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget) :
    ¬ EffectiveEvent p c E rho j := fun heff =>
  hstop (healing_attempt_ends_of_event E rho hstart hj hnext htime heff)

/-- The second frozen start arm is required when the start event is not effective.
This extracts that arm; it makes no settlement claim. -/
theorem healing_attempt_inclusive_start {k : AttemptKey}
    (hvalid : AttemptValid p c E rho k) (hne : ¬ EffectiveEvent p c E rho k.start) :
    ∃ ev rG, rho.events[k.start]? = some ev ∧ E.t_GST ≤ ev.time ∧
      E.t_GST ≤ p.actionTime rG ∧
      (∀ r, E.t_GST ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1 := by
  obtain ⟨ev, hi, hgst, hstart, _⟩ := hvalid
  rcases hstart with heff | ⟨rG, hG, hmin, ht, hcut⟩
  · exact (hne heff).elim
  · exact ⟨ev, rG, hi, hgst, hG, hmin, ht, hcut⟩

end AvailableChain.FGSA.Run
end
