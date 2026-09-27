module
public import AvailableChainSAPC.Proofs.CleanPCPath
public import AvailableChainSAPC.Proofs.Preservation

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- At a HEAD, the finite root is still on the input path. The clock
can expire or release rows, but it cannot create a row at this phase. -/
theorem headRoot_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (i : Nat) (reader : V)
    (hr : reader ∈ rho.honest) (r : Slot)
    (h : JointCleanInvariant p E rho i) :
    cleanRunPath p rho i (GridCO.liveRoot
      (clock p (Run.stateBefore (sapc p) rho i reader) (voteTime p r)).base) := by
  apply CleanStateOnPath.liveRoot h.facts.chain
  rw [clock_eq_preGate_of_no_gate p _ _ (voteTime_ne_gateTime p r)]
  exact (clockPreGate_clean p _ _ (h.facts.states i (le_refl _) reader hr)).1

/-- The capped timely-N transfer now has its finite-root premise from
the run invariant. It needs only the next HEAD in the horizon, including
a last incomplete label with no following gate. -/
theorem timely_nextHead_of_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i) (b : Block)
    (source : HonestTimelySource p rho i r b) :
    Block.Preceq b (headData p rho (r + 1) reader).target := by
  have hb : cleanRunPath p rho i b :=
    Or.inr ⟨b, .timely r b cap source, GridCO.block_preceq_self b⟩
  obtain ⟨v, hv, j, _, _, saved⟩ := source
  have root := headRoot_on_cleanRunPath p E rho i reader hr (r + 1) h
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he] at root
  have ha : capBroken p (headState p rho (r + 1) reader) = false := by
    rw [headState, capBroken_clock]
    exact capBroken_false_beforeTime p E rho hs.execution cap reader _
  have hsync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  exact synchronous_timely_active_head_covers p E rho hs.execution hΔ hs.acceptedRelay r hsync
    v reader hv hr (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2 b
    (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed (j + 1) v r b saved)
    ha (h.facts.chain.comparable _ _ root hb)

/-- An earlier genuine result continues at every capped HEAD, including
the final incomplete label. Local raw transfer and both root premises
come from the actual run and the input invariant. -/
theorem genuine_head_continuation_of_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (s : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (s + 1))))
    (h : JointCleanInvariant p E rho i)
    (j : Nat) (hj : j < i) (v : V) (hv : v ∈ rho.honest) (r : Slot) (b : Block)
    (ht : rho.events[j]? = some (.tick v (gateTime p r)))
    (raw : SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b) :
    Block.Preceq b (headData p rho (s + 1) reader).target := by
  have htime : gateTime p r ≤ voteTime p (s + 1) := by
    by_contra hn
    have := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he ht (lt_of_not_ge hn)
    omega
  have hrs : r < s := by
    by_contra hn
    have hle : (s : Time) ≤ r := by exact_mod_cast le_of_not_gt hn
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ at htime
    push_cast at htime
    nlinarith [p.deltaPos]
  have hhead : voteTime p s < voteTime p (s + 1) := by
    change 4 * p.Δ * (s : Time) + p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hnow := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have coverage (w : V) (hw : w ∈ rho.honest) :
      Block.Preceq b (headData p rho s w).target := by
    have hpub : PublicTime E (voteTime p s) := by
      refine ⟨4 * s + 1, ?_⟩
      change 4 * p.Δ * (s : Time) + p.Δ = _
      rw [hΔ]
      push_cast
      ring
    have hn : 0 ≤ voteTime p s := by
      change 0 ≤ 4 * p.Δ * (s : Time) + p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg s]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
      (hs.execution.tick_total w hw _ hpub hn (hhead.le.trans hnow))
    have hki := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed hk he hhead
    have cover := h.facts.transferred j hj v hv r b ht raw k hki w hw s hrs hk
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hk] at cover
    exact cover
  have hearly : earlyTime p s ≤ rho.horizon := by
    apply le_trans _ hnow
    change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨c, hc, hbc⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs s hearly b coverage reader hr
  have hb := h.facts.genuine j hj v hv r b ht raw
  have root := headRoot_on_cleanRunPath p E rho i reader hr (s + 1) h
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he] at root
  have hsync : E.t_GST ≤ earlyTime p s := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have hf : freezeTime p s ≤ rho.horizon := by
    apply le_trans _ hnow
    change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  apply synchronous_local_genuine_head_covers p E rho hs.execution hΔ hs.acceptedRelay
    s hsync hf reader hr b c hc hbc (h.facts.chain.comparable _ _ root hb)
  intro cert selected
  apply selectedPC_compatible_cleanRunPath p E rho hs.execution cap
    i reader (voteTime p (s + 1)) (s + 1) cert h.facts.chain b hb
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
  exact selected

/-- The complete capped HEAD/release step, including the final HEAD
when its following gate is outside the run. -/
theorem jointClean_head_tick_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r)))
    (h : JointCleanInvariant p E rho i) :
    JointCleanInvariant p E rho (i + 1) := by
  constructor
  · rw [cleanRunPath_eq_at_head_capped p E rho hs.execution cap i reader r he]
    apply cleanPathFacts_tick_of_no_early_no_gate p E rho hs.execution i reader _ he
      (voteTime_ne_earlyTime p r) (voteTime_ne_gateTime p r) h.facts
    · intro s c _ _ _ hc
      rw [clock_bestPC] at hc
      exact installedPC_on_cleanRunPath p E rho hs.execution cap i reader c hc
    · intro s c _ _ _ hc
      exact selectedPC_on_cleanRunPath p E rho hs.execution cap i reader _ s c hc
    · intro j hj v hv s b ht raw label hsl htime hr
      have hlabel : label = r := by
        have heq : (label : Time) = r := by
          change 4 * p.Δ * (r : Time) + p.Δ = 4 * p.Δ * (label : Time) + p.Δ at htime
          nlinarith [p.deltaPos]
        exact_mod_cast heq
      subst label
      cases r with
      | zero => exact (Nat.not_lt_zero s hsl).elim
      | succ r =>
        have cover := genuine_head_continuation_of_run_invariant p E rho hΔ t₀ hs cap
          i reader hr r he h j hj v hv s b ht raw
        rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
        exact cover
  · apply h.ordered.step_of_no_gate
    intro v s ht
    exact voteTime_ne_gateTime p r s (congrArg Event.time (Option.some.inj (he.symm.trans ht)))

end AvailableChain.SAPC
end
