module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Replay
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (duty execution import route)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Local signed event membership transfers in both directions. -/
theorem wcg_eventReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (e : V2.Event V (fgsa p c).Object) (hx : e.node ∈ rho.honest)
    (ht : e.time ≤ source.horizon) : e ∈ rho.events ↔ e ∈ source.events := by
  have he := ha.events e.node hx
  have hm := congrArg (fun es => e ∈ es) he
  simpa only [List.mem_filter, decide_eq_true_eq, true_and, and_true,
    ht, and_self, eq_self_iff_true] using (Iff.of_eq hm)

/-- Strict reads agree, so matched local ticks have the same input state. -/
theorem wcg_beforeReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    rho.stateBeforeTime E' t x = source.stateBeforeTime E t x :=
  wcg_filtered_replay ha x hx _ (fun _ he => (le_of_lt (of_decide_eq_true he)).trans ht)

/-- A retained source tick has a continuation tick at its own global index.
The input states agree even when unrelated nodes change the global ordering. -/
theorem wcg_tickEventReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hns : V2.D.NoRestart source) (hnr : V2.D.NoRestart rho)
    {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest) (ht : t ≤ source.horizon)
    (hj : source.events[j]? = some (.tick x t)) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      rho.stateBefore E' k x = source.stateBefore E j x := by
  have hm := (wcg_eventReplay ha (.tick x t) hx ht).mpr (List.mem_of_getElem? hj)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  refine ⟨k, hk, ?_⟩
  rw [V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hr hnr hk,
    V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs hns hj]
  exact wcg_beforeReplay ha x hx ht

end AvailableChain.FGSA.Run
end
