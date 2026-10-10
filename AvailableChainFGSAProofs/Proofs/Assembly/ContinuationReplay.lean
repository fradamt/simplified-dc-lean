module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Matched local ticks read after every same-time restart in each run. -/
theorem assembly_tickReplay_atWake (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {j : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest) (ht : t ≤ source.horizon)
    (hj : source.events[j]? = some (.tick x t)) :
    ∃ k, rho.events[k]? = some (.tick x t) ∧
      rho.stateBefore E' k x = source.stateBefore E j x := by
  have hf := congrArg (fun es => V2.Event.tick x t ∈ es) (ha.events x hx)
  have hm : V2.Event.tick x t ∈ rho.events := by
    have he : V2.Event.tick x t ∈ source.events := List.mem_of_getElem? hj
    have hf' : V2.Event.tick x t ∈ rho.events ↔ V2.Event.tick x t ∈ source.events := by
      simpa only [List.mem_filter, decide_eq_true_eq, ht, eq_self_iff_true,
        true_and, and_true, V2.Event.node, V2.Event.time] using Iff.of_eq hf
    exact hf'.mpr he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  refine ⟨k, hk, ?_⟩
  rw [V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hr hk,
    V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hs hj]
  let test := fun e : V2.Event V (fgsa p c).Object =>
    decide (e.time < t ∨ (e.time = t ∧ e.phase = 0))
  have down : ∀ e f, e.key ≤ f.key → test f = true → test e = true := by
    intro e f hef hf
    have hf' : f.time < t ∨ (f.time = t ∧ f.phase = 0) := of_decide_eq_true hf
    rcases hf' with h | ⟨h, hp⟩
    · exact decide_eq_true (Or.inl ((V2.D.Engine.time_le_of_key_le e f hef).trans_lt h))
    · rcases Prod.Lex.toLex_le_toLex.mp hef with he | ⟨he, hep⟩
      · exact decide_eq_true (Or.inl (he.trans_eq h))
      · exact decide_eq_true (Or.inr ⟨he.trans h, Nat.eq_zero_of_le_zero (hep.trans_eq hp)⟩)
  change ((rho.events.take (rho.events.filter test).length).foldl
    (V2.D.World.step E' rho) V2.D.World.init) x =
      ((source.events.take (source.events.filter test).length).foldl
        (V2.D.World.step E source) V2.D.World.init) x
  rw [← V2.D.Engine.filter_eq_take hr test down, ← V2.D.Engine.filter_eq_take hs test down]
  apply wcg_filtered_replay ha x hx
  intro e he
  rcases of_decide_eq_true he with h | ⟨h, _⟩
  · exact h.le.trans ht
  · exact h.le.trans ht

end AvailableChain.FGSA.Run
end
