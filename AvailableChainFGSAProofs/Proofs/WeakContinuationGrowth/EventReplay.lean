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

/-- Every public getter replays through the inclusive source endpoint. -/
theorem wcg_outputReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (g : V2.D.Output (fgsa p c)) (x : V) (hx : x ∈ rho.honest)
    {t : Time} (ht : t ≤ source.horizon) :
    V2.D.outputAt E' rho g x t = V2.D.outputAt E source g x t :=
  congrArg g (wcg_readReplay ha x hx ht)

/-- Empty-suffix public output safety needs no participation or half cap.
This transfers compatibility and monotonicity at all covered public reads.
The event-index safety fields require a separate occurrence-index argument. -/
theorem wcg_empty_outputs
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hsch : V2.D.ScheduleWellFormed E source)
    (hend : rho.horizon = source.horizon)
    {u : Slot} {Q : Block} {iSource : Nat} {ΔF : Time}
    (hcut : iSource = afterTicksIdx source (SA.gateTime p.toParams u))
    (hsafe : SSafeFromCut₂ p c E source iSource Q ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => SA.gateTime p.toParams u ≤ t ∧ t ≤ rho.horizon) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => SA.gateTime p.toParams u ≤ t ∧ t ≤ rho.horizon) := by
  have hidx : ∀ t, SA.gateTime p.toParams u ≤ t → iSource ≤ timeIdx source t := by
    intro t ht
    rw [hcut]
    exact (preIdx_le_afterTicksIdx E source hsch _).2.trans
      (V2.D.Engine.read_length_mono (rho := source) _ t ht)
  intro g hg
  obtain ⟨hc, hm⟩ := hsafe.outputs g hg
  constructor
  · intro t r x y ht hr hx hy
    change Block.Compatible (V2.D.outputAt E' rho g x t) (V2.D.outputAt E' rho g y r)
    rw [wcg_outputReplay ha g x hx (ht.2.trans_eq hend),
      wcg_outputReplay ha g y hy (hr.2.trans_eq hend)]
    exact hc t r x y (hidx t ht.1) (hidx r hr.1) (ha.honest hx) (ha.honest hy)
  · intro t r x ht hr htr hx
    change Block.Preceq (V2.D.outputAt E' rho g x t) (V2.D.outputAt E' rho g x r)
    rw [wcg_outputReplay ha g x hx (ht.2.trans_eq hend),
      wcg_outputReplay ha g x hx (hr.2.trans_eq hend)]
    exact hm t r x (hidx t ht.1) (hidx r hr.1) htr (ha.honest hx)

end AvailableChain.FGSA.Run
end
