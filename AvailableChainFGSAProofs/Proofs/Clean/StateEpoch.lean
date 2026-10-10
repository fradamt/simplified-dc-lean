module
public import AvailableChainFGSAProofs.Proofs.Clean.Chain
public import AvailableChainGeneric.Proofs.V2.Duty.Sleep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A restart keeps the durable Clean state and starts empty saved histories. -/
theorem clean_restart_fields {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.restart v t)) :
    let a := storeAt p c E rho j v
    let b := storeAt p c E rho (j + 1) v
    b.fg = a.fg ∧ b.base.blocks = a.base.blocks ∧
      b.base.obligations = a.base.obligations ∧
      b.base.stableRecord = a.base.stableRecord ∧
      b.base.genuine = [] ∧ b.fastWrite = [] ∧ b.restartTime = some t := by
  have hs : storeAt p c E rho (j + 1) v = acRestart p (storeAt p c E rho j v) t := by
    change (V2.D.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.D.Engine.state_after_restart he]
    rfl
  dsimp only
  rw [hs]
  exact ⟨acRestart_fg p _ t, acRestart_blocks p _ t, acRestart_obligations p _ t,
    acRestart_stableRecord p _ t, acRestart_genuine p _ t, acRestart_fastWrite p _ t,
    acRestart_restartTime p _ t⟩

/-- Completed event results stay in the global history when local caches are erased. -/
theorem cleanHist_step_restart (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.restart v t))
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) := by
  have hn (x : V) (s : Slot) : ¬ IsGateTick p c rho i x s := by
    intro ht
    change rho.events[i]? = some (.tick x _) at ht
    rw [he] at ht
    cases ht
  have hr : cleanResults p c E rho (i + 1) = cleanResults p c E rho i := by
    ext ⟨s, B⟩
    rw [cleanResults_mem_succ_iff hS]
    constructor
    · rintro (h | ⟨x, ht, _⟩)
      · exact h
      · exact (hn x s ht).elim
    · exact Or.inl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hr] using hh.ordered
  · simpa only [hr] using hh.same
  · intro j x s hj ht
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s ht).elim
    exact hh.nonempty j x s hji ht
  · intro j k x y s B hj hk ht hy hB
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s ht).elim
    exact hh.continues j k x y s B hji hk ht hy hB

/-- The enabled gate's receiver interval gives N4 its exact event-index epoch. -/
theorem clean_enabledGate_service_epoch (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {j : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho j x s)
    {a freeze : Time} (ha : slotStartZ p (s : Int) ≤ a) (haf : a < freeze)
    (hf : freeze ≤ SA.gateTime p.toParams s) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho freeze) := by
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hV.toScheduleWellFormed haf
  intro k t ht hat htf
  exact clean_enabledGate_restartFreeTime hV hR hx hG t (ha.trans_lt hat)
    (htf.le.trans hf) (List.mem_of_getElem? ht)

/-- Restarts before this same-time tick keep the FG fields of the strict time read. -/
theorem clean_gate_fg_before_time (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hi : IsGateTick p c rho i x s) :
    (storeAt p c E rho i x).fg =
      (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) x).st.fg := by
  let a := V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)
  have hai : a ≤ i := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS hi
      (SA.gateTime p.toParams s)).mp (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim
  have hp : (storeAt p c E rho i x).fg = (storeAt p c E rho a x).fg := by
    apply V2.D.Engine.stateBefore_step_induction E rho
      (fun nd => nd.st.fg = (storeAt p c E rho a x).fg) hai x ?_ rfl
    intro j e haj hji he hx hfg
    have htime : e.time = SA.gateTime p.toParams s := by
      have hlo : SA.gateTime p.toParams s ≤ e.time := by
        by_contra hn
        have hj := (Gen.V2.Duty.index_lt_idxBefore_iff hS he
          (SA.gateTime p.toParams s)).mpr (lt_of_not_ge hn)
        exact (Nat.not_lt_of_ge haj) hj
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      have hk := List.pairwise_iff_getElem.mp hS.sorted j i hjl hil hji
      rw [hje, hie] at hk
      exact le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk) hlo
    cases e with
    | restart v t =>
      change v = x at hx
      subst v
      simp only [V2.D.World.step, Function.update_self]
      change (acRestart p (storeAt p c E rho j x) t).fg = _
      rwa [acRestart_fg]
    | tick v t =>
      change v = x at hx
      subst v
      change t = SA.gateTime p.toParams s at htime
      subst t
      have hji' := fgsa_tick_unique E rho hS he hi
      exact (Nat.ne_of_lt hji hji').elim
    | deliver v o t =>
      change t = SA.gateTime p.toParams s at htime
      exact (Nat.not_lt_of_ge (V2.D.Engine.tick_index_lt_delivery E rho hS hi he
        htime.symm.le).le) hji |>.elim
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.gateTime p.toParams s) hS]
  exact hp

end AvailableChain.FGSA.Run
end
