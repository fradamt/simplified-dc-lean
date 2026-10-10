module
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSAClaims.Statements.Join
public import AvailableChainFGSARun.Proofs.Acceptance
public import AvailableChainFGSARun.Proofs.ReadyAcceptance
public import AvailableChainFGSARun.Proofs.Join
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A trigger uses a scheduled event inside the nonnegative run horizon. -/
theorem fgsa_trigger_nonneg (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {o : Obj p} {t : Time}
    (hT : Gen.V2.Duty.Trigger E rho o t) : 0 ≤ t := by
  rcases hT with ⟨v, _, i, he, _⟩ | ⟨v, _, i, ⟨parent, he, _⟩, _, _⟩ <;>
    exact (hS.in_horizon _ (List.mem_of_getElem? he)).1

/-- A valid receiver tick supplies the earlier awake interval on a NoRestart run. -/
theorem fgsa_awakeOn_before_tick_noRestart (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) {i : Nat} {x : V} {t : Time}
    (hi : rho.events[i]? = some (.tick x t)) (hx : x ∈ rho.honest)
    {a d : Time} (ha : 0 ≤ a) (hd : d ≤ t) : V2.D.AwakeOn E x a d := by
  intro u hau hud
  exact fgsa_awake_before_noRestart E rho hV hN x hx t
    (hV.in_horizon _ (List.mem_of_getElem? hi)).2
    (hV.tick_awake x t (List.mem_of_getElem? hi)) u (ha.trans hau) (hud.le.trans hd)

/-- The legacy NoRestart premise supplies the exact join guard at an existing tick. -/
theorem fgsa_joinedNow_noRestart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {t : Time} (hi : rho.events[i]? = some (.tick x t)) :
    joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) t).st = true := by
  apply fgsa_joinedNow_of_joinedEnv E rho hS hi
  intro w _ _ he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  exact (hN j x w hj).elim

/-- N4: ready service gives processing strictly before the deadline, and it
persists to the freeze in the same receiver epoch. Retained history must be safe. -/
theorem fgsa_catchUp_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (dl : Time → Time) (cut : Time) (o : Obj p) (send a freeze : Time) (x : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hQ : ¬ isRowObject o)
    (hT : Gen.V2.Duty.ReadyTrigger E rho o send x a (dl a))
    (hx : x ∈ rho.honest) (hsa : send ≤ a) (ha : 0 ≤ a) (had : a < dl a)
    (hc : dl a ≤ cut) (hh : dl a ≤ rho.horizon) (hfreeze : dl a ≤ freeze)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho x o a)
    (hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho freeze))
    (hReady : ∀ j t', a ≤ t' → t' < dl a → V2.D.Run.handlesAt E rho j x o t' →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x) o = false) :
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho (dl a) x) o = true ∧
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho freeze x) o = true := by
  have hidx := fgsa_idxBefore_mono rho hfreeze
  have hService := Gen.V2.Duty.service_of_readyTrigger hD hQ hT hx hsa ha had hc hh hNX
  have hp := Gen.V2.Duty.processed_by_deadline_of_service E rho (fgsaTimely p)
    (fgsaAcceptanceInv p) x o a (dl a) hS had hService hHistory
    (hRF.mono le_rfl hidx) (fgsaHooks p c) (fgsaAcceptance p c)
    (fun j t' hat htd hj =>
      ⟨cstoreInv_stateBefore E rho j x, hReady j t' hat htd hj⟩) hNX
  refine ⟨hp, ?_⟩
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho freeze hS]
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl a) hS] at hp
  exact (fgsaHooks p c).processed_stable E rho hS x o _ _ hidx
    (hRF.mono (Gen.V2.Duty.actionCut_le_idxBefore hS had) le_rfl) hp

/-- N7 supplier: a joined reader at a gate gives the exact store guard.
The caller supplies the approved environment restart bound at this same tick. -/
theorem fgsa_gate_joined_of_joinedEnv (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hJ : ∀ w, 0 ≤ w → w ≤ SA.gateTime p.toParams s →
      V2.Event.restart x w ∈ rho.events → w ≤ 4 * p.Δ * (s : Int)) :
    joinedAtTime p (V2.D.Run.stateBefore E rho i x).st.restartTime
      (SA.gateTime p.toParams s) = true := by
  have hj := fgsa_joinedNow_of_joinedEnv E rho hS hi (by
    intro w hw ht he
    have hs := fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i x) s
    have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
      exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans hs
    rw [hslot]
    have hbound := hJ w hw ht he
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hbound)
  change joinedNow p (FGSA.clock p _ _) = true at hj
  unfold joinedNow at hj
  rw [fgsa_clock_restartTime, (clock_vn _ _).2] at hj
  exact hj

/-- A NoRestart run enables each existing gate tick. -/
theorem fgsa_enabledGate_noRestart (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot} (hi : IsGateTick p c rho i x s) :
    enabledGateAt p c E rho i x s := by
  refine ⟨hi, ?_⟩
  have hb := fgsa_restartTime_bound E rho i x (4 * p.Δ * (s : Int)) (by
    intro j w _ hj
    exact (hN j x w hj).elim)
  change (match (V2.D.Run.stateBefore E rho i x).st.restartTime with
    | none => True
    | some w => w ≤ 4 * p.Δ * (s : Int))
  cases hr : (V2.D.Run.stateBefore E rho i x).st.restartTime with
  | none => trivial
  | some w => exact hb w hr

/-- The enabled gate supplies the exact join test used by the gate law. -/
theorem fgsa_gate_joined_of_enabled (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {i : Nat} {x : V} {s : Slot}
    (hEnabled : enabledGateAt p c E rho i x s) :
    joinedAtTime p (V2.D.Run.stateBefore E rho i x).st.restartTime
      (SA.gateTime p.toParams s) = true := by
  have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i x) s)
  have hg := hEnabled.2
  change (match (V2.D.Run.stateBefore E rho i x).st.restartTime with
    | none => True
    | some w => w ≤ 4 * p.Δ * (s : Int)) at hg
  cases hr : (V2.D.Run.stateBefore E rho i x).st.restartTime with
  | none => rfl
  | some w =>
    rw [hr] at hg
    change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) = true
    simpa only [hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      decide_eq_true_eq] using hg

/-- P11: a scheduled gate saves the executed result in both join branches. -/
theorem fgsa_gate_saved_guarded (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s))) :
    let st := (V2.D.Run.stateBefore E rho i x).st
    GridCO.savedGenuine (FGSA.clock p st (SA.gateTime p.toParams s)).base s =
      some (if joinedAtTime p st.restartTime (SA.gateTime p.toParams s) then
          SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
            (actView (clockPre p st (SA.gateTime p.toParams s))) s
        else none) := by
  intro st
  cases hj : joinedAtTime p st.restartTime (SA.gateTime p.toParams s) with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact fgsa_gate_saved_unjoined E rho hS hi hj
  | true =>
    simp only [ite_true]
    exact fgsa_gate_saved_result E rho hS hi hj

end AvailableChain.FGSA.Run
end
