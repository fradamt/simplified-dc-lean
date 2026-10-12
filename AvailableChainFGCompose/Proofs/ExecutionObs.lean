module
public import AvailableChainFGCompose.Statements.ExecutionObs
public import AvailableChainFGCompose.Statements.Restart
public import AvailableChainFGCompose.Statements.SafetyStore
public import AvailableChainKitFG.Correspondence -- shake: keep (Compose import policy)

public section

/-! The ordinary Duty fold satisfies the shared execution observation laws. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {V In : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable (E : Generic.Env V) (rho : V2.D.Run V P)

private theorem cut_start (x : V) (j : Nat) :
    ordinaryCutState E rho x (3 * j) = V2.D.Run.stateBefore E rho j x := by
  rw [ordinaryCutState_def, ite_eq_left (by omega), show 3 * j / 3 = j by omega]

private theorem cut_entry (x : V) (j : Nat) :
    ordinaryCutState E rho x (3 * j + 1) = ordinaryEntry E rho x j := by
  rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_left (by omega),
    show (3 * j + 1) / 3 = j by omega]

private theorem cut_done (x : V) (j : Nat) :
    ordinaryCutState E rho x (3 * j + 2) = V2.D.Run.stateBefore E rho (j + 1) x := by
  rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_right (by omega),
    show (3 * j + 2) / 3 = j by omega]

omit [DecidableEq V] in
private theorem idx_lt {j : Nat} {e : V2.Event V P.Object} (h : rho.events[j]? = some e) :
    j < rho.events.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

private theorem entryStep_tick (x : V) (st : P.State) (t : Time) :
    ordinaryEntryStep x st (.tick x t) = P.clock st t := ite_eq_left rfl

private theorem entryStep_restart (x : V) (st : P.State) (t : Time) :
    ordinaryEntryStep x st (.restart x t) = P.restore (P.durable st) t := ite_eq_left rfl

private theorem releaseStep_tick (x : V) (st : P.State) (t : Time) :
    ordinaryReleaseStep E rho x st (.tick x t) = dependencyReleased E rho (P.clock st t) x t :=
  ite_eq_left rfl

private theorem entry_some (x : V) {j : Nat} {e : V2.Event V P.Object}
    (h : rho.events[j]? = some e) :
    ordinaryEntry E rho x j = ordinaryEntryStep x (V2.D.Run.stateBefore E rho j x) e := by
  rw [ordinaryEntry_def, h]
  rfl

private theorem entry_none (x : V) {j : Nat} (h : rho.events[j]? = none) :
    ordinaryEntry E rho x j = V2.D.Run.stateBefore E rho j x := by
  rw [ordinaryEntry_def, h]
  rfl

private theorem succ_not_tick (x : V) {j : Nat} {e : V2.Event V P.Object}
    (h : rho.events[j]? = some e) (hne : ∀ t, e ≠ .tick x t) :
    V2.D.Run.stateBefore E rho (j + 1) x =
      ordinaryEntryStep x (V2.D.Run.stateBefore E rho j x) e := by
  rw [V2.D.Run.stateBefore_succ E rho h]
  cases e with
  | restart y t =>
    change Function.update _ y _ x = (if y = x then _ else _)
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne (Ne.symm hy), ite_eq_right hy]
  | tick y t =>
    change Function.update _ y _ x = (if y = x then _ else _)
    by_cases hy : y = x
    · subst hy; exact absurd rfl (hne t)
    · rw [Function.update_of_ne (Ne.symm hy), ite_eq_right hy]
  | deliver y o t =>
    change Function.update _ y _ x = (if y = x then _ else _)
    by_cases hy : y = x
    · subst hy; rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne (Ne.symm hy), ite_eq_right hy]

private theorem succ_tick (x : V) {j : Nat} {t : Time} (h : rho.events[j]? = some (.tick x t)) :
    V2.D.Run.stateBefore E rho (j + 1) x =
      ((dependencyReleased E rho (P.clock (V2.D.Run.stateBefore E rho j x) t) x t).filter
        P.objSelfVisible).foldl P.recordOwn (P.clock (V2.D.Run.stateBefore E rho j x) t) :=
  (V2.D.Run.step_tick_eq E rho h).1

private theorem released_some (x : V) {j : Nat} {e : V2.Event V P.Object}
    (h : rho.events[j]? = some e) :
    (ordinaryFGExecutionObs E rho).released x j =
      ordinaryReleaseStep E rho x (V2.D.Run.stateBefore E rho j x) e := by
  rw [ordinaryFGExecutionObs_def]
  change ((rho.events[j]?).map _).getD [] = _
  rw [h]
  rfl

private theorem time_at {j : Nat} {e : V2.Event V P.Object} (h : rho.events[j]? = some e)
    (x : V) {k : Nat} (h1 : 3 * j ≤ k) (h2 : k ≤ 3 * j + 2) :
    (ordinaryFGExecutionObs E rho).cutTime x k = e.time := by
  rw [ordinaryFGExecutionObs_def]
  change ((rho.events[k / 3]?).map V2.Event.time).getD 0 = _
  rw [show k / 3 = j by omega, h]
  rfl

/-- The ordinary Duty fold meets the shared execution laws, with no premise. -/
theorem ordinaryFGExecutionObs_laws :
    FGExecutionObsLaws E rho (ordinaryFGExecutionObs E rho) where
  init_state _ := rfl
  start_state j _ x _ := cut_start E rho x j
  done_state j _ x _ := cut_done E rho x j
  cut_order j _ x h := by
    have := idx_lt rho h
    change 3 * j < 3 * j + 1 ∧ 3 * j + 1 ≤ 3 * j + 1 ∧ 3 * j + 1 ≤ 3 * j + 2 ∧
      3 * j + 2 ≤ 3 * rho.events.length
    omega
  event_order i j _ _ x _ _ hij := by
    change 3 * i + 2 < 3 * j
    omega
  segment_time j e x k h h1 h2 := time_at E rho h x h1 h2
  tick_entry j x t h := by
    change ordinaryCutState E rho x (3 * j + 1) = P.clock (ordinaryCutState E rho x (3 * j)) t
    rw [cut_entry, cut_start, entry_some E rho x h, entryStep_tick]
  restart_entry j x t h := by
    change ordinaryCutState E rho x (3 * j + 1) =
      P.restore (P.durable (ordinaryCutState E rho x (3 * j))) t
    rw [cut_entry, cut_start, entry_some E rho x h, entryStep_restart]
  released_tick j x t h := by
    rw [released_some E rho x h, releaseStep_tick]
    change _ = dependencyReleased E rho (ordinaryCutState E rho x (3 * j + 1)) x t
    rw [cut_entry, entry_some E rho x h, entryStep_tick]
  released_other j x hne := by
    cases h : rho.events[j]? with
    | none =>
      rw [ordinaryFGExecutionObs_def]
      change ((rho.events[j]?).map _).getD [] = []
      rw [h]; rfl
    | some e =>
      rw [released_some E rho x h]
      cases e with
      | tick y t =>
        change (if y = x then _ else []) = []
        rw [ite_eq_right]
        rintro rfl
        exact hne t h
      | restart y t => rfl
      | deliver y o t => rfl
  tick_done j x t h := by
    change ordinaryCutState E rho x (3 * j + 2) =
      (((ordinaryFGExecutionObs E rho).released x j).filter P.objSelfVisible).foldl
        P.recordOwn (ordinaryCutState E rho x (3 * j + 1))
    rw [cut_done, cut_entry, entry_some E rho x h, released_some E rho x h, succ_tick E rho x h,
      entryStep_tick, releaseStep_tick]
  accept_origin x k o hacc := by
    obtain ⟨j, wire, t, h, rfl, rfl⟩ := hacc
    have := idx_lt rho h
    refine ⟨?_, rfl, h, rfl, ?_⟩
    · change 3 * j < 3 * rho.events.length
      omega
    · change 3 * j ≤ 3 * j
      omega
  accept_time x k o hacc := by
    obtain ⟨j, wire, t, h, rfl, rfl⟩ := hacc
    rw [time_at E rho h x (le_refl _) (by omega)]
    exact le_refl _

/-- Ordinary emissions are exactly the Duty-fold emissions. -/
theorem ordinary_obsEmits_iff (x : V) (o : P.Object) (t : Time) :
    obsEmits (ordinaryFGExecutionObs E rho) rho x o t ↔ V2.D.Run.emits E rho x o t := by
  rw [obsEmits_def]
  constructor
  · rintro ⟨j, h, ho⟩
    refine ⟨j, h, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho h).2]
    rw [released_some E rho x h, releaseStep_tick] at ho
    exact ho
  · rintro ⟨j, h, ho⟩
    refine ⟨j, h, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho h).2] at ho
    rw [released_some E rho x h, releaseStep_tick]
    exact ho

/-- A relation kept by every ordinary microstep holds across each local cut step. -/
private theorem cut_step {Q : P.State → P.State → Prop} (hrefl : ∀ st, Q st st)
    (hclock : ∀ st t, Q st (P.clock st t)) (hprocess : ∀ st o, Q st (P.process st o))
    (hrestore : ∀ st t, Q st (P.restore (P.durable st) t))
    (hown : ∀ st (l : List P.Object), Q st (l.foldl P.recordOwn st))
    (x : V) (k : Nat) (hk : k < 3 * rho.events.length) :
    Q (ordinaryCutState E rho x k) (ordinaryCutState E rho x (k + 1)) := by
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 3 ∧ k = 3 * j + r :=
    ⟨k / 3, k % 3, by omega, by omega⟩
  have hj : j < rho.events.length := by omega
  obtain ⟨e, he⟩ : ∃ e, rho.events[j]? = some e := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  · rw [Nat.add_zero, cut_start, cut_entry, entry_some E rho x he]
    cases e with
    | restart y t =>
      change Q _ (if y = x then _ else _)
      split_ifs
      · exact hrestore _ _
      · exact hrefl _
    | tick y t =>
      change Q _ (if y = x then _ else _)
      split_ifs
      · exact hclock _ _
      · exact hrefl _
    | deliver y o t =>
      change Q _ (if y = x then _ else _)
      split_ifs
      · exact hprocess _ _
      · exact hrefl _
  · rw [cut_entry, cut_done, entry_some E rho x he]
    by_cases ht : ∃ t, e = .tick x t
    · obtain ⟨t, rfl⟩ := ht
      rw [succ_tick E rho x he, entryStep_tick]
      exact hown _ _
    · rw [succ_not_tick E rho x he (fun t h => ht ⟨t, h⟩)]
      exact hrefl _
  · rw [cut_done, show 3 * j + 2 + 1 = 3 * (j + 1) by omega, cut_start]
    exact hrefl _

variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)

private theorem own_fold_core (L : FGCoreLaws R) (st : P.State) (l : List P.Object) :
    R.core (l.foldl P.recordOwn st) = R.core st := by
  induction l generalizing st with
  | nil => rfl
  | cons o l ih => rw [List.foldl_cons, ih, L.own_core]

/-- The ordinary Duty fold meets the observed core laws. -/
theorem ordinaryFGExecutionObs_core (L : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (T : FGTreeRestoreLaws R) : FGObservedCoreLaws R rho (ordinaryFGExecutionObs E rho) where
  tf_step x k hk := by
    rw [ordinaryFGExecutionObs_def] at hk ⊢
    exact cut_step E rho (Q := fun a b => (R.core a).fg.TF ⊆ (R.core b).fg.TF)
      (fun _ => subset_refl _) (fun st t => by rw [L.clock_fg])
      (fun st o => L.process_tf st o) (fun st t => by rw [T.restart_eq])
      (fun st l => by rw [own_fold_core R L]) x k hk
  restore_tf j x t h := by
    change (R.core (ordinaryCutState E rho x (3 * j + 1))).fg.TF =
      (R.core (ordinaryCutState E rho x (3 * j))).fg.TF
    rw [cut_entry, cut_start, entry_some E rho x h, entryStep_restart, T.restart_eq]
  head_mem j x t s h := by
    change ∃ B ∈ (R.core (ordinaryCutState E rho x (3 * j + 1))).fg.TF,
      R.erase B = R.headVote (ordinaryCutState E rho x (3 * j + 1)) s
    rw [cut_entry, entry_some E rho x h, entryStep_tick]
    exact HL.head_mem j x t s
  parent_closed x k _ := by
    change ∀ B ∈ (R.core (ordinaryCutState E rho x k)).fg.TF,
      B.parent ∈ (R.core (ordinaryCutState E rho x k)).fg.TF
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 3 ∧ k = 3 * j + r :=
      ⟨k / 3, k % 3, by omega, by omega⟩
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    · rw [Nat.add_zero, cut_start]; exact HL.parent_closed j x
    · rw [cut_entry]
      cases he : rho.events[j]? with
      | none => rw [entry_none E rho x he]; exact HL.parent_closed j x
      | some e =>
        by_cases ht : ∃ t, e = .tick x t
        · obtain ⟨t, rfl⟩ := ht
          rw [entry_some E rho x he, entryStep_tick, L.clock_fg]
          exact HL.parent_closed j x
        · rw [entry_some E rho x he, ← succ_not_tick E rho x he (fun t h => ht ⟨t, h⟩)]
          exact HL.parent_closed (j + 1) x
    · rw [cut_done]; exact HL.parent_closed (j + 1) x

/-- The ordinary Duty fold meets the observed finality laws. -/
theorem ordinaryFGExecutionObs_finality (L : FGCoreLaws R)
    (process_F : ∀ nd o, FGBlock.Preceq (R.core nd).fg.F (R.core (P.process nd o)).fg.F)
    (SR : FGSafetyRestartLaws R) :
    FGObservedFinalityLaws R rho (ordinaryFGExecutionObs E rho) where
  f_step x k hk := by
    rw [ordinaryFGExecutionObs_def] at hk ⊢
    exact cut_step E rho (Q := fun a b => FGBlock.Preceq (R.core a).fg.F (R.core b).fg.F)
      (fun _ => KitFG.preceq_refl _) (fun st t => by rw [L.clock_fg]; exact KitFG.preceq_refl _)
      (fun st o => process_F st o) (fun st t => by rw [SR.restart_F]; exact KitFG.preceq_refl _)
      (fun st l => by rw [own_fold_core R L]; exact KitFG.preceq_refl _) x k hk
  restore_f j x t h := by
    change (R.core (ordinaryCutState E rho x (3 * j + 1))).fg.F =
      (R.core (ordinaryCutState E rho x (3 * j))).fg.F
    rw [cut_entry, cut_start, entry_some E rho x h, entryStep_restart, SR.restart_F]

end AvailableChain.FGCompose
end
