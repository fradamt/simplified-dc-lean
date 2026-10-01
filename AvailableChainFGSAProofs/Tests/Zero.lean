module
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean -- shake: keep (test examples use the Export names)

-- Test fixtures and examples stay private.
set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.Zero

private abbrev p4 : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

private abbrev rho0 : V2.D.Run (Fin 4) (fgsa p4 unitCodec) where
  honest := {0}
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

private abbrev env0 : Generic.Env (Fin 4) :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private theorem schedule0 : V2.D.ScheduleWellFormed env0 rho0 where
  horizon_nonneg := le_rfl
  sorted := List.pairwise_singleton _ _
  nodup := List.nodup_singleton _
  in_horizon := by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨le_rfl, le_rfl⟩
  honest_only := by
    intro e he
    have heq := List.mem_singleton.mp he
    subst e
    exact Finset.mem_singleton_self _
  tick_public := by
    intro v t ht
    have he : V2.Event.tick v t = .tick 0 0 := List.mem_singleton.mp ht
    cases he
    exact ⟨0, rfl⟩
  tick_total := by
    intro v hv t _ ht hh
    have he : t = 0 := le_antisymm hh ht
    subst t
    have hv : v = 0 := Finset.mem_singleton.mp hv
    subst v
    exact List.mem_singleton_self _

private theorem noDelivery0 (i : Nat) (v : Fin 4) (o : (fgsa p4 unitCodec).Object)
    (t : Time) : rho0.events[i]? ≠ some (.deliver v o t) := by
  cases i <;> simp

-- Horizon zero with three faulty validators; no receipt is scheduled.
private theorem base0 : Base₂ p4 unitCodec env0 rho0 where
  valid := {
    toScheduleWellFormed := schedule0
    wire := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    deps := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    fresh := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    unforgeable := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim
    carried := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim }
  linked := by
    refine ⟨4, Equiv.refl _, ?_⟩
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · exact hℓ.elim
    · exact ⟨rfl, fun _ => rfl⟩
    · exact hℓ.elim
  cstar := by
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · change Function.Bijective (fun i : Fin 4 => i)
      exact Function.bijective_id
    · exact hℓ.elim
    · exact hℓ.elim
  noRestart := by intro i v t; cases i <;> simp
  delta := rfl

private theorem healthy0 : V2.D.HealthyPrefixDelivery env0 rho0 0 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, _⟩ w _ hd _
    have ht : 0 ≤ t := (schedule0.in_horizon _ (List.mem_of_getElem? hi)).1
    change t + 1 ≤ 0 at hd
    exact (not_le_of_gt (lt_add_of_le_of_pos ht (by decide)) hd).elim
  relay_accepted := by
    rintro v _ i o t ⟨⟨o', hi, _⟩, _⟩
    exact (noDelivery0 i v o' t hi).elim

private theorem prefix0 : HealthyPrefix₂ p4 unitCodec env0 rho0 0 :=
  HealthyPrefix₂.of_legacy base0 ⟨le_rfl, le_rfl⟩ healthy0
    (fun _ ht hb => (not_lt_of_ge ht hb).elim)

-- The equal-delay regime recovers the old all-object law.
example : V2.D.HealthyPrefixDelivery env0 rho0 0 := prefix0.legacy_delivery

-- Three faulty nodes and a required tick of the one honest node.
example : (Gen.V2.Duty.faulty rho0).card = 3 := by decide +kernel
example : ¬ Gen.Pure.FaultQ p4.n (Gen.V2.Duty.faulty rho0).card := by
  intro h
  have hn : ¬ (Gen.V2.Duty.faulty rho0).card < Gen.Pure.qF p4.n := by decide +kernel
  exact hn h.lt
example : timeIdx rho0 0 = 1 := by decide +kernel
example : timeIdx rho0 (-1) = 0 ∧ timeIdx rho0 (rho0.horizon + 1) = 1 := by decide +kernel

-- A complete, nonempty healthy-prefix witness with false FaultQ.
example : CleanHistoryAt p4 unitCodec env0 rho0 0 ∧
    CleanTruncAt p4 unitCodec env0 rho0 0 :=
  ⟨cleanHistoryAt_zero prefix0, cleanTruncAt_zero prefix0⟩

example : CleanSafetyAt p4 unitCodec env0 rho0 :=
  cleanSafetyAt_of_trunc p4 unitCodec env0 rho0 schedule0 (cleanTruncAt_zero prefix0)

-- Both theorem applications keep exactly the requested premises.
example (E : Generic.Env (Fin 4)) (h : HealthyPrefix₂ p4 unitCodec E rho0 0) :
    CleanHistoryAt p4 unitCodec E rho0 0 ∧ CleanTruncAt p4 unitCodec E rho0 0 :=
  ⟨cleanHistoryAt_zero h, cleanTruncAt_zero h⟩

example (E : Generic.Env (Fin 4)) (hs : V2.D.ScheduleWellFormed E rho0)
    (ht : CleanTruncAt p4 unitCodec E rho0 rho0.horizon) :
    CleanSafetyAt p4 unitCodec E rho0 := cleanSafetyAt_of_trunc p4 unitCodec E rho0 hs ht

end AvailableChain.FGSA.Run.Tests.Zero
end

-- Non-vacuity: Δ = 1; row emitted at 14, delivered at 16; ΔF = 3.
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.Delay
private abbrev p : FGSA.Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 2, 0, by decide⟩
private abbrev E : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
private abbrev mkRun (es : List (V2.Event (Fin 1) (fgsa p unitCodec).Object)) :
    V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 17
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()
private abbrev events : List (V2.Event (Fin 1) (fgsa p unitCodec).Object) :=
  (List.range 18).foldl (fun es n =>
    let r := mkRun (es ++ [.tick 0 n])
    es ++ [.tick 0 n] ++ ((V2.D.Run.emitsAt E r es.length).filter
      (fun o => match o.payload with | .row _ => false | _ => true)).map
        (fun o => .deliver 0 o n) ++
      (if n = 16 then (V2.D.Run.emitsAt E r 21).map (fun o => .deliver 0 o n) else [])) []
private abbrev rho := mkRun events
private abbrev children (o : (fgsa p unitCodec).Object) : List (fgsa p unitCodec).Object :=
  match o.payload with
  | .proposal _ raw sup rows => raw.map (ofHead p) ++ sup.map (ofHead p) ++ rows.map (ofRow p)
  | _ => []
private theorem carries_children (o o' : (fgsa p unitCodec).Object) :
    (fgsa p unitCodec).carries o o' ↔ o' ∈ children o := by
  change carriesS p o o' ↔ _
  cases o with
  | mk a m =>
    cases m with
    | head => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | row => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | proposal b raw sup rows =>
      change _ ↔ o' ∈ (raw.map (ofHead p) ++ sup.map (ofHead p)) ++ rows.map (ofRow p)
      constructor
      · rintro (h | h | h)
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h
      · intro h
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

private def EventOK (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop :=
  match e with
    | .deliver v o t =>
      (fgsa p unitCodec).wellFormed o = true ∧
      (fgsa p unitCodec).depsPresent (V2.D.Run.stateBefore E rho i v) o = true ∧
      (fgsa p unitCodec).processed (V2.D.Run.stateBefore E rho i v) o = false ∧
      (∃ j : Fin rho.events.length, rho.events[j.val].time ≤ t ∧
        rho.events[j.val] = .tick v rho.events[j.val].time ∧ o ∈ V2.D.Run.emitsAt E rho j) ∧
      (∀ o' ∈ children o, ∃ j : Fin rho.events.length,
        rho.events[j.val].time ≤ t ∧ rho.events[j.val] = .tick 0 rho.events[j.val].time ∧
          o' ∈ V2.D.Run.emitsAt E rho j)
    | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) :
    Decidable (EventOK i e) := by
  cases e <;> unfold EventOK <;> infer_instance

private theorem checks : ∀ i : Fin rho.events.length, EventOK i rho.events[i.val] := by
  decide +kernel

private theorem lsync_schedule : V2.D.ScheduleWellFormed E rho where
  horizon_nonneg := by decide
  sorted := by
    decide +kernel
  nodup := by
    decide +kernel
  in_horizon := by
    decide +kernel
  honest_only := by
    decide +kernel
  tick_public := by
    intro v t ht
    have hall : ∀ e ∈ rho.events, 0 ≤ e.time := by
      decide +kernel
    have hn : 0 ≤ t := hall _ ht
    exact ⟨t.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  tick_total := by
    intro v _ t _ ht hh
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 17 at hh
    interval_cases t <;> decide +kernel

private theorem lsync_execution : V2.D.ExecutionValid E rho where
  toScheduleWellFormed := lsync_schedule
  wire := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.1
  deps := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.2.1
  fresh := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.2.2.1
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    obtain ⟨j, ht, hj, hem⟩ := hc.2.2.2.1
    have huv : v = u := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hh := checks ⟨i, hil⟩
    simp only [EventOK, he] at hh
    obtain ⟨j, ht, hj, hem⟩ := hh.2.2.2.2 o' ((carries_children o o').mp hc)
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩

private def Delivered (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop :=
  match e with
      | .tick v t => ∀ o ∈ V2.D.Run.emitsAt E rho i, t + fgsaDelay E.Δ 3 o ≤ 17 →
        ∃ j : Fin rho.events.length, t ≤ rho.events[j.val].time ∧
          rho.events[j.val].time < t + fgsaDelay E.Δ 3 o ∧
          rho.events[j.val] = .deliver v o rho.events[j.val].time
      | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) :
    Decidable (Delivered i e) := by
  cases e <;> unfold Delivered <;> infer_instance

private theorem lsync_delivered : ∀ i : Fin rho.events.length, Delivered i rho.events[i.val] := by
  decide +kernel

private theorem slowPrefix : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ 3) 17 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, hem⟩ w _ hd _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := lsync_delivered ⟨i, hil⟩
    simp only [Delivered, he] at hc
    obtain ⟨j, ht, hd, hj⟩ := hc o hem hd
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact ⟨_, ht, hd, j, o, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, Or.inl rfl⟩
  relay_accepted := by
    intro v _ i o t ha w _ hp
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    rw [ha.2.2] at hp
    contradiction

private abbrev row : (fgsa p unitCodec).Object := (V2.D.Run.emitsAt E rho 21)[0]'(by decide +kernel)
private theorem row_emits : V2.D.Run.emits E rho 0 row 14 := by
  refine ⟨21, ?_, ?_⟩
  · decide +kernel
  · exact List.getElem_mem _

private def NoEarlyRow (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop := match e with
  | .deliver _ o t => 15 ≤ t ∨ row ∉ o :: children o
  | _ => True
private instance (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Decidable (NoEarlyRow e) := by
  cases e <;> unfold NoEarlyRow <;> infer_instance

private theorem no_early_row : ∀ j : Fin rho.events.length, NoEarlyRow rho.events[j.val] := by
  decide +kernel

private theorem old_fails : ¬ V2.D.HealthyPrefixDelivery E rho 17 := by
  intro h
  have hx : (fgsa p unitCodec).excludes (V2.D.Run.stateBeforeTime E rho 15 0) row = false := by
    decide +kernel
  obtain ⟨t, _, htd, j, o, hj, hh⟩ :=
    h.broadcast_emitted 0 (Finset.mem_univ _) row 14 row_emits 0 (Finset.mem_univ _) (by decide) hx
  obtain ⟨hjl, he⟩ := List.getElem?_eq_some_iff.mp hj
  have hc := no_early_row ⟨j, hjl⟩
  simp only [NoEarlyRow, he] at hc
  rcases hc with hc | hc
  · exact (not_lt_of_ge hc) htd
  · apply hc
    rcases (fgsaHooks p unitCodec).handles_carries _ o row hh with rfl | hcarry
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ ((carries_children o row).mp hcarry)
private theorem base : Base₂ p unitCodec E rho where
  valid := lsync_execution
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    rcases l with (_ | _) | _
    · exact hl.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hl.elim
  cstar := by
    intro l hl
    rcases l with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hl.elim
    · exact hl.elim
  noRestart := by
    intro i v t hi
    have hm := List.mem_of_getElem? hi
    have cert : ∀ e ∈ rho.events, (match e with | .restart _ _ => true | _ => false) = false := by
      decide +kernel
    exact Bool.noConfusion (cert _ hm)
  delta := rfl

private theorem slow_clean : Clean₂ p unitCodec E rho 3 := by
  refine ⟨⟨⟨base, ⟨by decide, le_rfl⟩, slowPrefix, by decide, ?_⟩, ?_⟩, rfl⟩
  · intro t _ _
    change 0 < 1
    decide
  · change 0 < 1
    decide

private theorem old_clean_fails : ¬ Clean₂ p unitCodec E rho := by
  intro h
  apply old_fails
  have hd := h.pre.healthy
  rw [fgsaDelay_self] at hd
  exact ⟨hd.broadcast_emitted, hd.relay_accepted⟩

private theorem lsync_delay_gap : E.Δ < (3 : Time) := by decide

-- The exported safety claim applies to this slower-row run.
private theorem slow_safety : CleanSafetyAt p unitCodec E rho :=
  fgsa_cleanSafetyClaim p unitCodec E rho () ⟨slow_clean⟩

#print axioms slow_clean
#print axioms old_clean_fails
#print axioms slow_safety

end AvailableChain.FGSA.Run.Tests.Delay
