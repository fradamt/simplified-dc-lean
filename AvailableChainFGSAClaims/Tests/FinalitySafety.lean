module
public import AvailableChainFGSAClaims.Statements.Packages.Inclusion
public import AvailableChainFGSAClaims.Statements.FinalityApi -- shake: keep (equation tests)
import Mathlib.Tactic.IntervalCases

set_option linter.privateModule false
set_option linter.defProp false

@[expose] public section

-- Concrete one-node execution: Δ=1, ΔF=3, horizon 17; row at 14 is delivered at 16.
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.FinalitySafety
private abbrev s45b_p : FGSA.Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 2, 0, by decide, 2, by decide⟩
private abbrev s45b_E : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
private abbrev s45b_mkRun (es : List (V2.Event (Fin 1) (fgsa s45b_p unitCodec).Object)) :
    V2.D.Run (Fin 1) (fgsa s45b_p unitCodec) where
  honest := Finset.univ
  horizon := 17
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()
private abbrev s45b_events : List (V2.Event (Fin 1) (fgsa s45b_p unitCodec).Object) :=
  (List.range 18).foldl (fun es n =>
    let r := s45b_mkRun (es ++ [.tick 0 n])
    es ++ [.tick 0 n] ++ ((V2.D.Run.emitsAt s45b_E r es.length).filter
      (fun o => match o.payload with | .row _ => false | _ => true)).map
        (fun o => .deliver 0 o n) ++
      (if n = 16 then (V2.D.Run.emitsAt s45b_E r 21).map (fun o => .deliver 0 o n) else [])) []
private abbrev s45b_rho := s45b_mkRun s45b_events
private abbrev s45b_children (o : (fgsa s45b_p unitCodec).Object) :
    List (fgsa s45b_p unitCodec).Object :=
  match o.payload with
  | .proposal _ raw sup rows =>
      raw.map (ofHead s45b_p) ++ sup.map (ofHead s45b_p) ++ rows.map (ofRow s45b_p)
  | _ => []
private def s45b_carries_children (o o' : (fgsa s45b_p unitCodec).Object) :
    (fgsa s45b_p unitCodec).carries o o' ↔ o' ∈ s45b_children o := by
  change carriesS s45b_p o o' ↔ _
  cases o with
  | mk a m =>
    cases m with
    | head => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | row => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | proposal b raw sup rows =>
      change _ ↔ o' ∈ (raw.map (ofHead s45b_p) ++ sup.map (ofHead s45b_p)) ++
        rows.map (ofRow s45b_p)
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

private def s45b_EventOK (i : Nat) (e : V2.Event (Fin 1) (fgsa s45b_p unitCodec).Object) : Prop :=
  match e with
    | .deliver v o t =>
      (fgsa s45b_p unitCodec).wellFormed o = true ∧
      (fgsa s45b_p unitCodec).depsPresent (V2.D.Run.stateBefore s45b_E s45b_rho i v) o = true ∧
      (fgsa s45b_p unitCodec).processed (V2.D.Run.stateBefore s45b_E s45b_rho i v) o = false ∧
      (∃ j : Fin s45b_rho.events.length, s45b_rho.events[j.val].time ≤ t ∧
        s45b_rho.events[j.val] = .tick v s45b_rho.events[j.val].time ∧
        o ∈ V2.D.Run.emitsAt s45b_E s45b_rho j) ∧
      (∀ o' ∈ s45b_children o, ∃ j : Fin s45b_rho.events.length,
        s45b_rho.events[j.val].time ≤ t ∧
        s45b_rho.events[j.val] = .tick 0 s45b_rho.events[j.val].time ∧
          o' ∈ V2.D.Run.emitsAt s45b_E s45b_rho j)
    | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa s45b_p unitCodec).Object) :
    Decidable (s45b_EventOK i e) := by
  cases e <;> unfold s45b_EventOK <;> infer_instance

private def s45b_checks :
    ∀ i : Fin s45b_rho.events.length, s45b_EventOK i s45b_rho.events[i.val] := by
  decide +kernel

private def s45b_lsync_schedule : V2.D.ScheduleWellFormed s45b_E s45b_rho where
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
    have hall : ∀ e ∈ s45b_rho.events, 0 ≤ e.time := by
      decide +kernel
    have hn : 0 ≤ t := hall _ ht
    exact ⟨t.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  tick_total := by
    intro v _ t _ ht hh
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 17 at hh
    interval_cases t <;> decide +kernel

private def s45b_lsync_execution : V2.D.ExecutionValid s45b_E s45b_rho where
  toScheduleWellFormed := s45b_lsync_schedule
  wire := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := s45b_checks ⟨i, hil⟩
    simp only [s45b_EventOK, he] at hc
    exact hc.1
  deps := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := s45b_checks ⟨i, hil⟩
    simp only [s45b_EventOK, he] at hc
    exact hc.2.1
  fresh := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := s45b_checks ⟨i, hil⟩
    simp only [s45b_EventOK, he] at hc
    exact hc.2.2.1
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := s45b_checks ⟨i, hil⟩
    simp only [s45b_EventOK, he] at hc
    obtain ⟨j, ht, hj, hem⟩ := hc.2.2.2.1
    have huv : v = u := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hh := s45b_checks ⟨i, hil⟩
    simp only [s45b_EventOK, he] at hh
    obtain ⟨j, ht, hj, hem⟩ := hh.2.2.2.2 o' ((s45b_carries_children o o').mp hc)
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩

private def s45b_Delivered (i : Nat) (e : V2.Event (Fin 1) (fgsa s45b_p unitCodec).Object) : Prop :=
  match e with
      | .tick v t => ∀ o ∈ V2.D.Run.emitsAt s45b_E s45b_rho i, t + fgsaDelay s45b_E.Δ 3 o ≤ 17 →
        ∃ j : Fin s45b_rho.events.length, t ≤ s45b_rho.events[j.val].time ∧
          s45b_rho.events[j.val].time < t + fgsaDelay s45b_E.Δ 3 o ∧
          s45b_rho.events[j.val] = .deliver v o s45b_rho.events[j.val].time
      | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa s45b_p unitCodec).Object) :
    Decidable (s45b_Delivered i e) := by
  cases e <;> unfold s45b_Delivered <;> infer_instance

private def s45b_lsync_delivered :
    ∀ i : Fin s45b_rho.events.length, s45b_Delivered i s45b_rho.events[i.val] := by
  decide +kernel

private def s45b_slowPrefix :
    Gen.V2.Duty.HealthyPrefixDeliveryBy s45b_E s45b_rho (fgsaDelay s45b_E.Δ 3) 17 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, hem⟩ w _ hd _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := s45b_lsync_delivered ⟨i, hil⟩
    simp only [s45b_Delivered, he] at hc
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

private def s45b_base : Base₂ s45b_p unitCodec s45b_E s45b_rho where
  valid := s45b_lsync_execution
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
    have cert : ∀ e ∈ s45b_rho.events,
        (match e with | .restart _ _ => true | _ => false) = false := by
      decide +kernel
    exact Bool.noConfusion (cert _ hm)
  delta := rfl

private def s45b_slow_clean : Clean₂ s45b_p unitCodec s45b_E s45b_rho 3 := by
  refine ⟨⟨⟨s45b_base, ⟨by decide, le_rfl⟩, s45b_slowPrefix, by decide, ?_⟩, ?_⟩, rfl⟩
  · intro t _ _
    change 0 < 1
    decide
  · change 0 < 1
    decide


private abbrev s45b_propIdx : Nat :=
  s45b_rho.events.findIdx (fun e => e == .tick 0 (SA.proposalTime s45b_p.toParams 1))

private abbrev s45b_proposal : (fgsa s45b_p unitCodec).Object :=
  (V2.D.Run.emitsAt s45b_E s45b_rho s45b_propIdx)[0]'(by decide +kernel)
private abbrev s45b_block : Block :=
  ((fgsaInterface s45b_p unitCodec).block s45b_proposal.payload).getD .genesis

private def s45b_honestProposal :
    HonestProposal s45b_E s45b_rho (fgsaInterface s45b_p unitCodec) 1 s45b_block := by
  constructor
  · rw [Gen.V2.Duty.HonestSlot_def]
    exact ⟨by decide, Finset.mem_univ _⟩
  · refine ⟨s45b_proposal, ⟨s45b_propIdx, ?_, ?_⟩, ?_⟩
    · decide +kernel
    · exact List.getElem_mem _
    · decide +kernel

private def s45b_cleanInclusion :
    CleanInclusionPrem s45b_p unitCodec s45b_E s45b_rho ⟨1, s45b_block⟩ 3 :=
  ⟨s45b_slow_clean, s45b_honestProposal, by decide⟩

private def s45b_exactProposal :
    ExactProposalPrem s45b_p unitCodec s45b_E s45b_rho ⟨1, s45b_block⟩ 3 :=
  ⟨s45b_slow_clean, s45b_honestProposal, by decide⟩

-- The packages have inhabited premises and a non-genesis, honestly emitted block.
example : s45b_block ≠ .genesis ∧ (1 : Time) < 3 := by decide +kernel
example : Nonempty
    (CleanInclusionPrem s45b_p unitCodec s45b_E s45b_rho ⟨1, s45b_block⟩ 3) :=
  ⟨s45b_cleanInclusion⟩
example : Nonempty
    (ExactProposalPrem s45b_p unitCodec s45b_E s45b_rho ⟨1, s45b_block⟩ 3) :=
  ⟨s45b_exactProposal⟩

example : FinalityFinalizedAt s45b_p .genesis .genesis 0 := by
  rw [FinalityFinalizedAt_def]
  decide +kernel

#print axioms s45b_cleanInclusion
#print axioms s45b_exactProposal

end AvailableChain.FGSA.Run.Tests.FinalitySafety
end
