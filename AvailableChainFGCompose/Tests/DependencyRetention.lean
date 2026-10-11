module
public import AvailableChainFGCompose.Proofs.Dependency

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.DependencyRetention

private def dr_history : FGHistoricalReads Bool Nat where
  acceptedBlocks _ := ∅
  acceptedBodies _ := []
  erase _ := .genesis
  root b := ⟨b⟩
  parent b := b - 1
  slot b := b
  readBlock _ _ := none
  preceq := (· ≤ ·)
  depth := id
  lca _ _ := .genesis

private def dr_reads : FGDependencyReads Bool Nat Nat Unit where
  accepted _ _ := False
  refused _ _ _ _ := False
  pending st b o := st = true ∧ b = 2 ∧ o = 7
  originAvailable _ b o := b = 2 ∧ o = 7
  validBody b := b = 2
  priorChecks _ _ := True
  timely _ _ := True
  conflictsFinal _ _ := False
  latest _ := ()
  notified _ _ := True
  matching _ _ := False
  companionHeld _ _ := False
  latestKey _ _ := none
  latestCompanion _ _ := none

private def dr_leaf : FGDependencyLeaf Bool Nat Nat where
  step _ _ _ _ _ := False
  callback _ _ _ _ := False
  report _ _ _ _ := False
  initial := false
  genesis := 0

private def dr_keep : FGDependencyStepKind → Unit → Bool → Bool → Prop :=
  fun _ _ a b => a = b

private theorem dr_keep_laws :
    FGDependencyStepLaws dr_history dr_reads dr_leaf dr_keep (fun s _ => s)
      (fun _ _ => False) where
  accepted_keep _ _ _ _ _ _ h := h.elim
  refused_keep _ _ _ _ _ _ _ _ h := h.elim
  pending_effect _ _ a b body origin h pending := by
    change a = b at h
    subst b
    exact ⟨pending.2, Or.inl pending⟩
  origin_keep _ _ _ _ _ _ _ h := h
  metadata_fg_eq _ _ _ _ _ _ _ := rfl
  insertion_leaf _ _ _ _ _ _ h _ := h.elim
  one_body _ _ _ _ _ h := h.elim
  restore_exact _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  no_signing _ _ _ _ _ := not_false

/-- Every named kind retains the original receipt, including restart before any PC. -/
private theorem dr_all_step_kinds (kind : FGDependencyStepKind) :
    Effect dr_history dr_reads true 2 7 :=
  dependency_effect_step dr_keep_laws (kind := kind) (x := ()) rfl
    ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩

private theorem dr_erase_then_quiesce :
    dependencyClosed dr_history dr_reads false ∧ ¬ Effect dr_history dr_reads false 2 7 := by
  constructor
  · intro work
    cases work <;> simp_all [dr_reads, dependencyResolved, dependencyRefused]
  · simp [Effect, dependencyResolved, dependencyRefused, dr_reads]

private theorem dr_erasure_rejected (kind : FGDependencyStepKind) :
    ¬ FGDependencyStepLaws dr_history dr_reads dr_leaf
      (fun k (_ : Unit) a b => k = kind ∧ a = true ∧ b = false)
      (fun s _ => s) (fun _ _ => False) := by
  intro laws
  exact dr_erase_then_quiesce.2
    (laws.pending_effect kind () true false 2 7 ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩)

private def dr_refusedReads : FGDependencyReads Nat Nat Nat Unit where
  accepted _ b := b = 0
  refused st b r pr := 0 < b ∧ b ≤ st ∧ r = ⟨b⟩ ∧ pr = ⟨b - 1⟩
  pending st b o := st < b ∧ b ≤ 3 ∧ o = b
  originAvailable _ b o := o = b
  validBody b := b ≤ 3
  priorChecks _ _ := True
  timely _ _ := True
  conflictsFinal _ _ := True
  latest _ := ()
  notified _ _ := True
  matching _ _ := False
  companionHeld _ _ := False
  latestKey _ _ := none
  latestCompanion _ _ := none

private def dr_refusedHistory : FGHistoricalReads Nat Nat where
  acceptedBlocks _ := {.genesis}
  acceptedBodies _ := [0]
  erase _ := .genesis
  root b := ⟨b⟩
  parent b := b - 1
  slot b := b
  readBlock _ _ := none
  preceq := (· ≤ ·)
  depth := id
  lca _ _ := .genesis

private def dr_refusalLeaf : FGDependencyLeaf Nat Nat Nat where
  step a b o result z := a = 0 ∧ b = 1 ∧ o = 1 ∧ result = .definitiveRefused ∧ z = 1
  callback _ _ _ _ := False
  report _ _ _ _ := True
  initial := 0
  genesis := 0

private def dr_directEvent (k b o : Nat) : Prop := k = 0 ∧ b = 1 ∧ o = 1
private def dr_inheritEvent (k b o : Nat) : Prop := k + 1 = b ∧ o = b ∧ 1 ≤ k

private theorem dr_direct_and_recursive_evidence :
    FGDependencyRefusalEvidence dr_refusedHistory dr_refusedReads dr_refusalLeaf
      id dr_directEvent dr_inheritEvent 3 3 3 := by
  have h1 : FGDependencyRefusalEvidence dr_refusedHistory dr_refusedReads dr_refusalLeaf
      id dr_directEvent dr_inheritEvent 1 1 1 := by
    refine .direct 0 1 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [dr_directEvent, dr_refusedReads, dr_refusedHistory, dr_refusalLeaf]
  have h2 : FGDependencyRefusalEvidence dr_refusedHistory dr_refusedReads dr_refusalLeaf
      id dr_directEvent dr_inheritEvent 2 2 2 := by
    refine .inherited 1 1 2 2 1 ?_ ?_ ?_ ?_ ?_ h1 ?_ <;>
      simp [dr_inheritEvent, dr_refusedReads, dr_refusedHistory, dependencyRefused]
  refine .inherited 2 2 3 3 2 ?_ ?_ ?_ ?_ ?_ h2 ?_ <;>
    simp [dr_inheritEvent, dr_refusedReads, dr_refusedHistory, dependencyRefused]

private theorem dr_late_child_always_pending_rejected :
    FGDependencyEnabled dr_refusedHistory dr_refusedReads 1 := by
  exact .inherit 2 2 ⟨by decide, by decide, rfl⟩
    ⟨by decide, by decide, rfl, rfl⟩ (by
      simp [dependencyResolved, dependencyRefused, dr_refusedReads, dr_refusedHistory])

/-- The reverse order has the same enabled recursive work after the parent report. -/
private theorem dr_recursive_child_rejected :
    FGDependencyEnabled dr_refusedHistory dr_refusedReads 2 := by
  exact .inherit 3 3 ⟨by decide, by decide, rfl⟩
    ⟨by decide, by decide, rfl, rfl⟩ (by
      simp [dependencyResolved, dependencyRefused, dr_refusedReads, dr_refusedHistory])

private theorem dr_both_orders_and_restart :
    dependencyRefused dr_refusedHistory dr_refusedReads (max (max 0 1) 3) 3 ∧
    dependencyRefused dr_refusedHistory dr_refusedReads (max (max 0 3) 1) 3 ∧
    dependencyRefused dr_refusedHistory dr_refusedReads (id 3) 3 := by
  simp [dependencyRefused, dr_refusedHistory, dr_refusedReads]

/-- An early read of the concrete retained child cannot have read closure. -/
private theorem dr_early_read_rejected :
    ¬ FGDependencyReadClosureLaws dr_refusedHistory dr_refusedReads
      (fun _ (_ : Unit) _ _ => True) id (fun _ => ⟨0, .ac, 0, 1, 1⟩)
      (fun _ _ st => st = 1) := by
  intro laws
  exact laws.read_closed () 0 1 rfl dr_late_child_always_pending_rejected

private theorem dr_held_conflict_report
    {State Body Origin Latest : Type} {H : FGHistoricalReads State Body}
    {D : FGDependencyReads State Body Origin Latest}
    {L : FGDependencyLeaf State Body Origin}
    {Arrival : State → Body → Origin → State → Prop} {Notify : State → Body → State → Prop}
    (laws : FGDependencyArrivalLeafLaws H D L Arrival Notify) {a b o z}
    (leaf : L.step a b o .definitiveRefused z) :
    D.validBody b ∧ D.priorChecks a b ∧ D.timely a b ∧ ¬ D.accepted a b ∧
    D.accepted a (H.parent b) ∧ D.conflictsFinal a b := by
  have h := (laws.direct_refusal_iff a b o z ⟨_, leaf⟩).mp leaf
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem dr_invalid_future_duplicate_missing_no_new_refusal
    {State Body Origin Latest : Type} {H : FGHistoricalReads State Body}
    {D : FGDependencyReads State Body Origin Latest}
    {L : FGDependencyLeaf State Body Origin}
    {Arrival : State → Body → Origin → State → Prop} {Notify : State → Body → State → Prop}
    (laws : FGDependencyArrivalLeafLaws H D L Arrival Notify) {a b o z result}
    (leaf : L.step a b o result z)
    (bad : result = .invalid ∨ result = .future ∨ result = .duplicate ∨ result = .pending)
    (fresh : ¬ dependencyRefused H D a b) : ¬ dependencyRefused H D z b :=
  fun refused => fresh (laws.rejected_no_refusal a z b o result leaf bad refused)

private theorem dr_no_acceptance_callback_for_refusal
    {State Body Origin Latest : Type} {H : FGHistoricalReads State Body}
    {D : FGDependencyReads State Body Origin Latest}
    {L : FGDependencyLeaf State Body Origin}
    {Arrival : State → Body → Origin → State → Prop} {Notify : State → Body → State → Prop}
    (laws : FGDependencyArrivalLeafLaws H D L Arrival Notify) {a b o z}
    (refused : dependencyRefused H D z b) : ¬ L.callback a b o z :=
  fun callback => (laws.callback_only a z b o callback).2.2 refused

private theorem dr_late_arrival_pending_rejected :
    ¬ FGDependencyArrivalLeafLaws dr_refusedHistory dr_refusedReads dr_refusalLeaf
      (fun a b o z => a = 1 ∧ b = 2 ∧ o = 2 ∧ z = 1) (fun _ _ _ => False) := by
  intro laws
  have refused := (laws.arrival_inherits 1 1 2 2 ⟨rfl, rfl, rfl, rfl⟩
    (by change (2 : Nat) ≤ 3; decide) ⟨by decide, by decide, rfl, rfl⟩).1
  have impossible : (2 : Nat) ≤ 1 := refused.2.1
  omega

#print axioms dr_late_arrival_pending_rejected

#print axioms dr_direct_and_recursive_evidence
#print axioms dr_keep_laws
#print axioms dr_all_step_kinds
#print axioms dr_erase_then_quiesce
#print axioms dr_erasure_rejected
#print axioms dr_late_child_always_pending_rejected
#print axioms dr_recursive_child_rejected
#print axioms dr_both_orders_and_restart
#print axioms dr_early_read_rejected
#print axioms dr_held_conflict_report
#print axioms dr_invalid_future_duplicate_missing_no_new_refusal
#print axioms dr_no_acceptance_callback_for_refusal

end AvailableChain.FGCompose.Tests.DependencyRetention
end
