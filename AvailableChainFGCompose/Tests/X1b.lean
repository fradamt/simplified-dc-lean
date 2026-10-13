module
public import AvailableChainFGCompose.Proofs.ExecutionHistory
public import AvailableChainFGCompose.Tests.DependencyOrigins

set_option linter.privateModule false

public section

/-! X1b controls. Levels: (a), (b), (d) are driver-interface executions with proved c3
trace laws (finite interface models, not ExecutionValid protocol fixtures); (c) is a
generic observation; the converse control is a generic event fold. -/

namespace AvailableChain.FGCompose.Tests.X1b
open AvailableChain.SimplexFG AvailableChain.FGCompose.Tests.DependencyOrigins

/-! ### (a), (d) on the do_run driver fixture -/

private noncomputable abbrev doObs : FGExecutionObs Bool do_protocol :=
  driverFGExecutionObs do_env do_run do_driver (fun _ => do_trace) (fun _ => do_op)

private theorem do_hacc : ∀ k b, k ≤ do_trace.length →
    (b ∈ do_history.acceptedBodies (do_trace.state k) ↔
      do_reads.accepted (do_trace.state k) b) := by
  intro k b hk
  change k ≤ 14 at hk
  revert b
  interval_cases k <;> decide

private theorem do_origin :
    FGAcceptedBodyOrigin do_env do_run do_history do_wireReads doObs false :=
  accepted_body_origin_driver_at (Leaf := do_leafProtocol) do_env do_run do_history do_wireReads
    do_reads do_leaf do_step do_driver (fun _ => do_trace) (fun _ => do_op) do_arrival do_notify
    id id do_read false do_trace_laws do_hacc

/-- (a) The child body 2, received first, is admitted at microstep 9 by the drain of the
parent's arrival event 2; the bridge returns its own original token. -/
private theorem child_admitted_by_parent :
    ∃ o, doObs.accepts false 9 o ∧
      FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧ o = do_child ∧
      doObs.start false 2 ≤ 9 ∧ 9 < doObs.done false 2 ∧
      do_run.events[2]? = some (.deliver false (do_wire 1) 1) := by
  have hnew : (2 : Fin 4) ∈ do_history.acceptedBodies (doObs.cutState false (9 + 1)) := by decide
  have hold : (2 : Fin 4) ∉ do_history.acceptedBodies (doObs.cutState false 9) := by decide
  rcases do_origin.origin 9 2 (by decide) hnew hold with
    ⟨o, ⟨_, b, hop⟩, horig⟩ | ⟨j, t, wire, hj, _, hd, _, _⟩
  · have ho : o = do_child := by
      change FGDependencyOperation.leaf 2 do_child .accepted = .leaf b o .accepted at hop
      cases hop; rfl
    exact ⟨o, ⟨by decide, b, hop⟩, horig, ho, by decide, by decide, rfl⟩
  · have hj4 : j < 4 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j <;> first | exact absurd hd (by decide) | simp at hj

/-- (d) The delayed old row: the acceptance at microstep 9 (time 1) carries the unchanged
original receipt of event 0 (time 0, same wire, rows equal to the body rows). -/
private theorem delayed_old_row :
    ∃ o, doObs.accepts false 9 o ∧
      FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧
      o.eventIndex = 0 ∧ o.receiptTime = 0 ∧ doObs.cutTime false 9 = 1 ∧
      o.wire = do_wire 2 ∧
      do_wireReads.decodedRows o.wire = do_wireReads.bodyRows 2 := by
  obtain ⟨o, hacc, horig, rfl, _⟩ := child_admitted_by_parent
  exact ⟨_, hacc, horig, rfl, rfl, rfl, rfl, horig.rows⟩

/-! ### (b) Admission during a completed restart: a new driver fixture -/

/-- The child arrives at 0, the parent at 1 is accepted, and the child's prior checks pass
only after the restart's reconstruction at 2; the restart's first drain admits the child. -/
noncomputable abbrev rs_run : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false (do_wire 2) 0, .deliver false (do_wire 1) 1,
    .restart false 2] }

noncomputable abbrev rs_history : FGHistoricalReads Nat (Fin 4) :=
  { do_history with
    acceptedBlocks := fun st => (if 6 ≤ st then [do_body 0, do_body 1, do_body 2]
      else if 3 ≤ st then [do_body 0, do_body 1] else [do_body 0]).toFinset
    acceptedBodies := fun st => if 6 ≤ st then [0, 1, 2] else if 3 ≤ st then [0, 1] else [0] }

noncomputable abbrev rs_child : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 0, do_wire 2, 0, 0⟩
noncomputable abbrev rs_parent : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 1, do_wire 1, 1, 0⟩

noncomputable abbrev rs_reads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat where
  accepted st b := b = 0 ∨ (b = 1 ∧ 3 ≤ st) ∨ (b = 2 ∧ 6 ≤ st)
  refused _ _ _ _ := False
  pending st b o := (b = 2 ∧ 1 ≤ st ∧ st < 6 ∧ o = rs_child) ∨
    (b = 1 ∧ st = 2 ∧ o = rs_parent)
  originAvailable st b o := (b = 2 ∧ 1 ≤ st ∧ o = rs_child) ∨
    (b = 1 ∧ 2 ≤ st ∧ o = rs_parent)
  validBody b := b ≠ 3
  priorChecks st b := (b = 1 ∧ st = 2) ∨ (b = 2 ∧ st = 5)
  timely _ _ := True
  conflictsFinal _ _ := False
  latest := id
  notified st b := b = 0 ∨ (b = 1 ∧ 4 ≤ st) ∨ (b = 2 ∧ 7 ≤ st)
  matching _ b := b = 2
  companionHeld st b := b = 2 ∧ 7 ≤ st
  latestKey _ _ := some (2, do_history.root 2)
  latestCompanion st _ := if 7 ≤ st then some 2 else none

noncomputable abbrev rs_leafProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
    if st = 2 ∧ wire.payload = 1 then 3
    else if st = 5 ∧ wire.payload = 2 then 6 else st }

noncomputable abbrev rs_leaf : FGDependencyLeaf Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) where
  step a b o outcome z := outcome = .accepted ∧
    ((a = 2 ∧ b = 1 ∧ o = rs_parent ∧ z = 3) ∨
     (a = 5 ∧ b = 2 ∧ o = rs_child ∧ z = 6))
  callback a b o z := (a = 2 ∧ b = 1 ∧ o = rs_parent ∧ z = 3) ∨
    (a = 5 ∧ b = 2 ∧ o = rs_child ∧ z = 6)
  report _ _ _ _ := False
  initial := 0
  genesis := 0

noncomputable abbrev rs_step (kind : FGDependencyStepKind) (_ : Bool) (a z : Nat) : Prop :=
  a = z ∨ (kind = .arrival ∧ ((a = 0 ∧ z = 1) ∨ (a = 1 ∧ z = 2))) ∨
    (kind = .leafRetry ∧ ((a = 2 ∧ z = 3) ∨ (a = 5 ∧ z = 6))) ∨
    (kind = .notification ∧ ((a = 3 ∧ z = 4) ∨ (a = 6 ∧ z = 7))) ∨
    (kind = .ordinary ∧ a = 4 ∧ z = 5)

noncomputable abbrev rs_driver : FGDependencyDriver Bool (Fin 4) do_protocol where
  enter st wire _ := if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st
  enterProgram st wire _ := .finish (if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st)
  hookProgram st op := match op with
    | .leaf b _ _ => .finish (rs_leafProtocol.process st (do_wire b))
    | .notification b _ =>
        .finish (if st = 3 ∧ b = 1 then 4 else if st = 6 ∧ b = 2 then 7 else st)
    | .reconstruct _ => .finish (if st = 4 then 5 else st)
    | _ => .finish st
  drain st := if 2 ≤ st ∧ st ≤ 3 then 4 else if 5 ≤ st ∧ st ≤ 6 then 7 else st
  reconstruct st _ := if st = 4 then 5 else st
  rebuild st _ := st
  retry st b _ _ := rs_leafProtocol.process st (do_wire b)
  work st e := if st = 2 then
    [.step (.leaf 1 rs_parent .accepted), .step (.notification 1 rs_parent)]
    else match e with
      | .deliver _ _ _ => if st = 1 then [.step .idle] else []
      | .restart _ t => if st = 4 then [.step (.reconstruct t),
          .step (.leaf 2 rs_child .accepted), .step (.notification 2 rs_child),
          .step (.rebuild t)] else [.step (.reconstruct t), .step (.rebuild t)]
      | _ => []
  inheritRefusal st _ _ := st
  notify st b _ := if st = 3 ∧ b = 1 then 4 else if st = 6 ∧ b = 2 then 7 else st
  replay st _ _ := st

noncomputable abbrev rs_op (k : Nat) :
    FGDependencyOperation (Fin 4) (FGReceiptToken Bool do_protocol.Object) do_protocol.Object :=
  match k with
  | 0 => .arrival 2 rs_child
  | 3 => .arrival 1 rs_parent
  | 4 => .leaf 1 rs_parent .accepted
  | 5 => .notification 1 rs_parent
  | 7 => .restore 2
  | 8 => .reconstruct 2
  | 9 => .leaf 2 rs_child .accepted
  | 10 => .notification 2 rs_child
  | 11 => .rebuild 2
  | _ => .idle

noncomputable abbrev rs_trace : FGDependencyTrace Nat where
  length := 12
  state k := [0, 1, 1, 1, 2, 3, 4, 4, 4, 5, 6, 7, 7][k]?.getD 7
  time k := [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2][k]?.getD 2
  start j := [0, 3, 7][j]?.getD 12
  done j := [2, 6, 12][j]?.getD 12
  readCut _ := 12
  entryCut j := [1, 4, 8][j]?.getD 12
  dutyCut j := [2, 6, 11][j]?.getD 12
  hookRead _ _ _ _ _ := False

noncomputable abbrev rs_arrival (a : Nat) (b : Fin 4)
    (o : FGReceiptToken Bool do_protocol.Object) (z : Nat) : Prop :=
  (a = 0 ∧ b = 2 ∧ o = rs_child ∧ z = 1) ∨ (a = 1 ∧ b = 1 ∧ o = rs_parent ∧ z = 2)

noncomputable abbrev rs_notify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  (a = 3 ∧ b = 1 ∧ z = 4) ∨ (a = 6 ∧ b = 2 ∧ z = 7)

private theorem rs_child_origin :
    FGReceiptOrigin do_env rs_run rs_history do_wireReads false 2 rs_child := by
  constructor <;> rfl

private theorem rs_parent_origin :
    FGReceiptOrigin do_env rs_run rs_history do_wireReads false 1 rs_parent := by
  constructor <;> rfl

private theorem rs_closed (st : Nat) (h : st = 1 ∨ st = 4 ∨ st = 7) :
    dependencyClosed rs_history rs_reads st := by
  intro work
  cases work with
  | inherit b o pending refused unresolved => exact refused.elim
  | retry b o pending valid prior timely held unresolved =>
    rcases h with rfl | rfl | rfl <;> simp_all
  | notify b resolved missing =>
    rcases h with rfl | rfl | rfl <;> simp_all [dependencyResolved, dependencyRefused]
  | companion b accepted matching missing =>
    rcases h with rfl | rfl | rfl <;> simp_all

private theorem rs_events_bound {j : Nat} {e : V2.Event Bool do_protocol.Object}
    (h : rs_run.events[j]? = some e) : j < 3 :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem rs_arrival_laws :
    FGDependencyArrivalLeafLaws rs_history rs_reads rs_leaf rs_arrival rs_notify where
  direct_refusal_iff a b o z invoked := by
    simp
  arrival_effect a z b o arrived valid timely := by
    rcases arrived with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [Effect, dependencyResolved, dependencyRefused]
  arrival_inherits _ _ _ _ _ _ h := h.elim
  arrival_pending a z b o arrived valid timely fresh missing noRefusal noSelf := by
    rcases arrived with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨rfl, by decide, by decide, rfl⟩
    · exact (missing (Or.inl rfl)).elim
  held_parent_accepts a z b o invoked := by
    obtain ⟨result, _, step⟩ := invoked
    rcases step with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [do_body]
  accepted_callback _ _ _ _ leaf := leaf.2
  callback_only a z b o callback := by
    refine ⟨⟨rfl, callback⟩, ?_, not_false⟩
    rcases callback with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide +kernel
  refusal_report _ _ _ _ h := h.elim
  rejected_no_refusal _ _ _ _ _ _ _ h := h.elim
  notification_resolved a z b notify := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [dependencyResolved, dependencyRefused]
  notification_keys _ _ _ _ := rfl
  notification_fields a z b i notify unmatched := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rfl
    · simp at unmatched
  notification_matching a z b i slot notify held matching := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have bad : (2 : Nat) = 1 :=
        congrArg BlockId.value (congrArg Prod.snd (Option.some.inj matching))
      omega
    · rfl
  refused_notification _ _ _ _ refused := refused.elim
  callback_latest a z b notify accepted := by
    rcases notify with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

private theorem rs_micro_steps (k : Nat) (hk : k < rs_trace.length) :
    ∃ kind, rs_step kind false (rs_trace.state k) (rs_trace.state (k + 1)) := by
  change k < 12 at hk
  interval_cases k <;> first
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)))⟩
    | exact ⟨.ordinary, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))⟩
    | exact ⟨.ordinary, Or.inl rfl⟩

noncomputable abbrev rs_read (_ : Bool) (_ _ : Nat) : Prop := False

theorem rs_trace_laws :
    FGDependencyTraceLaws do_env rs_run false rs_history do_wireReads rs_reads rs_leaf
      rs_step rs_trace rs_driver rs_op rs_arrival rs_notify
      (Leaf := rs_leafProtocol) id id rs_read where
  arrival_laws := rs_arrival_laws
  initial := rfl
  initial_accepted b h := by simpa [rs_reads, do_protocol, rs_leaf] using h
  micro_step := rs_micro_steps
  external_step j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  step_kind k hk := by
    change k < 12 at hk
    interval_cases k <;> simp [dependencyOperationKind, rs_op, rs_step]
  operation_bound k hk := by
    change k < 12 at hk
    interval_cases k <;> simp only [rs_op]
    all_goals first
      | exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, rs_child_origin, rfl⟩
      | exact ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl, rs_parent_origin, rfl⟩
      | exact ⟨rfl, 2, rfl, rfl⟩
      | exact ⟨rfl, 2, rfl, by decide, by decide, fun q lo hi => by
          norm_num at lo hi; omega⟩
      | simp [dependencyResolved, dependencyRefused, rs_notify]
  delivery_entry j wire t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  work_execution j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  work_step j e k h lo hi := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [rs_trace] at lo hi <;> interval_cases k <;> rfl
  hook_correspondence j e index kind cut st h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      change False ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _ <;>
      simp
  hook_reads j e r h member := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member <;> cases member
  receipt_entry j wire t b h awake valid decoded := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        rs_op, rs_arrival]
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        rs_op, rs_arrival]
    · cases h
  entry_boundary j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      exact ⟨rfl, by decide, by decide, rfl, rfl⟩
  drain_operations j e k h lo hi := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [rs_trace] at lo hi <;> interval_cases k <;> simp [rs_op]
    all_goals intro q lo hi; omega
  boundary_idle k hk outside := by
    change k < 12 at hk
    interval_cases k <;> simp only [rs_op]
    all_goals exfalso; apply outside
    all_goals first
      | exact ⟨0, _, rfl, by decide, by decide⟩
      | exact ⟨1, _, rfl, by decide, by decide⟩
      | exact ⟨2, _, rfl, by decide, by decide⟩
  raw_restore j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  raw_clock j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
  restore_data _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  reconstruct_program _ _ := rfl
  reconstruct_data st t := by
    dsimp only
    by_cases h4 : st = 4
    · subst h4
      rw [ite_eq_left (rfl : (4 : Nat) = 4)]
      refine ⟨rfl, rfl, ?_, fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, fun _ _ h => h.elim⟩
      · intro b; revert b; decide
      · intro b o; simp
      · intro b o; simp
      · intro b; revert b; decide
      · intro b o h; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1
    · rw [ite_eq_right h4]
      refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl,
        fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, fun _ _ h => h.elim⟩
      intro b o h; rcases h with ⟨h1, -, -, h2⟩ | ⟨h1, -, -, h2⟩ <;> omega
  restart_reconstruct j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    exact ⟨by decide, rfl⟩
  restart_drain_closed j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    exact rs_closed 7 (Or.inr (Or.inr rfl))
  restart_replay_order j t k b o h lo hi op := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    norm_num [rs_trace] at lo hi ⊢
    interval_cases k <;> simp_all [rs_op]
  rebuild_program _ _ := rfl
  rebuild_data st _ := by
    refine ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
    · intro b o h
      rcases h with (⟨rfl, rfl, rfl, hz⟩ | ⟨rfl, rfl, rfl, hz⟩) <;> cases hz
    · intro b o h; exact h.elim
  restart_rebuild j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
    refine ⟨11, by decide, by decide, rfl, ?_, ?_, ?_, rfl⟩
    · intro q t lo hi op
      norm_num [rs_trace] at lo hi
      interval_cases q <;> simp_all [rs_op]
    · intro q lo hi
      norm_num [rs_trace] at lo hi
      omega
    · intro q lo hi
      norm_num [rs_trace] at lo hi
      omega
  clock_no_insert _ _ := ⟨rfl, rfl⟩
  refusal_creation _ _ _ refused _ := refused.elim
  refusal_history _ _ _ refused := refused.elim
  notification_creation k b hk notified fresh := by
    change k < 12 at hk
    interval_cases k <;> simp_all
    all_goals rcases notified with rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩, 4, by decide, by simp [rs_op]⟩
    · exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩, 9, by decide, by simp [rs_op]⟩
  actual_read i st := by
    constructor
    · intro h; exact h.elim
    · rintro ⟨j, e, kind, he, required, _, _⟩
      have hj := rs_events_bound he
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at he <;> subst e <;>
        simp [dependencyReadRequired] at required
  read_order j e kind h required := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      simp [dependencyReadRequired] at required
  wire_validation wire b valid decoded := by
    have hb : wire.payload = b := Option.some.inj decoded
    simpa [do_protocol, rs_reads, hb] using valid
  origin_valid k b o hk origin := by
    change k ≤ 12 at hk
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · refine ⟨rs_child_origin, ?_⟩
      interval_cases k <;> simp_all
    · refine ⟨rs_parent_origin, ?_⟩
      interval_cases k <;> simp_all
  leaf_step k b o z hk leaf hz := by
    change k < 12 at hk
    rcases leaf with ⟨_, (⟨ha, rfl, rfl, rfl⟩ | ⟨ha, rfl, rfl, rfl⟩)⟩
    · refine ⟨rs_parent_origin, ?_, ?_⟩
      · clear hz
        interval_cases k <;> simp_all
      · change 3 = rs_leafProtocol.process (rs_trace.state k) (do_wire 1)
        rw [ha]
        rfl
    · refine ⟨rs_child_origin, ?_, ?_⟩
      · clear hz
        interval_cases k <;> simp_all
      · change 6 = rs_leafProtocol.process (rs_trace.state k) (do_wire 2)
        rw [ha]
        rfl
  origin_attribution k b hk held fresh := by
    have key : (k = 4 ∧ b = 1) ∨ (k = 9 ∧ b = 2) := by
      change k < 12 at hk
      revert held fresh
      revert b
      interval_cases k <;> decide
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rs_parent, ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inr ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
    · exact ⟨rs_child, ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
        Or.inl ⟨rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
  read_correspondence i st read := read.elim
  order_and_time i j ei ej hi hj le := by
    have bi := rs_events_bound hi
    have bj := rs_events_bound hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hi hj <;> subst ei <;> subst ej <;>
      decide +kernel
  finite_segment j e h := by
    have hj := rs_events_bound h
    interval_cases j <;> decide +kernel
  event_drain j y wire t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq, V2.Event.deliver.injEq] at h
    · exact rs_closed 1 (Or.inl rfl)
    · exact rs_closed 4 (Or.inr (Or.inl rfl))
    · cases h
  entry_drain j e h := by
    have hj := rs_events_bound h
    interval_cases j
    · exact rs_closed 1 (Or.inl rfl)
    · exact rs_closed 4 (Or.inr (Or.inl rfl))
    · exact rs_closed 7 (Or.inr (Or.inr rfl))
  segment_time j e k h lower upper := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [rs_trace] at lower upper <;> interval_cases k <;> rfl
  event_order i j ei ej hi hj lt := by
    have bi := rs_events_bound hi
    have bj := rs_events_bound hj
    interval_cases i <;> interval_cases j <;> simp_all
  completion_cut j e deadline h strict := by
    have hj := rs_events_bound h
    refine ⟨?_, ?_, ?_⟩
    · interval_cases j <;> decide +kernel
    · interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact strict
    · intro i ei hi before
      have bi := rs_events_bound hi
      interval_cases i <;> interval_cases j <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi h <;> subst ei <;> subst e <;>
        norm_num [rs_trace] at before <;>
        exact lt_of_le_of_lt (by decide) strict
  tick_records j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h
  atomic_tick j t h := by
    have hj := rs_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h

private noncomputable abbrev rsObs : FGExecutionObs Bool do_protocol :=
  driverFGExecutionObs do_env rs_run rs_driver (fun _ => rs_trace) (fun _ => rs_op)

private theorem rs_hacc : ∀ k b, k ≤ rs_trace.length →
    (b ∈ rs_history.acceptedBodies (rs_trace.state k) ↔
      rs_reads.accepted (rs_trace.state k) b) := by
  intro k b hk
  change k ≤ 12 at hk
  revert b
  interval_cases k <;> decide

private theorem rs_origin :
    FGAcceptedBodyOrigin do_env rs_run rs_history do_wireReads rsObs false :=
  accepted_body_origin_driver_at (Leaf := rs_leafProtocol) do_env rs_run rs_history do_wireReads
    rs_reads rs_leaf rs_step rs_driver (fun _ => rs_trace) (fun _ => rs_op) rs_arrival rs_notify
    id id rs_read false rs_trace_laws rs_hacc

/-- (b) Admission during a completed restart: body 2 enters accepted storage at microstep 9,
after the reconstruction at 8, inside the segment [7, 12) of the restart event 2. The bridge
returns the original token of event 0 (time 0, epoch 0), not a restart-time token. -/
private theorem child_admitted_in_restart :
    ∃ o, rsObs.accepts false 9 o ∧
      FGReceiptOrigin do_env rs_run rs_history do_wireReads false 2 o ∧ o = rs_child ∧
      rs_run.events[2]? = some (.restart false 2) ∧ rsObs.start false 2 < 8 ∧
      rs_op 8 = .reconstruct 2 ∧ 9 < rsObs.done false 2 ∧
      o.receiptTime = 0 ∧ o.receiptEpoch = 0 ∧ dependencyReceiverEpoch rs_run false 3 = 3 := by
  have hnew : (2 : Fin 4) ∈ rs_history.acceptedBodies (rsObs.cutState false (9 + 1)) := by decide
  have hold : (2 : Fin 4) ∉ rs_history.acceptedBodies (rsObs.cutState false 9) := by decide
  rcases rs_origin.origin 9 2 (by decide) hnew hold with
    ⟨o, ⟨_, b, hop⟩, horig⟩ | ⟨j, t, wire, hj, _, hd, _, _⟩
  · have ho : o = rs_child := by
      change FGDependencyOperation.leaf 2 rs_child .accepted = .leaf b o .accepted at hop
      cases hop; rfl
    subst ho
    exact ⟨_, ⟨by decide, b, hop⟩, horig, rfl, rfl, by decide, rfl, by decide, rfl, rfl,
      by decide⟩
  · have hj3 : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j <;> simp at hj

/-! ### (c) One body with two distinct wire histories (generic observation) -/

private noncomputable abbrev tw_w1 : do_protocol.Object := do_wire 2
private noncomputable abbrev tw_w2 : do_protocol.Object := ⟨.none, 2⟩

private noncomputable abbrev tw_run : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false tw_w1 0, .deliver false tw_w2 1] }

private noncomputable abbrev tw_history : FGHistoricalReads Nat (Fin 4) :=
  { do_history with
    acceptedBlocks := fun st => (if 1 ≤ st then [do_body 0, do_body 2] else [do_body 0]).toFinset
    acceptedBodies := fun st => if 1 ≤ st then [0, 2] else [0] }

private noncomputable abbrev tw_t1 : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 0, tw_w1, 0, 0⟩
private noncomputable abbrev tw_t2 : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 1, tw_w2, 1, 0⟩

/-- Body 2 is received twice, by different wires; the step from cut 1 accepts it from the
first receipt only. -/
private noncomputable abbrev twObs : FGExecutionObs Bool do_protocol where
  stateBefore j _ := if 1 ≤ j then 1 else 0
  cutLength _ := 6
  cutState _ k := if 2 ≤ k then 1 else 0
  cutTime _ k := if k < 3 then 0 else 1
  start _ j := 3 * j
  entry _ j := 3 * j + 1
  duty _ j := 3 * j + 1
  done _ j := 3 * j + 2
  released _ _ := []
  finish _ st := st
  accepts _ k o := k = 1 ∧ o = tw_t1
  ownWrites _ _ := []

private theorem tw_origin1 :
    FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t1 := by
  constructor <;> rfl

private theorem tw_origin2 :
    FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t2 := by
  constructor <;> rfl

private theorem tw_body_origin :
    FGAcceptedBodyOrigin do_env tw_run tw_history do_wireReads twObs false where
  origin k b hk hb hnb := by
    change k < 6 at hk
    have key : k = 1 ∧ b = 2 := by
      revert hb hnb; revert b
      interval_cases k <;> decide
    obtain ⟨rfl, rfl⟩ := key
    exact Or.inl ⟨tw_t1, ⟨rfl, rfl⟩, tw_origin1⟩

/-- (c) Both receipts are full receipt origins of the same body by distinct wires; the origin
bridge keeps the one actually accepted (event 0, wire `tw_w1`), not the later one. -/
private theorem two_wire_histories :
    tw_w1 ≠ tw_w2 ∧ FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t1 ∧
      FGReceiptOrigin do_env tw_run tw_history do_wireReads false 2 tw_t2 ∧
      twObs.accepts false 1 tw_t1 ∧ ¬ twObs.accepts false 1 tw_t2 := by
  refine ⟨by decide, tw_origin1, tw_origin2, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨_, h⟩
  have := congrArg FGReceiptToken.eventIndex h
  simp at this

/-! ### The ordinary bridge is one-way (integer time) -/

private def cvRow : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, none⟩
private def cvB : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [cvRow]

private abbrev cvProtocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun st => st
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev cvEnv : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

private noncomputable abbrev cvObj : cvProtocol.Object := ⟨.none, ()⟩

/-- Tick at 1, admission by a delivery at 3, tick at 4. -/
private noncomputable abbrev cvTrace : V2.D.Run Unit cvProtocol where
  honest := {()}
  horizon := 5
  events := [.tick () 1, .deliver () cvObj 3, .tick () 4]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private noncomputable abbrev cvReads : FGCoreReads cvProtocol 1 Unit Unit Unit where
  core st := ⟨(), ⟨if st then {.genesis, cvB} else {.genesis}, .genesis, .genesis, 0, 1⟩,
    [], []⟩
  erase := fun _ => .genesis
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem cv_positive :
    FGChainRowsAtCut cvReads cvTrace (ordinaryFGExecutionObs cvEnv cvTrace) cvB 4 := by
  intro W hW _ _
  have hmem : cvB ∈ (cvReads.core
      ((ordinaryFGExecutionObs cvEnv cvTrace).cutState () 5)).fg.TF := by decide
  have hcl : ∀ B ∈ (cvReads.core
      ((ordinaryFGExecutionObs cvEnv cvTrace).cutState () 5)).fg.TF,
      B.parent ∈ (cvReads.core ((ordinaryFGExecutionObs cvEnv cvTrace).cutState () 5)).fg.TF := by
    decide
  refine ⟨(), Finset.mem_singleton_self _, Or.inr ⟨1, _, 5, rfl, by decide, le_rfl, ?_,
    KitFG.ancestor_closed_of_parent_closed _ hcl cvB hmem W hW⟩⟩
  intro i ei hi hle
  have hi3 : i < 3 := (List.getElem?_eq_some_iff.mp hi).1
  interval_cases i <;> simp at hi <;> subst ei <;> decide

/-- The converse of `ordinary_chainRows_atCut_of_before` fails: with integer time the block
admitted at time 3 has a strict-cut witness before 4 but no strict-time read `t < 4`. -/
private theorem ordinary_converse_fails :
    FGChainRowsAtCut cvReads cvTrace (ordinaryFGExecutionObs cvEnv cvTrace) cvB 4 ∧
      ¬ ChainRowsBefore cvReads cvEnv cvTrace cvB 4 := by
  refine ⟨cv_positive, ?_⟩
  intro h
  obtain ⟨x, t, _, ht, hheld⟩ := h cvB (KitFG.preceq_refl _) cvRow (List.mem_singleton_self _)
  rw [Gen.V2.Duty.HoldsBefore_def] at hheld
  cases x
  have h3 : ¬ ((3 : Time) < t) := fun h =>
    absurd ht (not_lt.mpr (by simpa using Int.add_one_le_of_lt h))
  have h4 : ¬ ((4 : Time) < t) := fun h => absurd ht (not_lt.mpr h.le)
  unfold V2.D.Run.stateBeforeTime at hheld
  by_cases h1 : (1 : Time) < t
  · simp [V2.Event.time, h1, h3, h4] at hheld
    revert hheld
    decide
  · simp [V2.Event.time, h1, h3, h4] at hheld
    revert hheld
    decide

#print axioms do_hacc
#print axioms do_origin
#print axioms child_admitted_by_parent
#print axioms delayed_old_row
#print axioms rs_trace_laws
#print axioms rs_hacc
#print axioms rs_origin
#print axioms child_admitted_in_restart
#print axioms tw_body_origin
#print axioms two_wire_histories
#print axioms cv_positive
#print axioms ordinary_converse_fails

end AvailableChain.FGCompose.Tests.X1b
end
