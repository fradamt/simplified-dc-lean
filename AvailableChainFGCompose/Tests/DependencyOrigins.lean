module
public import AvailableChainFGCompose.Proofs.Dependency
public import Mathlib.Tactic.IntervalCases

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.DependencyOrigins

/-- A finite interface model. This is not an ExecutionValid protocol fixture. -/
private noncomputable abbrev do_protocol : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Fin 4
  Durable := Nat
  init := 0
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro _; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process st wire := if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 6 else st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed wire := decide (wire.payload ≠ 3)
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable abbrev do_leafProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
    if st = 2 ∧ wire.payload = 1 then 3
    else if st = 3 ∧ wire.payload = 2 then 4 else st }

private noncomputable abbrev do_env : Generic.Env Bool where
  Δ := 3
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

private noncomputable abbrev do_wire (b : Fin 4) : do_protocol.Object := ⟨.seat () 0, b⟩

private noncomputable abbrev do_run : V2.D.Run Bool do_protocol where
  honest := {false}
  horizon := 10
  events := [.deliver false (do_wire 2) 0, .restart false 1,
    .deliver false (do_wire 1) 1, .tick false 4]
  seatOf := fun _ _ => false
  input := fun _ _ => ()

private noncomputable abbrev do_body (b : Fin 4) : Block :=
  if b = 0 then .genesis else if b = 1 then .node .genesis 1 ⟨1⟩ 0
  else .node (.node .genesis 1 ⟨1⟩ 0) 2 ⟨2⟩ 0

private noncomputable abbrev do_history : FGHistoricalReads Nat (Fin 4) where
  acceptedBlocks st := (if 4 ≤ st then [do_body 0, do_body 1, do_body 2]
    else if 3 ≤ st then [do_body 0, do_body 1] else [do_body 0]).toFinset
  acceptedBodies st := if 4 ≤ st then [0, 1, 2] else if 3 ≤ st then [0, 1] else [0]
  erase := do_body
  root b := (do_body b).root
  parent b := if b = 2 ∨ b = 3 then 1 else 0
  slot b := (do_body b).slot
  readBlock _ _ := none
  preceq b c := Block.Preceq (do_body b) (do_body c)
  depth b := (do_body b).depth
  lca b c := Block.meet (do_body b) (do_body c)

private noncomputable abbrev do_wireReads : FGDependencyWireReads do_protocol (Fin 4) Nat where
  decodeBody wire := some wire.payload
  namedRoots wire := some (do_history.root wire.payload,
    do_history.root (do_history.parent wire.payload))
  proposalErase wire := some (do_body wire.payload)
  decodedRows wire := [wire.payload.val]
  bodyRows b := [b.val]

private noncomputable abbrev do_child : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 0, do_wire 2, 0, 0⟩
private noncomputable abbrev do_parent : FGReceiptToken Bool do_protocol.Object :=
  ⟨false, 2, do_wire 1, 1, 2⟩

private noncomputable abbrev do_reads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat where
  accepted st b := b = 0 ∨ (b = 1 ∧ 3 ≤ st) ∨ (b = 2 ∧ 4 ≤ st)
  refused _ _ _ _ := False
  pending st b o := (b = 2 ∧ 1 ≤ st ∧ st < 4 ∧ o = do_child) ∨
    (b = 1 ∧ st = 2 ∧ o = do_parent)
  originAvailable st b o := (b = 2 ∧ 1 ≤ st ∧ o = do_child) ∨
    (b = 1 ∧ 2 ≤ st ∧ o = do_parent)
  validBody b := b ≠ 3
  priorChecks st b := (b = 1 ∧ st = 2) ∨ (b = 2 ∧ st = 3)
  timely _ _ := True
  conflictsFinal _ _ := False
  latest := id
  notified st b := b = 0 ∨ (b = 1 ∧ 5 ≤ st) ∨ (b = 2 ∧ 6 ≤ st)
  matching _ b := b = 2
  companionHeld st b := b = 2 ∧ 6 ≤ st
  latestKey _ _ := some (2, do_history.root 2)
  latestCompanion st _ := if 6 ≤ st then some 2 else none

private noncomputable abbrev do_leaf : FGDependencyLeaf Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) where
  step a b o outcome z := outcome = .accepted ∧
    ((a = 2 ∧ b = 1 ∧ o = do_parent ∧ z = 3) ∨
     (a = 3 ∧ b = 2 ∧ o = do_child ∧ z = 4))
  callback a b o z := (a = 2 ∧ b = 1 ∧ o = do_parent ∧ z = 3) ∨
    (a = 3 ∧ b = 2 ∧ o = do_child ∧ z = 4)
  report _ _ _ _ := False
  initial := 0
  genesis := 0

private noncomputable abbrev do_step (kind : FGDependencyStepKind) (_ : Bool) (a z : Nat) : Prop :=
  a = z ∨ (kind = .arrival ∧ ((a = 0 ∧ z = 1) ∨ (a = 1 ∧ z = 2))) ∨
    (kind = .leafRetry ∧ ((a = 2 ∧ z = 3) ∨ (a = 3 ∧ z = 4))) ∨
    (kind = .notification ∧ ((a = 4 ∧ z = 5) ∨ (a = 5 ∧ z = 6)))

private noncomputable abbrev do_driver : FGDependencyDriver Bool (Fin 4) do_protocol where
  enter st wire _ := if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st
  enterProgram st wire _ := .finish (if st = 0 ∧ wire.payload = 2 then 1
    else if st = 1 ∧ wire.payload = 1 then 2 else st)
  hookProgram st op := match op with
    | .leaf b _ _ => .finish (do_leafProtocol.process st (do_wire b))
    | .notification b _ =>
        let z := if st = 4 ∧ b = 1 then 5 else if st = 5 ∧ b = 2 then 6 else st
        if st = 5 ∧ b = 2 then .read .ac z .finish else .finish z
    | _ => .finish st
  drain st := if 2 ≤ st ∧ st ≤ 5 then 6 else st
  retry st b _ _ := do_leafProtocol.process st (do_wire b)
  work st e := if st = 2 then
    [.step (.leaf 1 do_parent .accepted), .step (.leaf 2 do_child .accepted),
      .step (.notification 1 do_parent), .step (.notification 2 do_child)]
    else match e with
      | .deliver _ _ _ => if st = 1 then [.step .idle] else []
      | _ => []
  inheritRefusal st _ _ := st
  notify st b _ := if st = 4 ∧ b = 1 then 5 else if st = 5 ∧ b = 2 then 6 else st

private noncomputable abbrev do_op (k : Nat) :
    FGDependencyOperation (Fin 4) (FGReceiptToken Bool do_protocol.Object) do_protocol.Object :=
  match k with
  | 0 => .arrival 2 do_child
  | 3 => .restore 1
  | 5 => .arrival 1 do_parent
  | 6 => .leaf 1 do_parent .accepted
  | 7 => .leaf 2 do_child .accepted
  | 8 => .notification 1 do_parent
  | 9 => .notification 2 do_child
  | 11 => .clock 4
  | _ => .idle

private noncomputable abbrev do_trace : FGDependencyTrace Nat where
  length := 12
  state k := [0, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 6, 6][k]?.getD 6
  time k := [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4][k]?.getD 4
  start j := [0, 3, 5, 11][j]?.getD 12
  done j := [2, 4, 10, 12][j]?.getD 12
  readCut _ := 12
  entryCut j := [1, 4, 6, 12][j]?.getD 12
  dutyCut j := [2, 4, 10, 12][j]?.getD 12
  hookRead j index kind cut st := j = 2 ∧ index = 0 ∧ kind = .ac ∧ cut = 10 ∧ st = 6

private noncomputable abbrev do_read (_ : Bool) (i st : Nat) : Prop :=
  12 ≤ i ∧ i < 16 ∧ st = 6

private theorem do_child_origin :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child := by
  constructor <;> rfl

private theorem do_parent_origin :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 1 do_parent := by
  constructor <;> rfl

private theorem do_closed (st : Nat) (h : st = 1 ∨ st = 6) :
    dependencyClosed do_history do_reads st := by
  intro work
  cases work with
  | inherit b o pending refused unresolved => exact refused.elim
  | retry b o pending valid prior timely held unresolved =>
    rcases h with rfl | rfl <;> simp_all
  | notify b resolved missing =>
    rcases h with rfl | rfl <;> simp_all [dependencyResolved, dependencyRefused]
  | companion b accepted matching missing =>
    rcases h with rfl | rfl <;> simp_all

private theorem do_events_bound {j : Nat} {e : V2.Event Bool do_protocol.Object}
    (h : do_run.events[j]? = some e) : j < 4 :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem do_step_laws :
    FGDependencyStepLaws do_history do_reads do_leaf do_step (fun s _ => s)
      (fun _ _ => False) where
  accepted_keep k x a z b step held := by
    have le : a ≤ z := by rcases step with h | h | h | h <;> omega
    rcases held with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, Nat.le_trans h le⟩)
    · exact Or.inr (Or.inr ⟨rfl, Nat.le_trans h le⟩)
  refused_keep _ _ _ _ _ _ _ _ h := h.elim
  pending_effect k x a z b o step pending := by
    have le : a ≤ z := by rcases step with h | h | h | h <;> omega
    rcases pending with ⟨rfl, ha, hb, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨Or.inl ⟨rfl, by omega, rfl⟩, ?_⟩
      by_cases hz : z < 4
      · exact Or.inl (Or.inl ⟨rfl, by omega, hz, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨rfl, by omega⟩)))
    · refine ⟨Or.inr ⟨rfl, le, rfl⟩, ?_⟩
      by_cases hz : z = 2
      · exact Or.inl (Or.inr ⟨rfl, hz, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  origin_keep k x a z b o step origin := by
    have le : a ≤ z := by rcases step with h | h | h | h <;> omega
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · exact Or.inl ⟨rfl, Nat.le_trans h le, rfl⟩
    · exact Or.inr ⟨rfl, Nat.le_trans h le, rfl⟩
  metadata_fg_eq k x a z step notArrival notLeaf := by
    rcases step with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · rfl
    · exact (notArrival rfl).elim
    · exact (notLeaf rfl).elim
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  insertion_leaf k x a z b step held fresh := by
    rcases step with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact (fresh held).elim
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hb : b = 1 := by simp_all
        subst b
        exact ⟨do_parent, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
      · have hb : b = 2 := by simp_all
        subst b
        exact ⟨do_child, rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  one_body a z b o result leaf c held := by
    rcases leaf with ⟨rfl, (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)⟩
    all_goals simp_all
    all_goals tauto
  restore_exact _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  no_signing _ _ _ _ _ := not_false

private theorem do_state_laws : FGDependencyStateLaws do_history do_reads do_leaf where
  accepted_domain st b := by
    by_cases h4 : 4 ≤ st
    · have h3 : 3 ≤ st := by omega
      simp [h4, h3]
    · by_cases h3 : 3 ≤ st <;> simp [h4, h3]
  accepted_refused_disjoint _ _ _ _ h := h.elim
  pending_valid st b o h := by
    rcases h with ⟨rfl, lo, _, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨by decide, Or.inl ⟨rfl, lo, rfl⟩⟩
    · exact ⟨by decide, Or.inr ⟨rfl, Nat.le_refl _, rfl⟩⟩
  refused_valid _ _ _ _ h := h.elim
  genesis_accepted := Or.inl rfl
  initial_pending b o h := by simp at h
  initial_refused _ _ _ := not_false
  accepted_leaf st b held nonGenesis := by
    rcases held with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact (nonGenesis rfl).elim
    · exact ⟨2, 3, do_parent, ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩,
        by decide, Or.inr (Or.inl ⟨rfl, by decide⟩),
        Or.inr ⟨rfl, by omega, rfl⟩⟩
    · exact ⟨3, 4, do_child, ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩,
        by decide, Or.inr (Or.inr ⟨rfl, by decide⟩),
        Or.inl ⟨rfl, by omega, rfl⟩⟩

private noncomputable abbrev do_arrival (a : Nat) (b : Fin 4)
    (o : FGReceiptToken Bool do_protocol.Object) (z : Nat) : Prop :=
  (a = 0 ∧ b = 2 ∧ o = do_child ∧ z = 1) ∨
    (a = 1 ∧ b = 1 ∧ o = do_parent ∧ z = 2)

private noncomputable abbrev do_notify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  (a = 4 ∧ b = 1 ∧ z = 5) ∨ (a = 5 ∧ b = 2 ∧ z = 6)

private theorem do_arrival_laws :
    FGDependencyArrivalLeafLaws do_history do_reads do_leaf do_arrival do_notify where
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

private theorem do_micro_steps (k : Nat) (hk : k < do_trace.length) :
    ∃ kind, do_step kind false (do_trace.state k) (do_trace.state (k + 1)) := by
  change k < 12 at hk
  interval_cases k <;> first
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.arrival, Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.leafRetry, Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.notification, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))⟩
    | exact ⟨.ordinary, Or.inl rfl⟩

private theorem do_entry_steps (x : Bool) : FGDependencySteps do_step x 2 6 := by
  have s1 : do_step .leafRetry x 2 3 := by simp [do_step]
  have s2 : do_step .leafRetry x 3 4 := by simp [do_step]
  have s3 : do_step .notification x 4 5 := by simp [do_step]
  have s4 : do_step .notification x 5 6 := by simp [do_step]
  exact .tail .notification (.tail .notification
    (.tail .leafRetry (.tail .leafRetry (.refl 2) s1) s2) s3) s4

private theorem do_trace_laws :
    FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_trace do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read where
  arrival_laws := do_arrival_laws
  initial := rfl
  initial_accepted b h := by simpa [do_reads, do_protocol, do_leaf] using h
  micro_step := do_micro_steps
  external_step j e h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  step_kind k hk := by
    change k < 12 at hk
    interval_cases k <;> simp [dependencyOperationKind, do_op, do_step]
  operation_bound k hk := by
    change k < 12 at hk
    interval_cases k <;> simp only [do_op]
    all_goals first
      | exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, do_child_origin, rfl⟩
      | exact ⟨Or.inr ⟨rfl, rfl, rfl, rfl⟩, rfl, do_parent_origin, rfl⟩
      | simp [dependencyResolved, dependencyRefused, do_notify]
  delivery_entry j wire t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  work_execution j e h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact ⟨rfl, rfl⟩
  work_step j e k h lo hi := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [do_trace] at lo hi <;> interval_cases k <;> rfl
  hook_correspondence j e index kind cut st h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    · change (0 = 2 ∧ _) ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change (1 = 2 ∧ _) ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
    · change (2 = 2 ∧ index = 0 ∧ kind = .ac ∧ cut = 10 ∧ st = 6) ↔
        ∃ r, ([⟨4, .ac, 6⟩] : List (FGDependencyWorkRead Nat))[index]? = some r ∧
          r.kind = kind ∧ cut = 6 + r.offset ∧ st = r.consumed
      cases index <;> simp [eq_comm]
    · change (3 = 2 ∧ _) ↔ ∃ r, ([] : List (FGDependencyWorkRead Nat))[index]? = some r ∧ _
      simp
  hook_reads j e r h member := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
    · change r ∈ ([⟨4, .ac, 6⟩] : List (FGDependencyWorkRead Nat)) at member
      have hr := List.mem_singleton.mp member
      subst r
      exact ⟨by decide, rfl, do_entry_steps false, do_closed 6 (Or.inr rfl)⟩
    · change r ∈ ([] : List (FGDependencyWorkRead Nat)) at member
      cases member
  receipt_entry j wire t b h awake valid decoded := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        do_op, do_arrival]
    · cases h
    · obtain ⟨_, rfl, rfl⟩ := V2.Event.deliver.inj h
      have hb := Option.some.inj decoded
      subst b
      simp [Effect, dependencyResolved, dependencyRefused, dependencyReceiverEpoch,
        do_op, do_arrival]
    · cases h
  entry_boundary j e h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      exact ⟨rfl, by decide, by decide, rfl, rfl⟩
  drain_operations j e k h lo hi := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [do_trace] at lo hi <;> interval_cases k <;> simp [do_op]
  boundary_idle k hk outside := by
    change k < 12 at hk
    interval_cases k <;> simp only [do_op]
    all_goals exfalso; apply outside
    all_goals first
      | exact ⟨0, _, rfl, by decide, by decide⟩
      | exact ⟨1, _, rfl, by decide, by decide⟩
      | exact ⟨2, _, rfl, by decide, by decide⟩
      | exact ⟨3, _, rfl, by decide, by decide⟩
  raw_restore j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  raw_clock j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  restore_data _ _ := ⟨rfl, rfl, fun _ _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  clock_no_insert _ _ := ⟨rfl, rfl⟩
  refusal_creation _ _ _ refused _ := refused.elim
  refusal_history _ _ _ refused := refused.elim
  notification_creation k b hk notified fresh := by
    change k < 12 at hk
    interval_cases k <;> simp_all
    all_goals rcases notified with rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩, 6, by decide, by simp [do_op]⟩
    · exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩, 7, by decide, by simp [do_op]⟩
  actual_read i st := by
    constructor
    · rintro ⟨lo, hi, rfl⟩
      interval_cases i
      · exact ⟨3, .tick false 4, .fg, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .proposer, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .head, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨3, .tick false 4, .ac, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨j, e, kind, he, required, rfl, rfl⟩
      have hj := do_events_bound he
      interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at he <;> subst e
      all_goals simp [dependencyReadRequired] at required
      all_goals cases kind <;> exact ⟨by decide, by decide, rfl⟩
  read_order j e kind h required := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e
    all_goals simp [dependencyReadRequired] at required
    all_goals exact ⟨Nat.le_refl 12, Nat.le_refl 12, rfl, .refl _⟩
  wire_validation wire b valid decoded := by
    have hb : wire.payload = b := Option.some.inj decoded
    simpa [do_protocol, do_reads, hb] using valid
  origin_valid k b o hk origin := by
    change k ≤ 12 at hk
    rcases origin with ⟨rfl, h, rfl⟩ | ⟨rfl, h, rfl⟩
    · refine ⟨do_child_origin, ?_⟩
      interval_cases k <;> simp_all
    · refine ⟨do_parent_origin, ?_⟩
      interval_cases k <;> simp_all
  leaf_step k b o z hk leaf hz := by
    change k < 12 at hk
    rcases leaf with ⟨_, (⟨ha, rfl, rfl, rfl⟩ | ⟨ha, rfl, rfl, rfl⟩)⟩
    · refine ⟨do_parent_origin, ?_, ?_⟩
      · clear hz
        interval_cases k <;> simp_all
      · change 3 = do_leafProtocol.process (do_trace.state k) (do_wire 1)
        rw [ha]
        rfl
    · refine ⟨do_child_origin, ?_, ?_⟩
      · clear hz
        interval_cases k <;> simp_all
      · change 4 = do_leafProtocol.process (do_trace.state k) (do_wire 2)
        rw [ha]
        rfl
  origin_attribution k b hk held fresh := by
    obtain ⟨kind, step⟩ := do_micro_steps k hk
    obtain ⟨o, leaf⟩ := do_step_laws.insertion_leaf kind false _ _ b step held fresh
    rcases leaf with ⟨_, (⟨ha, rfl, rfl, hz⟩ | ⟨ha, rfl, rfl, hz⟩)⟩
    · exact ⟨do_parent, ⟨rfl, Or.inl ⟨ha, rfl, rfl, hz⟩⟩,
        Or.inr ⟨rfl, by omega, rfl⟩, by
          change k < 12 at hk
          interval_cases k <;> simp_all [do_op], rfl, rfl⟩
    · exact ⟨do_child, ⟨rfl, Or.inr ⟨ha, rfl, rfl, hz⟩⟩,
        Or.inl ⟨rfl, by omega, rfl⟩, by
          change k < 12 at hk
          interval_cases k <;> simp_all [do_op], rfl, rfl⟩
  read_correspondence i st read := by
    rcases read with ⟨_, _, rfl⟩
    exact ⟨Nat.le_refl 12, rfl, do_closed 6 (Or.inr rfl)⟩
  order_and_time i j ei ej hi hj le := by
    have bi := do_events_bound hi
    have bj := do_events_bound hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hi hj <;> subst ei <;> subst ej <;>
      decide +kernel
  finite_segment j e h := by
    have hj := do_events_bound h
    interval_cases j <;> decide +kernel
  event_drain j y wire t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq, V2.Event.deliver.injEq] at h
    · exact do_closed 1 (Or.inl rfl)
    · cases h
    · exact do_closed 6 (Or.inr rfl)
    · cases h
  entry_drain j e h := by
    have hj := do_events_bound h
    interval_cases j
    · exact do_closed 1 (Or.inl rfl)
    · exact do_closed 1 (Or.inl rfl)
    · exact do_closed 6 (Or.inr rfl)
    · exact do_closed 6 (Or.inr rfl)
  segment_time j e k h lower upper := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;>
      norm_num [do_trace] at lower upper <;> interval_cases k <;> rfl
  event_order i j ei ej hi hj lt := by
    have bi := do_events_bound hi
    have bj := do_events_bound hj
    interval_cases i <;> interval_cases j <;> simp_all
  completion_cut j e deadline h strict := by
    have hj := do_events_bound h
    refine ⟨?_, ?_, ?_⟩
    · interval_cases j <;> decide +kernel
    · interval_cases j <;> simp only [List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.some.injEq] at h <;> subst e <;> exact strict
    · intro i ei hi before
      have bi := do_events_bound hi
      interval_cases i <;> interval_cases j <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi h <;> subst ei <;> subst e <;>
        norm_num [do_trace] at before <;>
        exact lt_of_le_of_lt (by decide) strict
  tick_records j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    all_goals cases h <;> rfl
  atomic_tick j t h := by
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · cases h
    · cases h
    · cases h
    · have ht : (4 : Time) = t := V2.Event.tick.inj h |>.2
      subst t
      exact ⟨by decide, by decide, rfl, do_closed 6 (Or.inr rfl), .refl _⟩

private theorem do_same_time_positive :
    do_trace.time 7 = 1 ∧ do_trace.time 8 = 1 ∧ do_trace.time 9 = 1 ∧
    do_trace.time 10 = 1 ∧ do_trace.done 2 = 10 ∧
    dependencyResolved do_history do_reads (do_trace.state 10) 2 ∧
    do_reads.notified (do_trace.state 10) 2 ∧
    do_reads.companionHeld (do_reads.latest (do_trace.state 10)) 2 := by
  unfold dependencyResolved dependencyRefused
  decide +kernel

private theorem do_original_epoch_after_restart :
    dependencyReceiverEpoch do_run false 2 = 2 ∧ do_child.receiptEpoch = 0 ∧
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child :=
  ⟨rfl, rfl, do_child_origin⟩

private theorem do_wrong_receiver :
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads true 2 do_child := by
  intro h
  cases h.receiver_eq

private theorem do_same_root_forgery :
    do_history.root 2 = do_history.root 3 ∧
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads false 3 do_child := by
  refine ⟨rfl, ?_⟩
  intro h
  have bad : (2 : Fin 4) = 3 := Option.some.inj h.decoded
  exact (by decide : (2 : Fin 4) ≠ 3) bad

private theorem do_epoch_forgery :
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads false 2
      { do_child with receiptEpoch := 2 } := by
  intro h
  have bad : (2 : Nat) = 0 := h.epoch_eq
  omega

private theorem do_future_forgery :
    ¬ FGReceiptOrigin do_env do_run do_history do_wireReads false 2
      { do_child with eventIndex := 20 } := by
  intro h
  have bad : (none : Option (V2.Event Bool do_protocol.Object)) = some _ := h.delivered
  cases bad

private theorem do_delayed_drain_enabled :
    FGDependencyEnabled do_history do_reads 3 := by
  exact .retry 2 do_child (Or.inl ⟨rfl, by decide, by decide, rfl⟩)
    (by decide) (Or.inr ⟨rfl, rfl⟩) trivial (Or.inr (Or.inl ⟨rfl, by decide⟩))
    (by simp [dependencyResolved, dependencyRefused])

private theorem do_delayed_notification_enabled :
    FGDependencyEnabled do_history do_reads 4 := by
  exact .notify 2 (Or.inl (Or.inr (Or.inr ⟨rfl, by decide⟩)))
    (by simp)

private theorem do_later_read_closed_but_late :
    dependencyClosed do_history do_reads (do_trace.state 12) ∧
    ¬ do_trace.time 12 < (3 : Time) :=
  ⟨do_closed 6 (Or.inr rfl), by decide⟩

private theorem do_retained_only_entry :
    dependencyClosed do_history do_reads (do_trace.state (do_trace.done 1)) ∧
    do_trace.time (do_trace.done 1) = 1 ∧
    Effect do_history do_reads (do_trace.state (do_trace.done 1)) 2 do_child :=
  ⟨do_closed 1 (Or.inl rfl), rfl,
    Or.inl ⟨rfl, by decide, rfl⟩, Or.inl (Or.inl ⟨rfl, by decide, by decide, rfl⟩)⟩

private theorem do_terminal_equality_not_strict : ¬ (3 : Time) < 3 := by decide

/-- Only logical time changes in these weak models. Retention and origin data stay exact. -/
private noncomputable abbrev do_delayed (firstLate : Nat) : FGDependencyTrace Nat :=
  { do_trace with time := fun k => if firstLate ≤ k then 4 else do_trace.time k }

private theorem do_weak_delayed_model (firstLate : Nat) :
    (∀ k, k < (do_delayed firstLate).length → ∃ kind,
      do_step kind false ((do_delayed firstLate).state k)
        ((do_delayed firstLate).state (k + 1))) ∧
    (∀ k b o, k ≤ (do_delayed firstLate).length →
      do_reads.originAvailable ((do_delayed firstLate).state k) b o →
      FGReceiptOrigin do_env do_run do_history do_wireReads false b o) ∧
    (∀ i st, do_read false i st →
      (do_delayed firstLate).state ((do_delayed firstLate).readCut i) = st ∧
      dependencyClosed do_history do_reads st) := by
  refine ⟨do_micro_steps, ?_, ?_⟩
  · intro k b o bound origin
    exact (do_trace_laws.origin_valid k b o bound origin).1
  · intro i st read
    exact (do_trace_laws.read_correspondence i st read).2

private theorem do_delayed_child_countermodel :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step (do_delayed 8) do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have cutoff := laws.completion_cut 2 (.deliver false (do_wire 1) 1) 3 rfl (by decide)
  exact (by decide : ¬ (4 : Time) < 3) cutoff.2.1

private theorem do_delayed_notification_countermodel :
    do_trace.time 8 = 1 ∧
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step (do_delayed 9) do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, ?_⟩
  intro laws
  have cutoff := laws.completion_cut 2 (.deliver false (do_wire 1) 1) 3 rfl (by decide)
  exact (by decide : ¬ (4 : Time) < 3) cutoff.2.1

private theorem do_early_read_countermodel :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step { do_trace with readCut := fun _ => 7 }
      do_driver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have eq := (laws.read_correspondence 15 6 ⟨by decide, by decide, rfl⟩).2.1
  exact (by decide : (3 : Nat) ≠ 6) eq

private theorem do_future_in_range_receipt :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 1 do_parent ∧
    ¬ do_trace.start do_parent.eventIndex < 2 :=
  ⟨do_parent_origin, by decide⟩

private theorem do_positive_strict_no_early_read :
    dependencyStrictPrefix do_run do_trace 3 (do_trace.done 2) ∧
    (∀ i st, do_read false i st → ¬ do_trace.time (do_trace.readCut i) < 3) ∧
    do_trace.done 1 < do_trace.start 2 ∧
    do_trace.time (do_trace.done 1) = do_trace.time (do_trace.start 2) := by
  exact ⟨(dependency_drain_before_deadline do_trace_laws
    (j := 2) (wire := do_wire 1) (t := 1) (deadline := 3) rfl (by decide)).2.2,
    fun _ _ _ => (by decide : ¬ (4 : Time) < 3), by decide, rfl⟩

private theorem do_retained_only_path_consumer :
    ∃ j k, k = do_trace.done j ∧ 3 ≤ j ∧ dependencyStrictPrefix do_run do_trace 7 k ∧
      dependencyResolved do_history do_reads (do_trace.state k) 2 ∧
      do_reads.notified (do_trace.state k) 2 ∧
      (do_reads.accepted (do_trace.state k) 2 →
        do_reads.matching (do_reads.latest (do_trace.state k)) 2 →
        do_reads.companionHeld (do_reads.latest (do_trace.state k)) 2) := by
  have delivery : FGDependencyDeliveryLaws do_env do_run false do_history do_wireReads
      do_reads do_trace do_driver (fun _ _ _ => False) :=
    ⟨fun _ _ _ _ _ _ _ _ _ _ out => out.elim⟩
  apply dependency_finite_path_resolved_before do_trace_laws do_step_laws delivery
    (path := [1, 2]) (entry := 3) (tau := 4) (wake := 4)
    (event := .tick false 4)
  · exact .snoc (parent := 1) (b := 2) (path := [1])
      (.snoc (parent := 0) (b := 1) (path := []) .root rfl) rfl
  · rfl
  · rfl
  · exact Or.inl rfl
  · decide
  · exact le_rfl
  · intro t _ _; rfl
  · intro j t h after
    have hj := do_events_bound h
    interval_cases j <;> simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at h
    · cases h
    · have ht := (V2.Event.restart.inj h).2
      subst t
      exact (by decide : ¬ (4 : Time) < 1) after |>.elim
    · cases h
    · cases h
  · decide
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · refine ⟨by decide, ?_⟩
      intro k _ o pending _
      rcases pending with ⟨bad, _⟩ | ⟨_, eq, _⟩
      · cases bad
      · exact ⟨Or.inl ⟨rfl, eq⟩, trivial⟩
    · have hb' : b = 2 := by simpa using hb
      subst b
      refine ⟨by decide, ?_⟩
      intro k _ o pending parent
      rcases pending with ⟨_, lo, hi, _⟩ | ⟨bad, _⟩
      · have parentHeld : 3 ≤ do_trace.state k := by simpa using parent
        exact ⟨Or.inr ⟨rfl, by omega⟩, trivial⟩
      · cases bad
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl ⟨do_parent, Or.inr ⟨rfl, by decide, rfl⟩,
        Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, by decide⟩)))⟩
    · have hb' : b = 2 := by simpa using hb
      subst b
      exact Or.inl ⟨do_child, Or.inl ⟨rfl, by decide, rfl⟩,
        Or.inr (Or.inl (Or.inr (Or.inr ⟨rfl, by decide⟩)))⟩

private noncomputable def do_site (i : Nat) : FGDependencyReadSite Nat :=
  ⟨i / 4, match i % 4 with
    | 0 => .fg | 1 => .proposer | 2 => .head | _ => .ac,
    do_trace.entryCut (i / 4), do_trace.readCut i, 6⟩

private theorem do_read_closure_laws :
    FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      do_trace do_driver do_site do_read do_wireReads do_leaf do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id where
  trace_bound := do_trace_laws
  actual_read := do_trace_laws.actual_read
  site_correspondence i st h := by
    rcases h with ⟨lo, hi, rfl⟩
    interval_cases i <;> exact ⟨.tick false 4, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  hook_correspondence := do_trace_laws.hook_correspondence
  hook_completion := do_trace_laws.hook_reads
  read_closed i st h := (do_trace_laws.read_correspondence i st h).2.2
  finite_completion i st h := by
    rcases h with ⟨lo, hi, rfl⟩
    interval_cases i <;>
      exact ⟨by decide, by decide, rfl, rfl, .refl _, do_closed 6 (Or.inr rfl)⟩

private theorem do_bridge_original_child_rows : ∃ o,
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 o ∧
    do_wireReads.proposalErase o.wire = some (do_body 2) ∧
    do_wireReads.decodedRows o.wire = [2] := by
  exact dependency_accepted_origin_bridge do_trace_laws (i := 15) (st := 6)
    ⟨by decide, by decide, rfl⟩ (Or.inr (Or.inr ⟨rfl, by decide⟩)) (by decide)

private noncomputable abbrev do_sending (body : Fin 4) : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Unit
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Fin 4
  Durable := Nat
  init := 0
  clock := fun st _ => st
  actTime := fun _ => -1
  duties t := if t = -1 then [()] else []
  duties_spec := by intro d t; cases d; simp [eq_comm]
  duties_nodup := by intro t; split <;> simp
  act := fun _ _ _ => some body
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed wire := decide (wire.payload ≠ 3)
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable abbrev do_sendReads (body : Fin 4) :
    FGDependencyWireReads (do_sending body) (Fin 4) Nat where
  decodeBody wire := some wire.payload
  namedRoots wire := some (do_history.root wire.payload,
    do_history.root (do_history.parent wire.payload))
  proposalErase wire := some (do_body wire.payload)
  decodedRows wire := [wire.payload.val]
  bodyRows b := [b.val]

private noncomputable abbrev do_sentRun (body : Fin 4) (horizon : Time) :
    V2.D.Run Bool (do_sending body) where
  honest := {true}
  horizon := horizon
  events := [.tick true (-1)]
  seatOf := fun _ _ => true
  input := fun _ _ => ()

private noncomputable abbrev do_asleep : Generic.Env Bool :=
  { do_env with awake := fun x _ => x }

private noncomputable abbrev do_emptyTrace : FGDependencyTrace Nat where
  length := 1
  state _ := 0
  time _ := -1
  start _ := 0
  done _ := 1
  readCut _ := 1
  entryCut _ := 1
  dutyCut _ := 1
  hookRead _ _ _ _ _ := False

private noncomputable abbrev do_sendDriver (body : Fin 4) :
    FGDependencyDriver Bool (Fin 4) (do_sending body) where
  enter st _ _ := st
  enterProgram st _ _ := .finish st
  hookProgram st _ := .finish st
  drain := id
  retry st _ _ _ := st
  work _ _ := []
  inheritRefusal st _ _ := st
  notify st _ _ := st

private theorem do_honest_old_send (body : Fin 4) (horizon : Time) :
    dependencyEmits do_asleep (do_sentRun body horizon) (do_sendDriver body)
      true (do_wire body) (-1) ∧
    dependencyEmits do_env (do_sentRun body horizon) (do_sendDriver body)
      true (do_wire body) (-1) := by
  constructor <;> refine ⟨0, rfl, ?_⟩ <;>
    change do_wire body ∈ [do_wire body] <;> exact List.mem_singleton_self _

/-- Without the awake interval, actual old honest sends can have no receiver delivery. -/
private theorem do_awake_guard_countermodel :
    FGDependencyDeliveryLaws do_asleep (do_sentRun 1 10) false do_history (do_sendReads 1)
      do_reads do_emptyTrace (do_sendDriver 1) (fun _ _ _ => True) ∧
    dependencyEmits do_asleep (do_sentRun 1 10) (do_sendDriver 1) true (do_wire 1) (-1) ∧
    ¬ dependencyResolved do_history do_reads (do_emptyTrace.state 1) 1 := by
  refine ⟨⟨?_⟩, (do_honest_old_send 1 10).1, ?_⟩
  · intro sender wire sent wake deadline b honest emit decode valid outstanding
      sentlt wakelt awake noRestart horizon bound
    have impossible : false = true := awake wake le_rfl wakelt
    cases impossible
  · simp [dependencyResolved, dependencyRefused]

/-- The horizon guard is independent of sleeping: this receiver is always awake. -/
private theorem do_horizon_guard_countermodel :
    FGDependencyDeliveryLaws do_env (do_sentRun 1 0) false do_history (do_sendReads 1)
      do_reads do_emptyTrace (do_sendDriver 1) (fun _ _ _ => True) ∧
    dependencyEmits do_env (do_sentRun 1 0) (do_sendDriver 1) true (do_wire 1) (-1) ∧
    ¬ dependencyResolved do_history do_reads (do_emptyTrace.state 1) 1 := by
  refine ⟨⟨?_⟩, (do_honest_old_send 1 0).2, ?_⟩
  · intro sender wire sent wake deadline b honest emit decode valid outstanding
      sentlt wakelt awake noRestart horizon bound
    change deadline ≤ (0 : Time) at horizon
    change max (max sent (0 : Time)) wake + 3 ≤ deadline at bound
    have nonneg : (0 : Time) ≤ max (max sent 0) wake :=
      le_trans (le_max_right sent 0) (le_max_left _ wake)
    have floor : (3 : Time) ≤ max (max sent 0) wake + 3 :=
      Int.add_le_add nonneg (Int.le_refl 3)
    exact ((by decide : ¬ (3 : Time) ≤ 0)
      (le_trans (le_trans floor bound) horizon)).elim
  · simp [dependencyResolved, dependencyRefused]

private theorem do_validation_guard_countermodel :
    FGDependencyDeliveryLaws do_env (do_sentRun 3 10) false do_history (do_sendReads 3)
      do_reads do_emptyTrace (do_sendDriver 3) (fun wire _ _ => wire.payload = 3) ∧
    dependencyEmits do_env (do_sentRun 3 10) (do_sendDriver 3) true (do_wire 3) (-1) ∧
    ¬ dependencyResolved do_history do_reads (do_emptyTrace.state 1) 3 := by
  refine ⟨⟨?_⟩, (do_honest_old_send 3 10).2, ?_⟩
  · intro sender wire sent wake deadline b honest emit decode valid outstanding
    have hb : wire.payload = b := Option.some.inj decode
    exact (valid (hb.symm.trans outstanding)).elim
  · simp [dependencyResolved, dependencyRefused]

private theorem do_retained_outcome_countermodel :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    ¬ Effect do_history do_reads 0 2 do_child ∧
    ¬ dependencyResolved do_history do_reads 0 2 := by
  exact ⟨do_child_origin, by simp [Effect, dependencyResolved, dependencyRefused],
    by simp [dependencyResolved, dependencyRefused]⟩

/-- The first valid receipt cannot disappear before pending retention has a premise. -/
private noncomputable abbrev do_lostTrace : FGDependencyTrace Nat :=
  { do_trace with state := fun k => if k ≤ 2 then 0 else do_trace.state k }

private noncomputable abbrev do_lostDriver : FGDependencyDriver Bool (Fin 4) do_protocol :=
  { do_driver with enter := fun st wire o =>
      if wire.payload = 2 then st else do_driver.enter st wire o }

private def do_silentArrival (a : Nat) (b : Fin 4)
    (o : FGReceiptToken Bool do_protocol.Object) (z : Nat) : Prop :=
  do_arrival a b o z ∨ (a = 0 ∧ b = 2 ∧ o = do_child ∧ z = 0)

private theorem do_silent_first_receipt_rejected :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_lostTrace do_lostDriver do_op do_silentArrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨do_child_origin, ?_⟩
  intro laws
  have effect := (laws.receipt_entry 0 (do_wire 2) 0 2 rfl rfl rfl rfl).2.2 trivial
  have absent : ¬ Effect do_history do_reads 0 2 do_child := by
    simp [Effect, dependencyResolved, dependencyRefused]
  exact absent effect

/-- A real receipt and a hypothetical conflicting leaf do not justify a run refusal. -/
private noncomputable abbrev do_badRefusalReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with
    accepted := fun st b => b = 0 ∨ (b = 1 ∧ 3 ≤ st)
    refused := fun st b r pr => 4 ≤ st ∧ b = 2 ∧ r = do_history.root b ∧
      pr = do_history.root (do_history.parent b)
    priorChecks := fun st b => do_reads.priorChecks st b ∨ (st = 99 ∧ b = 2)
    conflictsFinal := fun st _ => st = 99 }

private noncomputable abbrev do_hypotheticalLeaf : FGDependencyLeaf Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) :=
  { do_leaf with
    step := fun a b o result z => do_leaf.step a b o result z ∨
      (a = 99 ∧ b = 2 ∧ o = do_child ∧ result = .definitiveRefused ∧ z = 100)
    report := fun a b o z => a = 99 ∧ b = 2 ∧ o = do_child ∧ z = 100 }

private theorem do_hypothetical_refusal_rejected :
    FGReceiptOrigin do_env do_run do_history do_wireReads false 2 do_child ∧
    do_hypotheticalLeaf.step 99 2 do_child .definitiveRefused 100 ∧
    do_badRefusalReads.accepted 99 (do_history.parent 2) ∧
    do_badRefusalReads.conflictsFinal 99 2 ∧
    ¬ do_badRefusalReads.conflictsFinal (do_trace.state 7) 2 ∧
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_badRefusalReads do_hypotheticalLeaf do_step do_trace do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨do_child_origin, Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩,
    Or.inr ⟨rfl, by decide⟩, rfl, by decide, ?_⟩
  intro laws
  have created := laws.refusal_creation 7 2 (by decide)
    ⟨by decide, rfl, rfl, rfl⟩ (by simp [dependencyRefused])
  rcases created with ⟨o, operation, _⟩ | ⟨o, operation, _⟩
  · cases operation
  · rcases operation with operation | operation <;> cases operation

#print axioms do_silent_first_receipt_rejected
#print axioms do_hypothetical_refusal_rejected

private noncomputable abbrev do_silentNotificationReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with notified := fun st b => b = 0 ∨ (b = 1 ∧ 3 ≤ st) ∨ (b = 2 ∧ 4 ≤ st) }

private theorem do_status_flag_without_hook_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_silentNotificationReads do_leaf do_step do_trace do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  obtain ⟨o, operation, _⟩ := laws.notification_creation 6 1 (by decide)
    (by simp) (by simp)
  cases operation

private noncomputable abbrev do_changedKeys : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with latestKey := fun st _ => if st < 5 then some (2, ⟨2⟩) else none }

private theorem do_notification_key_change_rejected :
    ¬ FGDependencyArrivalLeafLaws do_history do_changedKeys do_leaf do_arrival do_notify := by
  intro laws
  have eq := congrFun (laws.notification_keys 4 5 1 (Or.inl ⟨rfl, rfl, rfl⟩)) 0
  change none = some (2, (⟨2⟩ : BlockId)) at eq
  cases eq

private noncomputable abbrev do_futureOriginReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with originAvailable := fun st b o => do_reads.originAvailable st b o ∨
      (st = 1 ∧ b = 1 ∧ o = do_parent) }

private theorem do_future_origin_at_run_cut_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_futureOriginReads do_leaf do_step do_trace do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have order := (laws.origin_valid 1 1 do_parent (by decide)
    (Or.inr ⟨rfl, rfl, rfl⟩)).2
  change 5 < 1 at order
  omega

/-- The parent receipt has four real work transitions after its entry boundary. -/
private theorem do_nonempty_entry_segment :
    do_trace.entryCut 2 < do_trace.done 2 ∧
    FGDependencySteps do_step false (do_trace.state (do_trace.entryCut 2))
      (do_trace.state (do_trace.done 2)) := by
  refine ⟨by decide, ?_⟩
  have s1 : do_step .leafRetry false 2 3 := by simp [do_step]
  have s2 : do_step .leafRetry false 3 4 := by simp [do_step]
  have s3 : do_step .notification false 4 5 := by simp [do_step]
  have s4 : do_step .notification false 5 6 := by simp [do_step]
  exact .tail .notification (.tail .notification
    (.tail .leafRetry (.tail .leafRetry (.refl 2) s1) s2) s3) s4

private noncomputable abbrev do_ordinaryProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
      if wire.payload = 0 then st + 1 else do_protocol.process st wire }

private noncomputable abbrev do_ordinaryRun : V2.D.Run Bool do_ordinaryProtocol :=
  { do_run with events := [.deliver false (do_wire 0) 0] }

private noncomputable abbrev do_ordinaryWireReads :
    FGDependencyWireReads do_ordinaryProtocol (Fin 4) Nat :=
  { do_wireReads with decodeBody := fun wire =>
      if wire.payload = 0 then none else some wire.payload }

private noncomputable abbrev do_ordinaryDriver :
    FGDependencyDriver Bool (Fin 4) do_ordinaryProtocol :=
  { do_driver with enter := do_driver.enter }

/-- The actual standalone input changes knowledge. An idle entry is rejected. -/
private theorem do_silent_ordinary_rejected :
    do_ordinaryProtocol.process 0 (do_wire 0) = 1 ∧
    ¬ FGDependencyTraceLaws do_env do_ordinaryRun false do_history do_ordinaryWireReads
      do_reads do_leaf do_step do_trace do_ordinaryDriver (fun _ => .idle) do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, ?_⟩
  intro laws
  have bad := laws.delivery_entry 0 (do_wire 0) 0 rfl
  change FGDependencyOperation.idle = .ordinary (do_wire 0) at bad
  cases bad

private noncomputable abbrev do_otherOrdinary : do_protocol.Object := ⟨.none, 0⟩

private theorem do_substituted_ordinary_wire_rejected :
    do_ordinaryWireReads.decodeBody (do_wire 0) = none ∧
    do_ordinaryWireReads.decodeBody do_otherOrdinary = none ∧
    do_ordinaryProtocol.wellFormed do_otherOrdinary = true ∧
    ¬ FGDependencyTraceLaws do_env do_ordinaryRun false do_history do_ordinaryWireReads
      do_reads do_leaf do_step do_trace do_ordinaryDriver (fun _ => .ordinary do_otherOrdinary)
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro laws
  have bad := laws.delivery_entry 0 (do_wire 0) 0 rfl
  change FGDependencyOperation.ordinary do_otherOrdinary = .ordinary (do_wire 0) at bad
  have auth := congrArg V2.Signed.auth (FGDependencyOperation.ordinary.inj bad)
  cases auth

private noncomputable abbrev do_rejectedRun : V2.D.Run Bool do_protocol :=
  { do_run with events := [.deliver false (do_wire 3) 0] }

private theorem do_rejected_delivery_bound :
    ¬ FGDependencyTraceLaws do_env do_rejectedRun false do_history do_wireReads
      do_reads do_leaf do_step do_trace do_driver (fun _ => .idle) do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have bad := laws.delivery_entry 0 (do_wire 3) 0 rfl
  change FGDependencyOperation.idle = .rejected (do_wire 3) at bad
  cases bad

private theorem do_omitted_hook_read_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step { do_trace with hookRead := fun _ _ _ _ _ => False } do_driver do_op
      do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have actual := (laws.hook_correspondence 2 (.deliver false (do_wire 1) 1)
    0 .ac 10 6 rfl).mpr ⟨⟨4, .ac, 6⟩, rfl, rfl, rfl, rfl⟩
  exact actual

private noncomputable abbrev do_entryReadDriver : FGDependencyDriver Bool (Fin 4) do_protocol :=
  { do_driver with
    enterProgram := fun st wire o => .read .ac (do_driver.enter st wire o) .finish }

private theorem do_omitted_entry_read_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads do_reads do_leaf
      do_step do_trace do_entryReadDriver do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have actual := (laws.hook_correspondence 0 (.deliver false (do_wire 2) 0)
    0 .ac 1 1 rfl).mpr ⟨⟨0, .ac, 1⟩, rfl, rfl, rfl, rfl⟩
  cases actual.1

#print axioms do_omitted_entry_read_rejected

private theorem do_hook_read_nonempty_completion :
    do_trace.hookRead 2 0 .ac 10 6 ∧ do_trace.entryCut 2 < 10 ∧
    FGDependencySteps do_step false (do_trace.state (do_trace.entryCut 2)) 6 ∧
    dependencyClosed do_history do_reads 6 := by
  have completed := dependency_hook_read_completion do_trace_laws
    (e := .deliver false (do_wire 1) 1) rfl
    (show do_trace.hookRead 2 0 .ac 10 6 from ⟨rfl, rfl, rfl, rfl, rfl⟩)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by decide, completed.2.2.2⟩

/-- The public record rejects the former reflexive witness at a substituted closed cut. -/
private theorem do_substituted_closed_start_rejected :
    dependencyClosed do_history do_reads (do_trace.state 10) ∧
    ¬ FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      do_trace do_driver (fun i => { do_site i with entryCut := 10 }) do_read
      do_wireReads do_leaf do_op do_arrival do_notify (Leaf := do_leafProtocol) id id := by
  refine ⟨do_closed 6 (Or.inr rfl), ?_⟩
  intro laws
  obtain ⟨e, event, _, _, entry, _⟩ :=
    laws.site_correspondence 12 6 ⟨by decide, by decide, rfl⟩
  change 10 = 12 at entry
  omega

private theorem do_substituted_hook_start_rejected :
    FGDependencyEnabled do_history do_reads (do_trace.state (do_trace.entryCut 2)) ∧
    dependencyClosed do_history do_reads (do_trace.state 10) ∧
    ¬ FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      { do_trace with entryCut := fun j => if j = 2 then 10 else do_trace.entryCut j }
      do_driver do_site do_read do_wireReads do_leaf do_op do_arrival do_notify
      (Leaf := do_leafProtocol) id id := by
  refine ⟨?_, do_closed 6 (Or.inr rfl), ?_⟩
  · exact .retry 1 do_parent (Or.inr ⟨rfl, rfl, rfl⟩) (by decide)
      (Or.inl ⟨rfl, rfl⟩) trivial (Or.inl rfl)
      (by simp [dependencyResolved, dependencyRefused])
  · intro laws
    have wrong := (laws.trace_bound.entry_boundary 2 (.deliver false (do_wire 1) 1) rfl).1
    change 10 = 6 at wrong
    omega

#print axioms do_substituted_hook_start_rejected

private theorem do_wrong_read_kind_rejected :
    ¬ FGDependencyReadClosureLaws do_env do_run false do_history do_reads do_step
      do_trace do_driver (fun i => { do_site i with kind := .ac }) do_read
      do_wireReads do_leaf do_op do_arrival do_notify (Leaf := do_leafProtocol) id id := by
  intro laws
  obtain ⟨e, event, _, index, _⟩ :=
    laws.site_correspondence 12 6 ⟨by decide, by decide, rfl⟩
  change 12 = 15 at index
  omega

private theorem do_silence_fresh_refusal_rejected :
    ¬ FGDependencyTraceLaws do_env do_run false do_history do_wireReads
      do_badRefusalReads do_hypotheticalLeaf do_step do_trace do_driver
      (fun _ => .idle) do_arrival do_notify (Leaf := do_leafProtocol) id id do_read := by
  intro laws
  have created := laws.refusal_creation 7 2 (by decide)
    ⟨by decide, rfl, rfl, rfl⟩ (by simp [dependencyRefused])
  rcases created with ⟨o, operation, _⟩ | ⟨o, operation, _⟩
  · cases operation
  · rcases operation with operation | operation <;> cases operation

/-- A standalone PC-like object changes a latest key and enables a retained-body companion. -/
private noncomputable abbrev do_pcProtocol : V2.ProtocolSpecD Unit :=
  { do_protocol with process := fun st wire =>
      if st = 6 ∧ wire.payload = 0 then 7 else do_protocol.process st wire }

private noncomputable abbrev do_pcRun : V2.D.Run Bool do_pcProtocol :=
  { do_run with events := do_run.events ++ [.deliver false (do_wire 0) 5] }

private noncomputable abbrev do_pcReads : FGDependencyReads Nat (Fin 4)
    (FGReceiptToken Bool do_protocol.Object) Nat :=
  { do_reads with
    companionHeld := fun st b => b = 2 ∧ 6 ≤ st ∧ st ≠ 7
    latestKey := fun st _ => some (if 7 ≤ st then 3 else 2, do_history.root 2)
    latestCompanion := fun st _ => if 6 ≤ st ∧ st ≠ 7 then some 2 else none }

private noncomputable abbrev do_pcDriver : FGDependencyDriver Bool (Fin 4) do_pcProtocol :=
  { do_driver with
    enter := fun st wire o => if wire.payload = 0 then do_pcProtocol.process st wire
      else do_driver.enter st wire o
    enterProgram := fun st wire o => if wire.payload = 0 then
      .finish (do_pcProtocol.process st wire) else do_driver.enterProgram st wire o
    hookProgram := fun st op => match op with
      | .notification b _ => if st = 7 ∧ b = 2 then .read .ac 8 .finish
          else do_driver.hookProgram st op
      | _ => do_driver.hookProgram st op
    drain := fun st => if st = 7 then 8 else do_driver.drain st
    notify := fun st b o => if st = 7 ∧ b = 2 then 8 else do_driver.notify st b o
    work := fun st e => if st = 7 then [.step (.notification 2 do_child)]
      else do_driver.work st e }

private noncomputable abbrev do_pcWireReads : FGDependencyWireReads do_pcProtocol (Fin 4) Nat :=
  { do_wireReads with decodeBody := do_ordinaryWireReads.decodeBody }

private noncomputable abbrev do_pcNotify (a : Nat) (b : Fin 4) (z : Nat) : Prop :=
  do_notify a b z ∨ (a = 7 ∧ b = 2 ∧ z = 8)

private theorem do_pc_hook_laws :
    FGDependencyArrivalLeafLaws do_history do_pcReads do_leaf do_arrival do_pcNotify :=
  { do_arrival_laws with
    notification_resolved := by
      intro a z b h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;>
        simp [dependencyResolved, dependencyRefused]
    notification_keys := by
      intro a z b h
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;> rfl
    notification_fields := by
      intro a z b i h unmatched
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩
      · rfl
      · simp at unmatched
      · simp at unmatched
    notification_matching := by
      intro a z b i slot h held matching
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩
      · have bad : (2 : Nat) = 1 :=
          congrArg BlockId.value (congrArg Prod.snd (Option.some.inj matching))
        omega
      · rfl
      · rfl
    refused_notification := by intro _ _ _ _ h; exact h.elim
    callback_latest := by
      intro a z b h held
      rcases h with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨rfl, rfl, rfl⟩ <;>
        decide +kernel }

private theorem do_retained_processing_hook_effect :
    do_pcNotify 7 2 8 ∧
    do_pcReads.latestKey 7 0 = some (3, do_history.root 2) ∧
    do_pcReads.latestKey 8 0 = do_pcReads.latestKey 7 0 ∧
    do_pcReads.latestCompanion 7 0 = none ∧ do_pcReads.latestCompanion 8 0 = some 2 ∧
    (dependencyExecuteWork do_pcDriver 7
      (do_pcDriver.work 7 (.deliver false (do_wire 0) 5))).reads = [⟨1, .ac, 8⟩] :=
  ⟨Or.inr ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

#print axioms do_pc_hook_laws
#print axioms do_retained_processing_hook_effect

private theorem do_retained_processing_enables_and_completes :
    dependencyStateBefore do_env do_pcRun do_pcDriver false 4 = 6 ∧
    FGReceiptOrigin do_env do_pcRun do_history do_pcWireReads false 2 do_child ∧
    Effect do_history do_pcReads 6 1 do_parent ∧
    Effect do_history do_pcReads 6 2 do_child ∧
    do_pcProtocol.process 6 (do_wire 0) = 7 ∧
    dependencyEventEntry do_pcRun do_pcDriver false 4 6
      (.deliver false (do_wire 0) 5) = 7 ∧
    FGDependencyEnabled do_history do_pcReads 7 ∧
    (dependencyExecuteWork do_pcDriver 7
      (do_pcDriver.work 7 (.deliver false (do_wire 0) 5))).operations =
      [.notification 2 do_child] ∧
    dependencyStateBefore do_env do_pcRun do_pcDriver false 5 = 8 ∧
    dependencyClosed do_history do_pcReads 8 ∧
    do_pcReads.companionHeld (do_pcReads.latest 8) 2 := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · constructor <;> rfl
  · simp [Effect, dependencyResolved, dependencyRefused]
  · simp [Effect, dependencyResolved, dependencyRefused]
  · exact .companion 2 (Or.inr (Or.inr ⟨rfl, by decide⟩)) rfl (by simp)
  · intro work
    cases work <;> simp_all [dependencyResolved, dependencyRefused]
  · exact ⟨rfl, by decide, by decide⟩

#print axioms do_silent_ordinary_rejected
#print axioms do_substituted_ordinary_wire_rejected
#print axioms do_rejected_delivery_bound
#print axioms do_omitted_hook_read_rejected
#print axioms do_hook_read_nonempty_completion
#print axioms do_substituted_closed_start_rejected
#print axioms do_wrong_read_kind_rejected
#print axioms do_silence_fresh_refusal_rejected
#print axioms do_retained_processing_enables_and_completes

#print axioms do_status_flag_without_hook_rejected
#print axioms do_notification_key_change_rejected
#print axioms do_future_origin_at_run_cut_rejected
#print axioms do_nonempty_entry_segment

#print axioms do_read_closure_laws
#print axioms do_bridge_original_child_rows
#print axioms do_honest_old_send
#print axioms do_awake_guard_countermodel
#print axioms do_horizon_guard_countermodel
#print axioms do_validation_guard_countermodel
#print axioms do_retained_outcome_countermodel
#print axioms do_weak_delayed_model
#print axioms do_delayed_child_countermodel
#print axioms do_delayed_notification_countermodel
#print axioms do_early_read_countermodel
#print axioms do_future_in_range_receipt
#print axioms do_positive_strict_no_early_read
#print axioms do_retained_only_path_consumer
#print axioms do_state_laws
#print axioms do_arrival_laws
#print axioms do_step_laws
#print axioms do_trace_laws
#print axioms do_child_origin
#print axioms do_parent_origin
#print axioms do_same_time_positive
#print axioms do_original_epoch_after_restart
#print axioms do_wrong_receiver
#print axioms do_same_root_forgery
#print axioms do_epoch_forgery
#print axioms do_future_forgery
#print axioms do_delayed_drain_enabled
#print axioms do_delayed_notification_enabled
#print axioms do_later_read_closed_but_late
#print axioms do_retained_only_entry
#print axioms do_terminal_equality_not_strict

end AvailableChain.FGCompose.Tests.DependencyOrigins
end
