module
public import AvailableChainFGCompose.Statements.ExecutionBridges -- shake: keep (examples)
public import AvailableChainFGCompose.Proofs.ExecutionObs

set_option linter.privateModule false

public section

/-! Controls for the shared execution observation. Level: generic event fold (an interface
model, not an ExecutionValid protocol fixture). The positive instance is the ordinary
Duty fold on an explicit run with an equal-time restart and tick, then a delivery. The
probes drop an event or reorder equal-time cuts and fail a stated law. -/

namespace AvailableChain.FGCompose.Tests.X1a
open AvailableChain.SimplexFG

private theorem rows_nil (rs : List (Row (Fin 0))) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons row _ => exact Fin.elim0 row.signer

private def erase : FGBlock (Fin 0) → Block
  | .genesis => .genesis
  | .node p s r x _ => .node (erase p) s r x

private theorem erase_inj : Function.Injective erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp [erase] at h ⊢
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [erase] at h
    | node p' s' r' x' rs' =>
      simp only [erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hx⟩ := h
      have hpp := ih hp
      subst p' s' r' x'
      rw [rows_nil rs, rows_nil rs']

-- Each operation changes the counter, so a dropped or reordered event is visible.
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Unit
  init := 0
  clock := fun st _ => st + 1
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st + 10
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => 100
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

private noncomputable abbrev obj : protocol.Object := ⟨.none, ()⟩

private noncomputable abbrev mkRun (es : List (V2.Event Unit protocol.Object)) :
    V2.D.Run Unit protocol where
  honest := {()}
  horizon := 5
  events := es
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

/-- Restart and tick at the same time 1, then a delivery at 2. -/
private noncomputable abbrev trace : V2.D.Run Unit protocol :=
  mkRun [.restart () 1, .tick () 1, .deliver () obj 2]

private noncomputable abbrev obs : FGExecutionObs Unit protocol :=
  ordinaryFGExecutionObs env trace

/-! ### Positive instance: every premise is proved on the explicit run. -/

private theorem exec_laws : FGExecutionObsLaws env trace obs :=
  ordinaryFGExecutionObs_laws env trace

private noncomputable abbrev reads : FGCoreReads protocol 0 Unit Unit Unit where
  core _ := ⟨(), Store.init, [], []⟩
  erase := erase
  source := fun _ => some .genesis
  headVote := fun _ _ => erase .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem core_laws : FGCoreLaws reads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := fun _ h => h
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases Option.some.inj h; exact Finset.mem_singleton_self _
  erase_inj := erase_inj

private theorem head_laws : FGHeadLaws reads env trace where
  head_mem _ _ _ _ := ⟨.genesis, Finset.mem_singleton_self _, rfl⟩
  parent_closed _ _ B hB := by
    have : B = .genesis := by simpa [Store.init] using hB
    subst this
    exact hB

private theorem restore_laws : FGTreeRestoreLaws reads := ⟨fun _ _ => rfl⟩

private theorem core_obs : FGObservedCoreLaws reads trace obs :=
  ordinaryFGExecutionObs_core env trace reads core_laws head_laws restore_laws

private theorem finality_obs : FGObservedFinalityLaws reads trace obs :=
  ordinaryFGExecutionObs_finality env trace reads core_laws
    (fun _ _ => KitFG.preceq_refl _) ⟨fun _ _ => rfl⟩

/-- Inspected cuts: raw restore, clock (duty), completion, raw delivery entry. -/
private theorem inspected_cuts :
    obs.cutState () (obs.entry () 0) = 100 ∧ obs.cutState () (obs.duty () 1) = 101 ∧
      obs.cutState () (obs.done () 1) = 101 ∧ obs.cutState () (obs.done () 2) = 111 ∧
      obs.cutLength () = 9 := by
  decide

/-- The equal-time restart cut precedes the tick cut, both at time 1. -/
private theorem equal_time_order :
    obs.done () 0 < obs.start () 1 ∧ obs.cutTime () (obs.done () 0) = 1 ∧
      obs.cutTime () (obs.start () 1) = 1 :=
  ⟨exec_laws.event_order 0 1 _ _ () rfl rfl (by decide),
    exec_laws.segment_time 0 _ () _ rfl (by decide) le_rfl,
    exec_laws.segment_time 1 _ () _ rfl le_rfl (by decide)⟩

/-- The delivery is accepted at its entry step with its original token. -/
private theorem delivery_accepted :
    obs.accepts () 6 (fgEventToken trace () 2 obj 2) :=
  ⟨2, obj, 2, rfl, rfl, rfl⟩

private theorem delivery_origin :
    (fgEventToken trace () 2 obj 2).receiptTime ≤ obs.cutTime () 6 ∧
      trace.events[(fgEventToken trace () 2 obj 2).eventIndex]? = some (.deliver () obj 2) :=
  ⟨exec_laws.accept_time _ _ _ delivery_accepted,
    (exec_laws.accept_origin _ _ _ delivery_accepted).2.2.1⟩

/-- The HEAD read at the tick's duty cut is held there with its history. -/
private theorem head_at_duty :
    ∃ B ∈ (reads.core (obs.cutState () (obs.duty () 1))).fg.TF,
      reads.erase B = reads.headVote (obs.cutState () (obs.duty () 1)) 0 :=
  core_obs.head_mem 1 () 1 0 rfl

private theorem chain_rows_at_cut : FGChainRowsAtCut reads trace obs .genesis 2 := by
  intro W hW row hrow
  cases W with
  | genesis => cases hrow
  | node _ _ _ _ rs => cases rs with
    | nil => cases hrow
    | cons r _ => exact Fin.elim0 r.signer

/-! ### Adversarial probes -/

/-- The run without the tick. -/
private noncomputable abbrev dropped : V2.D.Run Unit protocol :=
  mkRun [.restart () 1, .deliver () obj 2]

/-- An instance that drops the tick fails the clock-entry law. -/
private theorem dropped_fails :
    ¬ FGExecutionObsLaws env trace (ordinaryFGExecutionObs env dropped) := by
  intro h
  have := h.tick_entry 1 () 1 rfl
  revert this
  decide

/-- The run with the equal-time restart and tick swapped. -/
private noncomputable abbrev swapped : V2.D.Run Unit protocol :=
  mkRun [.tick () 1, .restart () 1, .deliver () obj 2]

/-- An instance that applies the equal-time tick before the restart fails the raw-restore
entry law. -/
private theorem swapped_fails :
    ¬ FGExecutionObsLaws env trace (ordinaryFGExecutionObs env swapped) := by
  intro h
  have := h.restart_entry 0 () 1 rfl
  revert this
  decide

/-- An instance with the correct states but reversed equal-time cut maps. -/
private noncomputable abbrev reversedCuts : FGExecutionObs Unit protocol :=
  { obs with
    start := fun _ j => if j = 0 then 3 else if j = 1 then 0 else 3 * j
    entry := fun _ j => if j = 0 then 4 else if j = 1 then 1 else 3 * j + 1
    duty := fun _ j => if j = 0 then 4 else if j = 1 then 1 else 3 * j + 1
    done := fun _ j => if j = 0 then 5 else if j = 1 then 2 else 3 * j + 2 }

private theorem reversed_cuts_fail : ¬ FGExecutionObsLaws env trace reversedCuts := by
  intro h
  have := h.event_order 0 1 _ _ () rfl rfl (by decide)
  revert this
  decide

/-- A release attributed to a non-tick event fails the release law. -/
private noncomputable abbrev extraRelease : FGExecutionObs Unit protocol :=
  { obs with released := fun _ j => if j = 2 then [obj] else [] }

private theorem extra_release_fails : ¬ FGExecutionObsLaws env trace extraRelease := by
  intro h
  have := h.released_other 2 () (fun t ht => by cases ht)
  revert this
  decide

#print axioms exec_laws
#print axioms core_laws
#print axioms head_laws
#print axioms restore_laws
#print axioms core_obs
#print axioms finality_obs
#print axioms inspected_cuts
#print axioms equal_time_order
#print axioms delivery_accepted
#print axioms delivery_origin
#print axioms head_at_duty
#print axioms chain_rows_at_cut
#print axioms dropped_fails
#print axioms swapped_fails
#print axioms reversed_cuts_fail
#print axioms extra_release_fails

end AvailableChain.FGCompose.Tests.X1a
end
