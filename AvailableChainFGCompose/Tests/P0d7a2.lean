module
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window law fixture)
public import AvailableChainFGCompose.Proofs.Finality.RecordInv

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7a2
open AvailableChain.SimplexFG AvailableChain.KitFG

-- The proposed layer repair is an exact expansion, with no semantic change.
private theorem d7g_own_origin_expansion
    {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
    {n : Nat} {Wire : Type} (S : FGSafetyReads P n Wire) (T : FGTiming)
    (E : Generic.Env V) (rho : V2.D.Run V P) :
    HighRecordOwnOrigin S T E rho =
      (∀ j x o u, x ∈ rho.honest →
        o ∈ (if (rho.events[j]?).map V2.Event.node = some x then
          (V2.D.Run.emitsAt E rho j).filter P.objSelfVisible else []) →
        S.decodeObject o = some u →
        ∃ r a, HonestRowAt S E rho T j x r a ∧ S.decode a = some u) := by
  simp only [HighRecordOwnOrigin, V2.D.Engine.ownReleasedAt_def]

-- Inhabited interface trace; no FG-SA or PC-SA ExecutionValid claim is made.
private abbrev d7g_E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev d7g_cfg : FGConfig := ⟨4⟩
private abbrev d7g_hd : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev d7g_boot : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev d7g_X : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [d7g_boot]
private abbrev d7g_Y : FGBlock (Fin 1) := .node d7g_X 2 ⟨2⟩ 0 []
private abbrev d7g_Z : FGBlock (Fin 1) := .node .genesis 1 ⟨9⟩ 0 [d7g_boot]
private abbrev d7g_row : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩
private abbrev d7g_old : RecordOnce := record_row_once RecordOnce.initial d7g_row
private abbrev d7g_source (nd : RecordOnce) := if nd.sent.isEmpty then d7g_X else d7g_Y

private theorem d7g_parent_paths :
    d7g_X ≠ .genesis ∧ d7g_Y.parent = d7g_X ∧ FGBlock.Preceq d7g_X d7g_Y ∧
      (derive d7g_E d7g_cfg d7g_X).h = 2 ∧ (derive d7g_E d7g_cfg d7g_Y).h = 2 := by
  decide +kernel

private theorem d7g_current :
    (createRowOnce d7g_E d7g_cfg RecordOnce.initial 0 (some d7g_X) d7g_hd).1 =
      some d7g_row := by decide +kernel

private theorem d7g_guard_choice :
    height_pair d7g_old.toRecord (some (2, ⟨1⟩)) none = .vote 2 ⟨1⟩ false := by
  exact high_record_target_choice _ _ _ _ (Or.inr (by decide +kernel)) rfl (Or.inl rfl)
    (by intro f h; cases h)

private theorem d7g_prior :
    (createRowOnce d7g_E d7g_cfg d7g_old 0 (some d7g_Y) d7g_hd).1 = none ∧
      d7g_row.onceKey ∈ d7g_old.sent := by decide +kernel

private theorem d7g_timeout_rejected :
    ¬ HighRecordGuard_W (record_row_once RecordOnce.initial
      (⟨0, .vote 2 ⟨1⟩ true, none⟩ : Row (Fin 1))) 2 d7g_X := by
  intro h
  have hf : true = false := h.2.1
  cases hf

private theorem d7g_wrong_target_rejected :
    ¬ HighRecordGuard_W (record_row_once RecordOnce.initial
      (⟨0, .vote 2 ⟨9⟩ false, none⟩ : Row (Fin 1))) 2 d7g_X := by
  intro h
  rcases h.1 with h | h <;> cases h

private theorem d7g_finality_lock :
    height_pair Record.initial (some (2, ⟨1⟩)) (some ⟨2, ⟨1⟩⟩) = .vote 2 ⟨1⟩ false ∧
    height_pair Record.initial (some (2, ⟨1⟩)) (some ⟨2, ⟨9⟩⟩) = .empty := by
  decide +kernel

noncomputable section
private abbrev d7t_P : V2.ProtocolSpecD Unit where
  State := RecordOnce
  Label := Unit
  Duty := Time
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := RecordOnce
  init := RecordOnce.initial
  clock := fun nd _ => nd
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun nd _ _ => (createRowOnce d7g_E d7g_cfg nd 0 (some (d7g_source nd)) d7g_hd).1
  gossip := fun _ _ => []
  process := fun nd _ => nd
  selfVisible := fun _ => true
  recordOwn := fun nd o => match o.auth with
    | .seat _ i => record_row_once nd { o.payload with signer := i }
    | .none => nd
  durable := id
  restore := fun nd _ => nd
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev d7t_S : FGSafetyReads d7t_P 1 d7t_P.Object where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := id
  decode := fun o => match o.auth with
    | .seat _ i => some { o.payload with signer := i }
    | .none => none
  decodeObject := fun o => match o.auth with
    | .seat _ i => some { o.payload with signer := i }
    | .none => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := id
  inputs := fun nd => (some (d7g_source nd), d7g_hd)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

private abbrev d7t_entry (a : d7t_P.Object) := namedEntry a.payload.height_pair
private abbrev d7t_wire : d7t_P.Object := ⟨.seat () 0, d7g_row⟩
private abbrev d7t_T : FGTiming where
  delta := 1
  roundSlots := 2
  proposal := fun s => 4 * s
  vote := fun s => 4 * s + 1
  early := fun s => 4 * s + 2
  freeze := fun s => 4 * s + 3
  release := fun s => 4 * s + 5
  gate := fun s => 4 * s + 6
  action := fun r => 4 * (r * 2 : Nat) + 6

private theorem d7t_timing : FGTimingLaws d7t_T where
  delta_pos := by decide
  rounds := by decide
  proposal_eq := by intro s; simp
  vote_eq := by intro s; rfl
  early_eq := by intro s; rfl
  freeze_eq := by intro s; rfl
  release_eq := by intro s; rfl
  gate_eq := by intro s; rfl
  action_eq := by intro r; rfl

private abbrev d7t_env : Generic.Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ t => decide (t = 6 ∨ t = 14)

private abbrev d7t_run : V2.D.Run (Fin 1) d7t_P where
  honest := {0}
  horizon := 14
  events := [.tick 0 6, .restart 0 14, .tick 0 14]
  seatOf := fun _ i => i
  input := fun _ _ => ()

private theorem d7t_schedule : V2.D.ScheduleWellFormed d7t_env d7t_run where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro ev hm
    change ev ∈ [.tick 0 6, .restart 0 14, .tick 0 14] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  honest_only := by
    intro ev hm
    change ev ∈ [.tick 0 6, .restart 0 14, .tick 0 14] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  tick_public := by
    intro x t hm
    change V2.Event.tick x t ∈ [.tick 0 6, .restart 0 14, .tick 0 14] at hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      reduceCtorEq, or_false, false_or] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨14, rfl⟩
  tick_total := by
    intro x _ t _ _ _ ha
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have ht : t = 6 ∨ t = 14 := of_decide_eq_true ha
    rcases ht with rfl | rfl <;> simp

private theorem d7t_client : FGSafetyClientLaws d7t_S d7g_E d7g_cfg where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record := by
    intro nd o
    cases o with
    | mk auth payload => cases auth <;> rfl
  tick_rows := by
    intro V _ E rho e he nd x t
    have hx : e 0 = x := by
      rw [← e.apply_symm_apply x]
      congr 1
      exact Subsingleton.elim _ _
    have hs : e.symm x = 0 := Subsingleton.elim _ _
    have hseat : rho.seatOf () 0 = x := (he 0).trans hx
    have hsigner : ∀ u : Row (Fin 1), { u with signer := (0 : Fin 1) } = u := by
      intro u
      have hu : u.signer = 0 := Subsingleton.elim _ _
      cases u
      cases hu
      rfl
    cases ha : E.awake x t <;>
      cases hr : (createRowOnce d7g_E d7g_cfg nd 0 (some (d7g_source nd)) d7g_hd).1 <;>
      simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, hs, hr, hseat]
    rename_i u
    change [{ u with signer := (0 : Fin 1) }] = [u]
    rw [hsigner]

private theorem d7t_wires : FGRowPermissionWireLaws d7t_S d7t_entry where
  decoded_wire := by
    intro o u hu
    refine ⟨o, rfl, hu, ?_⟩
    cases o with
    | mk auth payload =>
      cases auth with
      | none => cases hu
      | seat label i => cases hu; rfl

private abbrev d7t_D : FGHistoryWireReads d7t_S where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer a := match a.auth with | .seat _ i => some i | .none => none
  decode_height a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl
  decode_finality a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl
  decode_signer a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl

private theorem d7t_fresh_origin :
    HonestRowAt d7t_S d7t_env d7t_run d7t_T 0 0 0 d7t_wire := by
  refine ⟨by decide, rfl, ?_⟩
  decide +kernel

private theorem d7t_restart_record :
    V2.D.Run.stateBefore d7t_env d7t_run 1 0 = d7g_old ∧
    V2.D.Run.stateBefore d7t_env d7t_run 2 0 = d7g_old ∧
    d7t_run.events[1]? = some (.restart 0 (d7t_T.action 1)) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem d7t_suppressed :
    V2.D.Run.emitsAt d7t_env d7t_run 2 = [] := by decide +kernel

private theorem d7t_only_row {j r : Nat} {x : Fin 1} {a : d7t_P.Object}
    (ha : HonestRowAt d7t_S d7t_env d7t_run d7t_T j x r a) :
    j = 0 ∧ x = 0 ∧ r = 0 ∧ a = d7t_wire := by
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rcases ha with ⟨_, ht, ha⟩
  have hidx : j < 3 := (List.getElem?_eq_some_iff.mp ht).1
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · have ht' : 6 = 4 * ((r : Int) * 2) + 6 := by
      exact Option.some.inj (congrArg (fun ev => ev.map V2.Event.time) ht)
    have hr : r = 0 := by omega
    have hw : a = d7t_wire := List.mem_singleton.mp ha
    exact ⟨rfl, rfl, hr, hw⟩
  · cases ht
  · rw [d7t_suppressed] at ha; cases ha

private theorem d7t_emission :
    HighRecordEmission d7t_S d7t_T d7t_env d7t_run d7g_E d7g_cfg := by
  intro j x r a u ha hd
  obtain ⟨rfl, rfl, rfl, rfl⟩ := d7t_only_row ha
  have hu : d7g_row = u := Option.some.inj hd
  subst u
  exact d7g_current

private theorem d7t_own : HighRecordOwnOrigin d7t_S d7t_T d7t_env d7t_run := by
  intro j x o u _hx ho hd
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rw [V2.D.Engine.ownReleasedAt_def] at ho
  split at ho
  · rename_i hnode
    have hem := (List.mem_filter.mp ho).1
    have hidx : j < 3 := by
      by_contra hn
      have hnone : d7t_run.events[j]? = none := List.getElem?_eq_none (by change 3 ≤ j; omega)
      rw [hnone] at hnode
      cases hnode
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · have hw : o = d7t_wire := List.mem_singleton.mp hem
      subst o
      exact ⟨0, d7t_wire, d7t_fresh_origin, hd⟩
    · cases hem
    · rw [d7t_suppressed] at hem; cases hem
  · cases ho

private theorem d7t_fresh_after_restart :
    HighRecordFresh 3 (d7t_S.record (V2.D.Run.stateBefore d7t_env d7t_run 2 0)) := by
  apply high_record_fresh_at_cut (D := d7t_D) d7t_client d7t_emission d7t_own 2 0 3 (by decide)
  intro j r a h _hj ha hh
  obtain ⟨rfl, _, rfl, rfl⟩ := d7t_only_row ha
  have he : 2 = h := Option.some.inj hh
  omega

private theorem d7t_prior_exact :
    ∃ j r a, j = 0 ∧ r = 0 ∧ a = d7t_wire ∧ j < 2 ∧
      HonestRowAt d7t_S d7t_env d7t_run d7t_T j 0 r a ∧
      d7t_D.heightPair a = .vote 2 ⟨1⟩ false :=
  ⟨0, 0, d7t_wire, rfl, rfl, rfl, by decide, d7t_fresh_origin, rfl⟩

private def d7t_erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (d7t_erase p) s r (encFGBody x rs)

private theorem d7t_erase_inj : Function.Injective d7t_erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [d7t_erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [d7t_erase] at h
    | node q t u y ts =>
      simp only [d7t_erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem d7t_reflect (A B : FGBlock (Fin 1))
    (h : Block.Preceq (d7t_erase A) (d7t_erase B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
    have he : d7t_erase A = d7t_erase .genesis := of_decide_eq_true h
    exact d7t_erase_inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (d7t_erase A = d7t_erase (.node P slot root app rows)) ||
      Block.preceq (d7t_erase A) (d7t_erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact d7t_erase_inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

private abbrev d7t_R : FGCoreReads d7t_P 1 Unit Unit d7t_P.Object where
  core _ := ⟨(), ⟨{.genesis, d7g_X, d7g_Y}, .genesis, .genesis, 0, 2⟩, [], []⟩
  erase := d7t_erase
  source nd := some (d7g_source nd)
  headVote _ _ := d7t_erase d7g_Y
  finalityHead _ := some d7g_Y
  proposalFG _ _ := none

private abbrev d7t_O : FGObservationReads d7t_R where
  height := KitFG.Window.certificateHeight d7g_E d7g_cfg 2
  finality := KitFG.Window.certificateFinality d7g_E d7g_cfg 2
  controls nd := treeStoreControlsView (simplexHeightView d7g_E d7g_cfg) (d7t_R.core nd).fg
  viable _ trees := trees

private abbrev d7t_point : FGServicePoint :=
  ⟨⟨0, 0, 1, 0, 0, d7t_erase d7g_X⟩, 2, d7t_erase d7g_Y, 8⟩

private theorem d7t_source_cases {x : Fin 1} {r : Nat} {C : FGBlock (Fin 1)}
    (h : actionSourceFG d7t_R d7t_env d7t_run d7t_T x r = some (some C)) :
    C = d7g_X ∨ C = d7g_Y := by
  obtain ⟨nd, _, hs⟩ := Option.map_eq_some_iff.mp h
  have he : d7g_source nd = C := Option.some.inj hs
  unfold d7g_source at he
  split at he
  · exact Or.inl he.symm
  · exact Or.inr he.symm

private theorem d7t_history (horizon : Time) :
    FGHistoricalHighChain d7t_R d7t_O d7t_T d7t_env d7t_run d7t_point horizon := by
  intro x z r q C B _hx _hz hC hB _hc _hb _hr _hq
  rcases d7t_source_cases hC with rfl | rfl <;>
    rcases d7t_source_cases hB with rfl | rfl
  all_goals exact ⟨by unfold Block.Compatible; decide +kernel,
    by unfold Block.Compatible; decide +kernel, Nat.zero_le _⟩

private theorem d7t_pre_service_sources :
    actionSourceFG d7t_R d7t_env d7t_run d7t_T 0 0 = some (some d7g_X) ∧
    actionSourceFG d7t_R d7t_env d7t_run d7t_T 0 1 = some (some d7g_Y) ∧
    d7t_T.action 0 < d7t_point.serviceStart := by
  decide +kernel

private theorem d7t_equal_height_entry :
    (d7t_O.height d7g_X).T_h = (d7t_O.height d7g_Y).T_h := by
  exact high_source_entry_eq d7t_history
    (KitFG.Window.windowCertificateLaws d7g_E d7g_cfg 2
      (by unfold Electorate.IsQuorum; decide +kernel) (by decide))
    d7t_reflect 0 0 0 1 d7g_X d7g_Y (by decide) (by decide) d7t_pre_service_sources.1
    d7t_pre_service_sources.2.1 (by unfold high; decide +kernel)
    (by unfold high; decide +kernel) (by decide +kernel)


private abbrev d7t_badR : FGCoreReads d7t_P 1 Unit Unit d7t_P.Object :=
  { d7t_R with source := fun nd => some (if nd.sent.isEmpty then d7g_Z else d7g_Y) }

private abbrev d7t_badO : FGObservationReads d7t_badR where
  height := KitFG.Window.certificateHeight d7g_E d7g_cfg 2
  finality := KitFG.Window.certificateFinality d7g_E d7g_cfg 2
  controls nd := d7t_O.controls nd
  viable _ trees := trees

-- A high row from the earlier fork has a real parent path and a different entry.
private theorem d7t_fork_nontrivial :
    d7g_Z ≠ .genesis ∧ (d7t_O.height d7g_Z).h = 2 ∧
      (d7t_O.height d7g_Z).T_h ≠ (d7t_O.height d7g_Y).T_h ∧
      ¬ Block.Compatible (d7t_erase d7g_Z) (d7t_erase d7g_Y) := by
  unfold Block.Compatible
  decide +kernel

private theorem d7t_reject_historical_fork :
    ¬ FGHistoricalHighChain d7t_badR d7t_badO d7t_T d7t_env d7t_run d7t_point 14 := by
  intro h
  have bad := (h 0 0 0 1 d7g_Z d7g_Y (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)).1
  exact d7t_fork_nontrivial.2.2.2 bad


end

#print axioms d7g_own_origin_expansion
#print axioms d7g_parent_paths
#print axioms d7g_current
#print axioms d7g_guard_choice
#print axioms d7g_prior
#print axioms d7g_timeout_rejected
#print axioms d7g_wrong_target_rejected
#print axioms d7g_finality_lock
#print axioms d7t_client
#print axioms d7t_fresh_origin
#print axioms d7t_restart_record
#print axioms d7t_suppressed
#print axioms d7t_emission
#print axioms d7t_own
#print axioms d7t_fresh_after_restart
#print axioms d7t_prior_exact

#print axioms d7t_history
#print axioms d7t_pre_service_sources
#print axioms d7t_equal_height_entry
#print axioms d7t_fork_nontrivial
#print axioms d7t_reject_historical_fork

end AvailableChain.FGCompose.Tests.P0d7a2
end
