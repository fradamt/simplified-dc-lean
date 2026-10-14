module
import all AvailableChainFGCompose.Tests.PopulationRows

set_option linter.privateModule false
noncomputable section

namespace AvailableChain.FGCompose.Tests.PopulationRowsControls
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGCompose.Tests.PopulationRows

private theorem client_premises_sat :
    (∀ nd, (reads.inputs nd).1 = core.source nd) ∧
    (∀ nd H, core.finalityHead nd = some H →
      (reads.inputs nd).2 = certificateHeadFields obs.height obs.finality H) ∧
    (∀ nd, HighRecordGuard_W (reads.record nd) 3 bBlock ∧
      HighRecordFresh 4 (reads.record nd)) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro nd H hH
    obtain rfl := Option.some.inj hH.symm
    change (⟨3, bBlock.root, 0⟩ : HeadFields) =
      certificateHeadFields obs.height obs.finality dBlock
    decide +kernel
  · intro nd
    simp [HighRecordGuard_W, HighRecordFresh, RecordOnce.initial, Record.initial]


#print axioms client_premises_sat

private theorem release_premises_sat :
    ∀ i q nd row,
      postClock (env Nat) run (safetyHolder reads run i) (timing.action q) = some nd →
      (env Nat).awake (safetyHolder reads run i) (timing.action q) = true →
      (createRowOnce electorate cfg (reads.record nd) i
        (reads.inputs nd).1 (reads.inputs nd).2).1 = some row →
      ∃ j, run.events[j]? = some (.tick (safetyHolder reads run i) (timing.action q)) ∧
        reads.encode (wire row) ∈ V2.D.Run.emitsAt (env Nat) run j := by
  intro i q nd row hnd _ hr
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have ht : timing.action q ≤ 32 := by
    change postClock (env Nat) run 9 (timing.action q) = some nd at hnd
    unfold postClock preTick at hnd
    obtain ⟨st, hpre, _⟩ := Option.map_eq_some_iff.mp hnd
    obtain ⟨j, hj, _⟩ := Option.map_eq_some_iff.mp hpre
    exact (schedule_premises_sat.in_horizon _
      (List.mem_of_getElem? (V2.D.Run.tickIdx?_spec hj))).2
  have hq : q ≤ 3 := by
    change 4 * ((q * 2 : Nat) : Int) + 6 ≤ 32 at ht
    push_cast at ht
    omega
  interval_cases q
  · change some 6 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    have he : (createRowOnce electorate cfg (reads.record 6) 0
        (reads.inputs 6).1 (reads.inputs 6).2).1 = some row0 := by decide +kernel
    rw [he] at hr
    obtain rfl := Option.some.inj hr.symm
    exact ⟨6, rfl, by decide +kernel⟩
  · change some 14 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    have he : (createRowOnce electorate cfg (reads.record 14) 0
        (reads.inputs 14).1 (reads.inputs 14).2).1 = some row1 := by decide +kernel
    rw [he] at hr
    obtain rfl := Option.some.inj hr.symm
    exact ⟨14, rfl, by decide +kernel⟩
  · change some 22 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    have he : (createRowOnce electorate cfg (reads.record 22) 0
        (reads.inputs 22).1 (reads.inputs 22).2).1 = some row2 := by decide +kernel
    rw [he] at hr
    obtain rfl := Option.some.inj hr.symm
    exact ⟨22, rfl, by decide +kernel⟩
  · change some 30 = some nd at hnd
    obtain rfl := Option.some.inj hnd
    have he : (createRowOnce electorate cfg (reads.record 30) 0
        (reads.inputs 30).1 (reads.inputs 30).2).1 = some row3 := by decide +kernel
    rw [he] at hr
    obtain rfl := Option.some.inj hr.symm
    exact ⟨30, rfl, by decide +kernel⟩

#print axioms release_premises_sat

private theorem reflection_premises_sat (A B : FGBlock (Fin 1))
    (h : Block.Preceq (erase A) (erase B)) : FGBlock.Preceq A B := by
  have inj : Function.Injective erase := by
    intro X
    induction X with
    | genesis => intro Y he; cases Y <;> simp_all [erase]
    | node p s r x rs ih =>
      intro Y he
      cases Y with
      | genesis => simp [erase] at he
      | node q t u y ts =>
        simp only [erase, Block.node.injEq] at he
        obtain ⟨hp, hs, hr, hb⟩ := he
        obtain ⟨hx, hrows⟩ := encFGBody_inj hb
        cases ih hp
        cases hs
        cases hr
        cases hx
        cases hrows
        rfl
  induction B with
  | genesis =>
    have he : erase A = erase .genesis := of_decide_eq_true h
    exact inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (erase A = erase (.node P slot root app rows)) ||
      Block.preceq (erase A) (erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

#print axioms reflection_premises_sat

private theorem pending_premises_sat : ∃ m : middleType run,
    (m.A₀ = aBlock ∧ m.B = bBlock ∧ m.U = bBlock ∧ m.X_D = dBlock ∧
      m.cD = 6 ∧ m.d = 2) ∧
    (∀ x nd, x ∈ run.honest → postClock (env Nat) run x 30 = some nd →
      ∃ H, core.finalityHead nd = some H ∧ FGBlock.Preceq m.X_D H ∧
        (obs.height H).h = m.d + 2 ∧ (obs.height H).J = m.U ∧
        (obs.height H).h_j = m.d + 1 ∧ (obs.finality H).h_F < m.d + 1 ∧
        (obs.height H).T_h = (obs.height m.X_D).T_h) := by
  obtain ⟨m, selected, act⟩ := action_premises_sat
  refine ⟨m, selected, ?_⟩
  exact rowsPrem_pending_head_holder m
    (KitFG.Window.windowHeightLaws electorate cfg 2 (by decide))
    (KitFG.Window.windowHeightBridge electorate cfg 2 (by decide)) act.read act.head act.walk
    (fun _ A B _ _ hp => reflection_premises_sat A B hp)

#print axioms pending_premises_sat

private theorem fresh_rows_premises_sat : ∃ m : middleType run,
    m.X_D = dBlock ∧ m.U = bBlock ∧ m.d = 2 ∧
    (∀ x ∈ run.honest, ∃ H, core.finalityHead 30 = some H ∧
      FGBlock.Preceq m.X_D H ∧ (obs.height H).J = m.U ∧ (obs.height H).h_j = 3) ∧
    (∀ x ∈ run.honest, HighRecordGuard_W (reads.record 30) 3 m.U ∧
      HighRecordFresh 4 (reads.record 30)) ∧
    ∃ rows : Fin 1 → protocol.Object,
      FreshFinalityRows_W core reads obs timing (env Nat) run history electorate
        (fun _ => true) 3 3 m.U {0} rows ∧
      (∀ i ∈ ({0} : Finset (Fin 1)), history.heightPair (rows i) =
        .vote 4 (obs.height m.X_D).T_h.root false) := by
  obtain ⟨m, ⟨_, _, hU, hD, _, hd⟩, heads⟩ := pending_premises_sat
  have sources : ∀ x ∈ run.honest, ∃ nd C,
      postClock (env Nat) run x (timing.action (pt.r + 2)) = some nd ∧
      core.source nd = some C ∧ FGBlock.Preceq m.X_D C ∧
      (obs.height C).h = m.d + 2 ∧ (obs.height C).T_h = (obs.height m.X_D).T_h := by
    intro x hx
    rw [hD, hd]
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    all_goals exact ⟨30, dBlock, by decide +kernel, rfl, preceq_refl _,
      by decide +kernel, rfl⟩
  have records : ∀ x nd, x ∈ run.honest →
      postClock (env Nat) run x (timing.action (pt.r + 2)) = some nd →
      HighRecordGuard_W (reads.record nd) (m.d + 1) m.U ∧
        HighRecordFresh (m.d + 2) (reads.record nd) := by
    intro x nd _ _
    rw [hd, hU]
    exact client_premises_sat.2.2 nd
  have result := rowsPrem_fresh_rows_holder m
    (KitFG.Window.windowHeightLaws electorate cfg 2 (by decide))
    (KitFG.Window.windowHeightBridge electorate cfg 2 (by decide)) wire
    (fun _ => rfl) (fun _ _ _ _ => rfl) client_premises_sat.1 release_premises_sat
    sources heads client_premises_sat.2.1 records timing_premises_sat {0}
    (by intro i _; change (9 : Nat) ∈ run.honest; decide)
    (by change (1 : Nat) ≤ 1; decide) (by intros; rfl)
  refine ⟨m, hD, hU, hd, ?_, ?_, ?_⟩
  · intro x hx
    have hnd : postClock (env Nat) run x 30 = some 30 := by
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> decide +kernel
    obtain ⟨H, hH, hp, _, hJ, hj, _⟩ := heads x 30 hx hnd
    exact ⟨H, hH, hp, hJ, by simpa only [hd] using hj⟩
  · intro x hx
    rw [hU]
    exact client_premises_sat.2.2 30
  · obtain ⟨rows, fresh, _, hp⟩ := result
    exact ⟨rows, by simpa only [hd] using fresh, by simpa only [hd] using hp⟩

#print axioms fresh_rows_premises_sat

end AvailableChain.FGCompose.Tests.PopulationRowsControls
end
