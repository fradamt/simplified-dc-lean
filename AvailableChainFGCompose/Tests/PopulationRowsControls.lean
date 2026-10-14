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

end AvailableChain.FGCompose.Tests.PopulationRowsControls
end
