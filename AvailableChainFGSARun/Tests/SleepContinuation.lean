module
public import AvailableChainFGSARun.Tests.Sleep
public import AvailableChainFGSARun.Proofs.Schedule

public section

namespace AvailableChain.FGSA.Run.SleepContinuationTests

open SleepTests

/-- The stored proposal has a delivery before the wake and is kept across it. -/
theorem retained_origin :
    ∃ j o t, j < 9 ∧ run.events[j]? = some (.deliver 0 o t) ∧
      toWire p o = toWire p proposal ∧ j + 1 ≤ 8 ∧
      ∀ k, j + 1 ≤ k → k ≤ 9 →
        toWire p proposal ∈ (V2.D.Run.stateBefore env run k 0).st.proposals := by
  obtain ⟨j, o, t, hj, hd, ho, -, hr⟩ :=
    stored_proposal_delivered env run 9 0 (toWire p proposal) (by decide +kernel)
  have he : o = proposal := toWire_injective ho
  subst o
  have hje : j = 5 := by
    interval_cases j <;> simp [run] at hd ⊢
    have he : row = proposal := (V2.Event.deliver.inj hd).2.1
    have hm := congrArg (fun o : Obj p => o.payload) he
    change Msg.row _ = Msg.proposal _ at hm
    cases hm
  exact ⟨j, proposal, t, hj, hd, ho, by omega, hr⟩

/-- A joined node reads a strict clock bound after an exact-boundary wake. -/
theorem joined_strict :
    (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 6 0).st.base.now < 16 := by
  exact fgsa_preTick_now_lt_joined (joinEnv 8) (joinRun 8)
    (join_valid 8 (Or.inl rfl)).1.toScheduleWellFormed (by decide) (by decide)
    (by decide +kernel)

/-- Same-time wake and tick have non-strict clock and vote-stamp bounds. -/
theorem same_time_bound :
    (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base.now ≤ 8 ∧
    ∀ o : GridCO.Wire p.n .root,
      GridCO.stampVote (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base o ≤ 8 := by
  have hs := (join_valid 8 (Or.inl rfl)).1.toScheduleWellFormed
  exact ⟨fgsa_preTick_now_le (joinEnv 8) (joinRun 8) hs (by decide),
    fgsa_preTick_votes_stamped_le (joinEnv 8) (joinRun 8) hs (by decide)⟩

/-- Kept blocks remain below the next proposal slot, even for an unjoined node. -/
theorem retained_block_bound :
    (∀ b ∈ (V2.D.Run.stateBefore env run 10 0).st.base.blocks, b.slot < 2) ∧
    (namedProposal p .genesis 1 0 [] [] []).erase ∈
      (V2.D.Run.stateBefore env run 10 0).st.base.blocks := by
  exact ⟨(fgsa_stored_block_slots env run valid.toScheduleWellFormed
    (by decide) (by decide : 0 < 2)).1, by decide +kernel⟩

/-- The epoch condition fails exactly at the same-time wake boundary. -/
theorem wake_epoch_equiv :
    let epoch := ∀ j w, j < 2 → (joinRun 8).events[j]? = some (.restart 0 w) → w < 8
    ((V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base.now < 8 ↔ epoch) ∧
      ¬ epoch := by
  refine ⟨fgsa_preTick_now_lt_iff (joinEnv 8) (joinRun 8)
    (join_valid 8 (Or.inl rfl)).1.toScheduleWellFormed (by decide) (by decide), ?_⟩
  intro h
  exact (lt_irrefl (8 : Time)) (h 1 8 (by decide) (by decide))

/-- API coverage for the unjoined companion; the raw fixture result is also empty. -/
theorem gate_empty :
    GridCO.savedGenuine (FGSA.clock p
      (V2.D.Run.stateBefore (joinEnv 9) (joinRun 9) 7 0).st
      (SA.gateTime p.toParams 1)).base 1 = some none := by
  exact fgsa_gate_saved_unjoined (joinEnv 9) (joinRun 9)
    (join_valid 9 (Or.inr rfl)).1.toScheduleWellFormed (by decide) (by decide +kernel)

/-- Public admission thresholds do not require public wakes. -/
theorem admission_public (o : Obj p) : V2.PublicTime env (fgsaAdmissionTime p o) :=
  fgsa_admissionTime_public p env rfl o

end AvailableChain.FGSA.Run.SleepContinuationTests
end

#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.retained_origin
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.joined_strict
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.same_time_bound
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.retained_block_bound
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.wake_epoch_equiv
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.gate_empty
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.admission_public
