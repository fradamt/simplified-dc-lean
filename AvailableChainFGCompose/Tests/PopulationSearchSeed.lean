module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRepair
import all AvailableChainFGCompose.Tests.PopulationService

set_option linter.privateModule false

noncomputable section
namespace AvailableChain.FGCompose.Tests.PopulationSearchSeed
open AvailableChain.SimplexFG AvailableChain.KitFG
open AvailableChain.FGCompose.Tests.PopulationService

/-! Generic ordinary-event-fold control: the exact POP-4 mixed run, now consumed by
POP-5's saved-seed theorem. Its proposer is 7; only holder 9 releases an FG row. -/

private abbrev seedObs : FGObservationReads core where
  height := height
  finality := fun _ => ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView height (core.core nd).fg
  viable nd X := treeStoreFrameView height (core.core nd).fg X

private theorem saved_seed_premises_sat :
    FGTimingLaws timing ∧ FGObservationLaws core seedObs ∧
    HonestProposal env run interface 2 .genesis ∧
    V2.D.proposerOf run interface 2 = 7 ∧
    FrontierSeedQualification timing 1 env.t_GST 0 2 ∧
    PhaseInterval core env run seedObs 0 (timing.gate 2) 1 (some .genesis) false ∧
    FrontierProposalService core env run timing 2 .genesis ∧
    FrontierLocalServiceFG core reads env run seedObs timing interface Row.height_pair
      2 .genesis .genesis 1 (timing.gate 2) ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    (∀ x ∈ run.honest, actionSourceFG core env run timing x 1 = some (some .genesis)) := by
  obtain ⟨hp, hproposer, _, _, _, _, hqual, hphase, _⟩ := seed_premises_sat
  obtain ⟨_, _, _, _, _, _, _, hrow, hhead, _, hsource, _, _⟩ := service_premises_sat
  refine ⟨?_, ⟨fun _ => rfl, fun _ _ => rfl⟩, hp, hproposer, hqual, ?_, ?_, ?_, hrow,
    hsource⟩
  · constructor <;> first | decide | (intro s; dsimp only [timing] <;> push_cast <;> ring)
  · exact hphase
  · intro _ x hx _
    exact hhead x hx
  · obtain ⟨hhead, hparent, hstable, hlater, hopen⟩ := mixed_service
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H hx hs ht hh
      exact hhead x s H hx hs (ht.trans (by decide)) hh
    · intro s B hs ht hp
      exact hparent s B hs (ht.trans (by decide)) hp
    · intro i x hx ht hi hit
      exact hstable i x hx (ht.trans (by decide)) hi
        (hit.trans (frontierSearch_timeIdx_mono run (by decide)))
    · intro s B hs ht hp
      exact hlater s B hs (ht.trans (by decide)) hp
    · intro r hq ht
      exact hopen r hq (ht.trans (by decide))

#print axioms saved_seed_premises_sat

private theorem mixed_saved_seed_consumer :
    StrongServedFG core reads env run seedObs timing interface Row.height_pair 0 1 1 14 ∧
    V2.D.proposerOf run interface 2 = 7 ∧
    HonestRowAt reads env run timing 0 9 0 row := by
  obtain ⟨ht, ho, hp, hproposer, hqual, hphase, hservice, hlocal, hrow, _⟩ :=
    saved_seed_premises_sat
  refine ⟨?_, hproposer, hrow⟩
  exact frontierSearch_save_seed_holder core reads env run seedObs timing interface
    Row.height_pair 0 1 ho ht le_rfl le_rfl hphase hqual hp rfl rfl hservice le_rfl hlocal

#print axioms mixed_saved_seed_consumer

/-! A schedule-valid refusal fixture. The FG record ignores non-FG signatures.
Holder 9 has its actual FG row; nonholder 7's exact HEAD differs from the selected proposal. -/
private abbrev wrongHead : Block := .node .genesis 1 ⟨99⟩ 0
private abbrev missingProtocol : V2.ProtocolSpecD Unit :=
  { protocol with recordOwn := fun st o => match o.auth with
      | .seat l _ => if l = 6 then record_row_once st o.payload else st
      | .none => st }
private abbrev missingRun : V2.D.Run Nat missingProtocol where
  honest := run.honest
  horizon := 18
  events := (List.range 19).flatMap fun (t : Nat) => [.tick 7 (t : Time), .tick 9 (t : Time)]
  seatOf := run.seatOf
  input := run.input
private abbrev missingCore : FGCoreReads missingProtocol 1 Unit Unit (Row (Fin 1)) where
  core := core.core
  erase := core.erase
  source := core.source
  headVote st _ := if st.sent.isEmpty then wrongHead else .genesis
  finalityHead := core.finalityHead
  proposalFG := core.proposalFG
private abbrev missingObs : FGObservationReads missingCore where
  height := height
  finality := fun _ => ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView height (missingCore.core nd).fg
  viable nd X := treeStoreFrameView height (missingCore.core nd).fg X
private abbrev missingIface : V2.D.Interface missingProtocol where
  confirmed := interface.confirmed
  stable := interface.stable
  block := interface.block
  opening := interface.opening
  propLabel := interface.propLabel
  propDuty := interface.propDuty
  propDuty_label := interface.propDuty_label
  propLabel_single := interface.propLabel_single
  propLabel_injective := interface.propLabel_injective
private abbrev missingReads : FGSafetyReads missingProtocol 1 (Row (Fin 1)) where
  proposalErase := reads.proposalErase
  proposalRows := reads.proposalRows
  encode := reads.encode
  decode := reads.decode
  decodeObject := reads.decodeObject
  fgLabel := reads.fgLabel
  fgSeats := reads.fgSeats
  record := reads.record
  inputs := reads.inputs
  enabled := reads.enabled
  finalizedOut := reads.finalizedOut

private theorem missing_receiver_premises_sat :
    V2.D.ScheduleWellFormed env missingRun ∧ FGTimingLaws timing ∧
    FGObservationLaws missingCore missingObs ∧ missingRun.honest = {7, 9} ∧
    HonestProposal env missingRun missingIface 2 .genesis ∧
    FrontierSeedQualification timing 1 env.t_GST 0 2 ∧
    PhaseInterval missingCore env missingRun missingObs 0 (timing.gate 2) 1
      (some .genesis) false ∧
    FrontierLocalServiceFG missingCore missingReads env missingRun missingObs timing
      missingIface Row.height_pair 2 .genesis .genesis 1 (timing.gate 2) ∧
    HonestRowAt missingReads env missingRun timing 13 9 0 row ∧
    headAtLabel missingCore env missingRun timing 9 2 = some .genesis ∧
    (∀ q : Fin 5, headAtLabel missingCore env missingRun timing 7 q.val = some wrongHead) ∧
    (∀ q, AttemptJoinedAt env missingRun timing 7 q (timing.vote q)) := by
  have hrow : HonestRowAt missingReads env missingRun timing 13 9 0 row := by
    unfold HonestRowAt
    decide +kernel
  have hc : OpeningCoveredFG missingCore missingReads env missingRun height timing Row.height_pair
      (FGHonestSeats missingReads missingRun) 1 .genesis := by
    intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨.genesis, missingRun.stateBefore env 29 9, 13, 0, row,
      rfl, by decide +kernel, by decide, by decide, by decide, hrow, rfl⟩
  refine ⟨?_, saved_seed_premises_sat.1, ⟨fun _ => rfl, fun _ _ => rfl⟩, rfl, ?_, ?_, ?_,
    ?_, hrow, by decide +kernel, by decide +kernel, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      dsimp only [missingRun] at ht
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp ht
      have hk' : (x = 7 ∧ t = (k : Time)) ∨ (x = 9 ∧ t = (k : Time)) := by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          V2.Event.tick.injEq] using hk
      rcases hk' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨k, by simp⟩
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 19 := by change (k : Int) * 1 ≤ 18 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      dsimp only [missingRun, env]
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rcases hx' with rfl | rfl <;> simp
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, row⟩,
      ⟨16, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact Or.inr ⟨0, by decide, fun _ _ => Nat.zero_le _, by decide, by decide, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    change (missingObs.controls RecordOnce.initial).H = 1 ∧ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H _ _ _ hH
      delta headAtLabel at hH
      obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hH
      change (if nd.sent.isEmpty then wrongHead else Block.genesis) = H at he
      rw [← he]
      split <;> decide
    · intro s B _ _ hp
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      decide
    · intro i x _ _ _ _
      change Block.Preceq .genesis .genesis
      decide
    · intro s B hs ht _
      change 8 < 4 * (s : Int) at hs
      change 4 * (s : Int) + 6 ≤ 14 at ht
      omega
    · intro r hqr ht
      change @LE.le Nat _ 2 (r * 2) at hqr
      change 8 * (r : Int) + 6 ≤ 14 at ht
      have hr : @Eq Nat r 1 := by omega
      subst r
      exact ⟨hc, ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩,
        fun _ _ _ _ => rfl, fun _ => by decide⟩
  · intro q
    refine ⟨rfl, ?_, ?_⟩
    · intro u _ _ hw
      have hf : true = false := hw.2
      cases hf
    · intro u _ _ hr
      simp [List.mem_flatMap] at hr

#print axioms missing_receiver_premises_sat

private theorem missing_receiver_service_rejected :
    (¬ FrontierProposalService missingCore env missingRun timing 2 .genesis) ∧
    ∀ t, ¬ StrongServedFG missingCore missingReads env missingRun missingObs timing
      missingIface Row.height_pair 0 1 1 t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heads, joined⟩ := missing_receiver_premises_sat
  have noService (q : Nat) (hq : q < 5) (ht : timing.vote q ≤ missingRun.horizon) :
      ¬ FrontierProposalService missingCore env missingRun timing q .genesis := by
    intro hs
    have hh := hs ht 7 (by decide) (joined q)
    have hw : headAtLabel missingCore env missingRun timing 7 q = some wrongHead :=
      heads ⟨q, hq⟩
    rw [hw] at hh
    cases hh
  refine ⟨noService 2 (by decide) (by decide), ?_⟩
  intro t hs
  obtain ⟨u, J, c, q, Q, Qfg, _, hp, _, _, hsvc, _, _, _, hg, hh, _⟩ := hs
  obtain ⟨_, o, _, hb⟩ := hp
  have hQ : Q = .genesis := (Option.some.inj hb).symm
  subst Q
  have hgate := hg.trans hh
  change 4 * (q : Int) + 6 ≤ 18 at hgate
  have hq : @LT.lt Nat _ q 5 := by omega
  have hvote : timing.vote q ≤ missingRun.horizon := by
    change 4 * (q : Int) + 1 ≤ 18
    omega
  exact noService q hq hvote hsvc

#print axioms missing_receiver_service_rejected

end AvailableChain.FGCompose.Tests.PopulationSearchSeed
end
