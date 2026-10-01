module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainGeneric.Proofs.AC.Support
public import AvailableChainGeneric.Proofs.Pure.Walk

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
open Gen.Pure

/-- P3 F2.3, F1b.4; bp02 §4.2. Class (iii), FG-SA store instance.
DC: Goldfish/Adoption.lean:415–435,441–461. INTENTIONAL: liveRoot and
FJ eligibility replace the SG anchor and eligibility (spec:2519–2525,
2557–2565). Only the stored suffix is required; strict sibling dominance
and majority instantiate the generic walk without a run premise. -/
theorem fgsa_headVote_covers_of_transfer
    (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hpath : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      C ∈ erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st (s + 1))))
    (hmajority : GridCO.voterCount (headVotes p st (s + 1)) <
      2 * GridCO.goldfishScore st.base.blocks
        (headVotes p st (s + 1)) (headSupport p st (s + 1)) B)
    (hdominance : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks
        (headVotes p st (s + 1)) (headSupport p st (s + 1)) D <
      GridCO.goldfishScore st.base.blocks
        (headVotes p st (s + 1)) (headSupport p st (s + 1)) B) :
    Block.Preceq B (headVote p st (s + 1)) := by
  change Block.Preceq B (if s + 1 = 0 then _ else _)
  rw [ite_eq_right (Nat.succ_ne_zero s)]
  apply walk_covers_of_dominated_suffix _ _ _ _ _ hanchor
  rw [DominatedSuffix_def]
  intro C hac hcb
  have hm := Gen.AC.goldfishScore_antitone st.base.blocks
    (headVotes p st (s + 1)) (headSupport p st (s + 1)) C B hcb
  refine ⟨hpath C hac hcb, ?_, ?_⟩
  · change (_ || decide (_ < 2 * _) || _) = true
    have hmaj : GridCO.voterCount (headVotes p st (s + 1)) <
        2 * GridCO.goldfishScore st.base.blocks
          (headVotes p st (s + 1)) (headSupport p st (s + 1)) C := by omega
    simp only [hmaj, decide_true, Bool.or_true, Bool.true_or]
  · intro D _ hp _ hne
    have he : D.depth = C.depth := by
      cases D with
      | genesis => cases C with
        | genesis => rfl
        | node P s id => cases hp
      | node P s id => cases C with
        | genesis => cases hp
        | node Q t jd =>
          have heq : P = Q := Option.some.inj hp
          subst Q
          rfl
    have hn : ¬ Block.Compatible D C := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hne (prefix_eq_of_depth D C h (Nat.le_of_eq he.symm))
      · exact hne (prefix_eq_of_depth C D h (Nat.le_of_eq he)).symm
    have hd : Block.compatible B D = false := by
      rw [block_compatible_comm]
      exact Bool.eq_false_iff.mpr (block_incompatible_of_preceq hn hcb)
    exact lt_of_lt_of_le (hdominance D hd) hm

end AvailableChain.FGSA
end
