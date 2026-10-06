module
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainPCSAProofs.Proofs.Shared.RetainedWalk

public section

/-! Formation step 1 boundaries (pcsa34-r4.3a §5.3).
BLOCKED: F4 does not imply the retained target_prefix (BestAncestry).
Tests.FormationCounterexample checks a valid finite slot-4 run with F1–F7:
a proposer lock selects parent(P), then release at v_s removes that lock.
The parent path is ineligible at every voter, so HEAD is a rival of P.
F3 gives equal PC targets, not eligibility on the path to the proposer root.
The missing fact is BestAncestry from the voter root to the retained cut.
FG-SA Clean.Transfer cannot supply that fact for arbitrary prehistory. -/

namespace AvailableChain.PCSA

/-- F4 bounds the live root using only the locks selected by the walk. -/
theorem pcsa_formation_root_below_parent (p : Params) (st : State p.n)
    (v : Option (PC p.n)) (P : Block)
    (hStart : Block.Preceq (walkBase p st v) P.parent)
    (hLocks : ∀ B, LiveLease st B → Block.Compatible B (walkBase p st v) →
      (walkBase p st v).depth < B.depth → Block.Preceq B P.parent) :
    Block.Preceq (liveRoot p st v) P.parent := by
  rcases pcsa_liveRoot_origin p st v with he | hm
  · exact he ▸ hStart
  · obtain ⟨row, hr, he, ht, _, hc, hd, _⟩ :=
      (pcsa_walkLocks_mem p st v _).mp hm
    exact hLocks _ ⟨row, hr, he, ht⟩ hc hd

/-- The current-slot child is eligible even without majority support. -/
theorem pcsa_formation_current_eligible (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root)) (P : Block)
    (hSlot : P.slot = st.slot p) : eligible p st raw support P = true := by
  change (_ || _ || (P.slot == st.slot p)) = true
  rw [hSlot, BEq.rfl, Bool.or_true]

/-- The exact terminal path fixes the executable voter HEAD. -/
theorem pcsa_formation_headVote_exact (p : Params) (st : State p.n) (s : Slot)
    (P : Block) (hs : s ≠ 0)
    (hRoot : Block.Preceq (liveRoot p st (voterPC p st s)) P)
    (hPath : Gen.Pure.DominatedSuffix (liveRoot p st (voterPC p st s)) P
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
      (GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s))
      (eligible p st (headVotes p st s) (headSupport p st s)))
    (hStop : Gen.Pure.NoEligibleChild
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
      (eligible p st (headVotes p st s) (headSupport p st s)) P) :
    headVote p st s = P := by
  change (if s = 0 then Block.genesis else _) = P
  rw [ite_eq_right hs]
  exact pcsa_headInTree_exact_path p st _ _ _ _ P hRoot hPath hStop

end AvailableChain.PCSA
end
