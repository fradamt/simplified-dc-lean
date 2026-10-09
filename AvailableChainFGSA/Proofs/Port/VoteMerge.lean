module
public import AvailableChainFGSA.Model.FrameNext
public import AvailableChainFGSA.Model.Legacy.Frame
public import AvailableChainFGSA.Proofs.Port.ContestFrame
public import AvailableChainFGSA.Proofs.Port.Tree

public section

namespace AvailableChain.FGSA.Legacy

/-! Before SWITCH, each complete legacy reader is definitionally equal to its
canonical reader. All dependencies declared by Frame are copied into Legacy. -/

theorem controls_eq : @controls = @FGSA.controls := rfl

theorem fullTree_eq : @fullTree = @FGSA.fullTree := rfl

theorem erasedList_eq : @erasedList = @FGSA.erasedList := rfl

theorem liveRoot_eq : @liveRoot = @FGSA.liveRoot := rfl

theorem eligible_eq : @eligible = @FGSA.eligible := rfl

theorem headInTree_eq : @headInTree = @FGSA.headInTree := rfl

theorem getHead_eq : @getHead = @FGSA.getHead := rfl

theorem proposalsAt_eq : @proposalsAt = @FGSA.proposalsAt := rfl

theorem voterBlocks_eq : @voterBlocks = @FGSA.voterBlocks := rfl

theorem headVotes_eq : @headVotes = @FGSA.headVotes := rfl

theorem headSupport_eq : @headSupport = @FGSA.headSupport := rfl

theorem headVote_eq : @headVote = @FGSA.headVote := rfl

theorem proposerVotes_eq : @proposerVotes = @FGSA.proposerVotes := rfl

theorem proposerSupport_eq : @proposerSupport = @FGSA.proposerSupport := rfl

theorem chainWireRows_eq : @chainWireRows = @FGSA.chainWireRows := rfl

theorem blockWireRows_eq : @blockWireRows = @FGSA.blockWireRows := rfl

theorem proposalRows_eq : @proposalRows = @FGSA.proposalRows := rfl

theorem propose_eq : @propose = @FGSA.propose := rfl

theorem fgHead_eq : @fgHead = @FGSA.fgHead := rfl

theorem fgBlockOf_eq : @fgBlockOf = @FGSA.fgBlockOf := rfl

theorem deepest_eq : @deepest = @FGSA.deepest := rfl

theorem fgSource_eq : @fgSource = @FGSA.fgSource := rfl

theorem fgInputs_eq : @fgInputs = @FGSA.fgInputs := rfl

theorem attest_eq : @attest = @FGSA.attest := rfl

end AvailableChain.FGSA.Legacy

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- Pure comparison: every selected proposal is still held above F. -/
theorem proposalsAtNext_eq_of_retained (p : Params) (st : State p.n) (s : Slot)
    (hP : ∀ o ∈ st.proposals, ∀ r N, o.decode = some (.block r N) → N.slot = s →
      ∃ B ∈ tree p st, eraseFG B = N.erase) :
    proposalsAtNext p st s = proposalsAt st s := by
  unfold proposalsAtNext proposalsAt
  apply List.filterMap_congr
  intro o ho
  cases hd : o.decode with
  | none => rfl
  | some d =>
      cases d with
      | block r N =>
          by_cases hs : N.slot = s
          · simp [hs, hP o ho r N hd hs]
          · simp [hs]
      | vote r i h => rfl
      | row i r => rfl

/-- Raw merge equality only needs equality of the retained proposal lists. -/
theorem headVotesNext_eq_of_proposals (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s) :
    headVotesNext p st s = headVotes p st s := by
  delta headVotesNext headVotes
  rw [hP]

/-- The new voter view agrees when every held block extends F. -/
theorem voterBlocksNext_eq_of_tree (p : Params) (st : State p.n) (s : Slot)
    (hT : tree p st = st.fg.TF) : voterBlocksNext p st s = voterBlocks p st s := by
  delta voterBlocksNext voterBlocks
  rw [hT]

/-- Pure support comparison. Only carried heads with the correct label and
slot need retention. There is no new condition on the frozen arm. -/
theorem headSupportNext_eq_of_retained (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s)
    (hH : ∀ o ∈ (proposalsAt st s).flatMap (fun row => row.2.map baseVote),
      GridCO.headLabel? o = some (s - 1) → ∀ h,
      GridCO.resolvedHead? st.base o = some h → h.slot ≤ s - 1 →
      ∃ B ∈ tree p st, eraseFG B = h) :
    headSupportNext p st s = headSupport p st s := by
  delta headSupportNext headSupport
  rw [hP]
  dsimp only
  apply congrArg List.eraseDups
  apply congrArg (List.append _)
  apply List.filter_congr
  intro o ho
  by_cases hl : GridCO.headLabel? o = some (s - 1)
  · cases hr : GridCO.resolvedHead? st.base o with
    | none => rfl
    | some h =>
        change (GridCO.headLabel? o == some (s - 1) &&
            (decide (∃ B ∈ tree p st, eraseFG B = h) && decide (h.slot ≤ s - 1))) =
          (GridCO.headLabel? o == some (s - 1) && decide (h.slot ≤ s - 1))
        by_cases hs : h.slot ≤ s - 1
        · simp [hl, hs, hH o ho hl h hr hs]
        · simp [hs]
  · have hb : (GridCO.headLabel? o == some (s - 1)) = false := by
      exact beq_eq_false_iff_ne.mpr hl
    rw [hb, Bool.false_and, Bool.false_and]

/-- The tree condition can be supplied by a pure prefix fact on held blocks. -/
theorem tree_eq_of_all_extends (p : Params) (st : State p.n)
    (hF : ∀ B ∈ st.fg.TF, FGBlock.Preceq st.fg.F B) : tree p st = st.fg.TF := by
  apply Finset.filter_eq_self.mpr
  exact hF

/-- Once the live controls agree, the full viable trees agree as well. -/
theorem fullTree_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : fullTree p st = FGSA.fullTree p st := by
  unfold fullTree FGSA.fullTree KitFG.treeStoreFrameView KitFG.storeFrameView
  change KitFG.filteredFromView (heightView p) (controls p st) st.fg.TF = _
  rw [hc]
  rfl

/-- Live leases are selected by the copied fold over the guarded full tree. -/
theorem liveRootNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : liveRootNext p st = liveRoot p st := by
  delta liveRootNext liveRoot
  rw [fullTree_eq_of_controls p st hc, hc]

/-- Eligibility keeps the cumulative parent heights and uses the new floor. -/
theorem eligibleNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : eligibleNext p st = eligible p st := by
  funext raw support b
  delta eligibleNext eligible
  rw [hc]

theorem headInTreeNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : headInTreeNext p st = headInTree p st := by
  funext T raw support
  delta headInTreeNext headInTree
  rw [liveRootNext_eq_of_controls p st hc,
    eligibleNext_eq_of_controls p st hc]

theorem getHeadNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : getHeadNext p st = getHead p st := by
  funext raw support
  delta getHeadNext getHead
  rw [fullTree_eq_of_controls p st hc, erasedList_eq,
    headInTreeNext_eq_of_controls p st hc]

/-- The guarded voter walk agrees when controls, the voter tree, and both
merges agree. The preceding lemmas give pure retention conditions for them. -/
theorem headVoteNext_eq_of_reads (p : Params) (st : State p.n) (s : Slot)
    (hc : controls p st = FGSA.controls p st)
    (hT : voterBlocksNext p st s = voterBlocks p st s)
    (hV : headVotesNext p st s = headVotes p st s)
    (hS : headSupportNext p st s = headSupport p st s) :
    headVoteNext p st s = headVote p st s := by
  have hf : KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocks p st s) =
      KitFG.storeFrameView (heightView p) st.fg (voterBlocks p st s) := by
    unfold KitFG.treeStoreFrameView KitFG.storeFrameView
    change KitFG.filteredFromView (heightView p) (controls p st) _ = _
    rw [hc]
    rfl
  delta headVoteNext headVote
  rw [hT, hV, hS, hf, erasedList_eq,
    headInTreeNext_eq_of_controls p st hc]

end AvailableChain.FGSA.Next
end
