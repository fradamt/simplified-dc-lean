module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainKitFG.FrameBridge
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainGeneric.Proofs.Pure.Fold
public import AvailableChainFGSA.Proofs.WindowHeightBridge

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
One bridge supplies all active height readers. -/
theorem heightView_bridge (p : Params) : HeightBridge p.E p.cfg (heightView p) :=
  Window.windowHeightBridge p p.K_W p.kWLarge

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The active controls equal the old store controls through LF7. -/
theorem controls_eq (p : Params) (st : State p.n) :
    controls p st = storeControls p.E p.cfg st.fg :=
  (storeControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) st.fg).symm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The active full tree equals the old store frame through LF7. -/
theorem fullTree_eq (p : Params) (st : State p.n) :
    fullTree p st = storeFrame p.E p.cfg st.fg st.fg.TF :=
  (storeFrame_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) st.fg st.fg.TF).symm

/-- [ROOT-DIGEST-2 W1; DC root HEAD] The height view preserves the old eligibility test. -/
theorem fgsa_eligible_eq (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root)) (b : Block) :
    eligible p st raw support b =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧
        hOf p.E p.cfg P < (controls p st).lo) ||
      decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
      b.slot == st.slot p) := by
  unfold eligible
  simp only [hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The voter frame equals the old store frame through LF7. -/
theorem headVote_eq (p : Params) (st : State p.n) (s : Slot) :
    headVote p st s =
      (if s = 0 then .genesis else
        headInTree p st (erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)))
          (headVotes p st s) (headSupport p st s)) := by
  unfold headVote
  rw [← storeFrame_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The live-root selector returns a descendant of the active root. -/
theorem fgsa_Z_preceq_liveRoot (p : Params) (st : State p.n) :
    Block.Preceq (eraseFG (controls p st).Z) (liveRoot p st) := by
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · rw [he]
    exact block_preceq_refl _
  · obtain ⟨entry, -, hr⟩ := List.mem_filterMap.1 hm
    split at hr
    · next hc =>
      obtain ⟨B, hB, he⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
      rw [← Option.some.inj hr, ← he]
      exact eraseFG_preceq
        ((KitFG.mem_filteredFromView (heightView p) (controls p st) st.fg.TF B).mp hB).2.2.1
    · cases hr

end AvailableChain.FGSA
end
