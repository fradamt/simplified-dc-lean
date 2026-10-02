module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainKitFG.FrameBridge

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The active controls equal the old store controls through LF7. -/
theorem controls_eq (p : Params) (st : State p.n) :
    controls p st = storeControls p.E p.cfg st.fg :=
  (storeControls_of_bridge p.E p.cfg (heightView p) (fun _ => rfl) st.fg).symm

/-- The active full tree equals the old store frame through LF7. -/
theorem fullTree_eq (p : Params) (st : State p.n) :
    fullTree p st = storeFrame p.E p.cfg st.fg st.fg.TF :=
  (storeFrame_of_bridge p.E p.cfg (heightView p) (fun _ => rfl) st.fg st.fg.TF).symm

/-- The height view preserves the old eligibility test. -/
theorem fgsa_eligible_eq (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n)) (b : Block) :
    eligible p st raw support b =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧
        hOf p.E p.cfg P < (controls p st).lo) ||
      decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
      b.slot == st.slot p) := by
  unfold eligible
  simp only [hOf_of_bridge p.E p.cfg (heightView p) (fun _ => rfl)]

/-- The voter frame equals the old store frame through LF7. -/
theorem headVote_eq (p : Params) (st : State p.n) (s : Slot) :
    headVote p st s =
      (if s = 0 then .genesis else
        headInTree p st (erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)))
          (headVotes p st s) (headSupport p st s)) := by
  unfold headVote
  rw [← storeFrame_of_bridge p.E p.cfg (heightView p) (fun _ => rfl)]

end AvailableChain.FGSA
end
