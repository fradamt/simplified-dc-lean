module
public import AvailableChainFGSA.Proofs.Port.VoteMerge
public import AvailableChainFGSA.Tests.Smoke

public section

namespace AvailableChain.FGSA.Next.MergeTests

open AvailableChain.SimplexFG

/-- Slot zero has the same genesis head for every parameter set. -/
theorem initial_head (p : Params) : headVoteNext p (initial p.n) 0 = .genesis := rfl

private abbrev p := Tests.pT
private def first : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 []
private def final : FGBlock (Fin 4) := .node first 2 ⟨101⟩ 0 []
private def above : FGBlock (Fin 4) := .node final 3 ⟨102⟩ 0 []
private def fork : FGBlock (Fin 4) := .node .genesis 3 ⟨103⟩ 0 []
private def proposal : FGBlock (Fin 4) := .node above 4 ⟨104⟩ 0 []
private def offProposal : FGBlock (Fin 4) := .node fork 4 ⟨105⟩ 0 []
private def future : FGBlock (Fin 4) := .node final 4 ⟨106⟩ 0 []
private def vote (i : Fin 4) (s : Slot) (r : BlockId) : HeadWire 4 :=
  ⟨.seat (.head s) i, r⟩
private def a := vote 0 3 above.root
private def b := vote 1 3 first.root
private def c := vote 0 3 fork.root
private def d := vote 2 3 ⟨999⟩
private def e := vote 3 3 future.root
private def wrong := vote 3 2 above.root
private def raw := [a, b, c, a, d, e, wrong]
private def support := [b, a, c, d, e, a, wrong]
private def carried (B : FGBlock (Fin 4)) (rs ss : List (HeadWire 4)) : Wire 4 :=
  ⟨.proposer B.slot,
    .proposal (Tests.namedBody (Tests.namedFixture B.parent) (eraseFG B) rs ss [])⟩

/-- Pure reader fixtures. These stores need no admission or execution premise. -/
private def st : State 4 :=
  { base := { GridCO.initial 4 .root with
      now := 17
      blocks := [.genesis, eraseFG first, eraseFG final, eraseFG above, eraseFG fork,
        eraseFG proposal, eraseFG offProposal, eraseFG future]
      votes := [baseVote d, baseVote a]
      voteStamp := [(baseVote d, 14), (baseVote a, 14)]
      blockStamp := [(eraseFG above, 15), (eraseFG fork, 15),
        (eraseFG proposal, 15), (eraseFG offProposal, 15), (eraseFG future, 15)] }
    fg := { Store.init with
      TF := {.genesis, first, final, above, fork, proposal, offProposal, future}, F := final }
    proposals := [carried offProposal [b] [b], carried proposal raw support,
      carried proposal [c, b] [a], carried above [e] [e]] }

/-- Only slot-4 proposals in the accepted tree supply lists; order is unchanged. -/
example : proposalsAtNext p st 4 = [(raw, support), ([c, b], [a])] ∧
    proposalsAt st 4 = [([b], [b]), (raw, support), ([c, b], [a])] := by decide +kernel

/-- Raw participation includes unresolved, off-F, ancestor, and future heads.
Frozen votes precede carried votes; the first occurrence wins deduplication. -/
example : headVotesNext p st 4 = [baseVote d, baseVote a, baseVote b, baseVote c, baseVote e] ∧
    GridCO.voterCount (headVotesNext p st 4) = 4 ∧
    GridCO.equivocates (headVotesNext p st 4) 0 = true := by decide +kernel

/-- Carried support excludes ancestor, conflicting, unresolved, and future heads.
The retained head passes through its proposal even at the strict freeze boundary. -/
example : GridCO.resolvedHead? st.base (baseVote b) = some (eraseFG first) ∧
    GridCO.resolvedHead? st.base (baseVote c) = some (eraseFG fork) ∧
    headSupportNext p st 4 = [baseVote a] ∧
    GridCO.goldfishScore st.base.blocks (headVotesNext p st 4)
      (headSupportNext p st 4) (eraseFG fork) = 1 := by decide +kernel

/-- Only retained proposal ancestors enter the late voter arm. Off-F blocks
stay out even with a current-slot proposal. Early ancestors below F stay out too. -/
example : above ∈ voterBlocksNext p st 4 ∧ proposal ∈ voterBlocksNext p st 4 ∧
    first ∉ voterBlocksNext p st 4 ∧ fork ∉ voterBlocksNext p st 4 ∧
    offProposal ∉ voterBlocksNext p st 4 ∧ fork ∈ voterBlocks p st 4 := by decide +kernel

private def ordered : State 4 :=
  { st with
    base := { st.base with votes := [] }
    proposals := [carried proposal [vote 1 3 final.root, a, vote 1 3 final.root, a]
      [vote 1 3 final.root, a, vote 1 3 final.root, a]] }

/-- Distinct retained support heads keep their first-occurrence order too. -/
example : headVotesNext p ordered 4 = [baseVote (vote 1 3 final.root), baseVote a] ∧
    headSupportNext p ordered 4 = [baseVote (vote 1 3 final.root), baseVote a] := by
  decide +kernel

private def frozen : State 4 :=
  { st with proposals := [], base := { st.base with
      votes := [baseVote b, baseVote a]
      voteStamp := [(baseVote b, 14), (baseVote a, 15)]
      blockStamp := [(eraseFG first, 14), (eraseFG above, 14)] } }

/-- The minimal change keeps frozen ancestor support. A vote stamped exactly
at the freeze is absent from both frozen arms. -/
example : headVotesNext p frozen 4 = [baseVote b] ∧
    headSupportNext p frozen 4 = [baseVote b] ∧
    headSupportNext p frozen 4 = Legacy.headSupport p frozen 4 := by decide +kernel

private def collision : FGBlock (Fin 4) := .node final 3 first.root 0 []
private def ambiguous : State 4 :=
  { st with
    base := { st.base with blocks := st.base.blocks ++ [eraseFG collision], votes := [] }
    fg := { st.fg with TF := insert collision st.fg.TF }
    proposals := [carried proposal [b] [b]] }

/-- The retained collision cannot repair an ambiguous cumulative root. -/
example : GridCO.resolvedHead? ambiguous.base (baseVote b) = none ∧
    headVotesNext p ambiguous 4 = [baseVote b] ∧
    headSupportNext p ambiguous 4 = [] ∧
    Block.findByRoot? (erasedList ambiguous (tree p ambiguous)) first.root =
      some (eraseFG collision) := by decide +kernel

/-- Preserve the old admitted-state regression through the complete legacy chain. -/
example : Legacy.headSupport p Tests.stXs 3 = [baseVote Tests.vX] ∧
    headSupportNext p Tests.stXs 3 = [] ∧ headVotesNext p Tests.stXs 3 = [] := by
  decide +kernel

private def contest : State 4 :=
  { Tests.stK with
    fg := { Tests.stK.fg with F := Tests.B1a }
    base := { Tests.stK.base with
      votes := [baseVote (vote 0 3 Tests.B1a.root), baseVote (vote 0 3 Tests.Y.root)]
      voteStamp := [(baseVote (vote 0 3 Tests.B1a.root), 14),
        (baseVote (vote 0 3 Tests.Y.root), 14)] } }

/-- The late off-F top block contests only the legacy frame. The guarded
controls also reach the voter walk, which can now select the lower-band X. -/
example : (Legacy.controls p contest).contest = true ∧
    (controls p contest).contest = false ∧
    (controls p contest).H = (Legacy.controls p contest).H ∧
    (controls p contest).J = (Legacy.controls p contest).J ∧
    headVoteNext p contest 4 = eraseFG Tests.X ∧
    Legacy.headVote p contest 4 = eraseFG Tests.childA := by decide +kernel

/-- The slot-zero guard is preserved. -/
example : headVoteNext p st 0 = .genesis ∧ proposeNext p st 0 = none := by decide

end AvailableChain.FGSA.Next.MergeTests
end
