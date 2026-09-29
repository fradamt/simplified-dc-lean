module
public import AvailableChainFGSA.Model.Handlers

@[expose] public section

namespace AvailableChain.FGSA.Tests

open AvailableChain.SimplexFG

/-! Test support: a proved rewrite of a proposal delivery with an explicit FG
block, for fixtures whose `decide +kernel` checks would otherwise reduce
`fgBlock` again at each use. -/

/-- [test helper] The accepted branch of `admitBlock`, with an explicit FG block
`B` in place of `fgBlock P b rows`. The kernel reduces `fgBlock P b rows` again
at each use, and each reduction decodes the body (`appOf`). On a large store
this makes a `decide +kernel` check too slow, so such a test first rewrites
with `process_eq_admitWith` (for the `B` with `fgBlock P b rows = B`). -/
def admitWith (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (P B : FGBlock (Fin p.n)) : State p.n :=
  if blockAccepted p st s b P rows then
    let st1 : State p.n := { st with
      base := GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s b raw support) b (raw.map baseHead)
      fg := on_block p.E p.cfg st.fg B
      proposals := st.proposals ++ [⟨.proposer s, .proposal b raw support rows⟩] }
    let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
    rows.foldl (admitRow p) st2
  else st

/-- [test helper] A proposal delivery, with its FG parent `P` and its FG block
`B` explicit. -/
theorem process_eq_admitWith (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (P B : FGBlock (Fin p.n)) (hP : parentFG st b = some P) (hB : fgBlock P b rows = B) :
    process p st ⟨.proposer s, .proposal b raw support rows⟩ =
      admitWith p st s b raw support rows P B := by
  subst hB
  change admitBlock p st s b raw support rows = _
  unfold admitBlock
  rw [hP]
  rfl

end AvailableChain.FGSA.Tests
end
