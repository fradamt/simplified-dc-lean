module
public import AvailableChainFGSARun.Proofs.Acceptance
public import AvailableChainFGSARun.Tests.Protocol

public section

namespace AvailableChain.FGSA.Run.Tests

open AvailableChain.SimplexFG

private def t77Rows : List (RowWire 1) :=
  [⟨.seat (.fg 0) 0, ⟨.empty, none⟩⟩,
   ⟨.seat (.fg 0) 0, ⟨.vote 1 genesisRoot false, none⟩⟩,
   ⟨.seat (.fg 0) 0, ⟨.vote 2 genesisRoot false, none⟩⟩]

private def t77Envelope : Obj p1 :=
  propObj 1 (.proposal (.node .genesis 1 (packBody 0 t77Rows)) [] [] t77Rows)

private def t77Third : Obj p1 :=
  baseObj (.fg 0) (.row ⟨.vote 2 genesisRoot false, none⟩)

private def t77Pre : Node p1 := P1.clock P1.init 4

/-- The third row is ready at the pre-state. The cap reached inside the
proposal delivery excludes it at the post-state. -/
theorem fgsa_carried_row_cap_control :
    let rows : List (RowWire 1) :=
      [⟨.seat (.fg 0) 0, ⟨.empty, none⟩⟩,
       ⟨.seat (.fg 0) 0, ⟨.vote 1 genesisRoot false, none⟩⟩,
       ⟨.seat (.fg 0) 0, ⟨.vote 2 genesisRoot false, none⟩⟩]
    let envelope := propObj 1 (.proposal (.node .genesis 1 (packBody 0 rows)) [] [] rows)
    let third := baseObj (.fg 0) (.row ⟨.vote 2 genesisRoot false, none⟩)
    let pre := P1.clock P1.init 4
    P1.wellFormed envelope = true ∧
      P1.excludes pre third = false ∧
      P1.processed (P1.process pre envelope) third = false ∧
      P1.excludes (P1.process pre envelope) third = true := by
  decide +kernel

/-- The capped third row is still a handled child. -/
example : P1.handles t77Pre t77Envelope t77Third := by
  change handlesS p1 t77Pre.st t77Envelope t77Third
  right
  change (∃ P, parentFG t77Pre.st _ = some P ∧
    blockAccepted p1 t77Pre.st 1 _ P t77Rows = true) ∧
      (t77Third ∈ [].map (ofHead p1) ∨ t77Third ∈ t77Rows.map (ofRow p1))
  constructor
  · exact ⟨.genesis, by decide +kernel, by decide +kernel⟩
  · right
    decide +kernel

/-- A slot-zero HEAD can be admitted before the honest vote time of 1. Its
admission threshold is zero. -/
example :
    P1.processed (P1.process P1.init (baseObj (.head 0) (.head .genesis)))
      (baseObj (.head 0) (.head .genesis)) = true ∧
    fgsaTimely p1 P1.init (baseObj (.head 0) (.head .genesis)) := by
  unfold fgsaTimely
  decide +kernel

/-- A negative store clock shows why AdmitSound requires a nonnegative clock. -/
example :
    let nd : Node p1 := ⟨{ initial 1 with base.now := -1 }, Record.initial⟩
    P1.processed (P1.process nd (baseObj (.head 0) (.head .genesis)))
      (baseObj (.head 0) (.head .genesis)) = true ∧
    ¬ fgsaTimely p1 nd (baseObj (.head 0) (.head .genesis)) := by
  unfold fgsaTimely
  decide +kernel

end AvailableChain.FGSA.Run.Tests
end
