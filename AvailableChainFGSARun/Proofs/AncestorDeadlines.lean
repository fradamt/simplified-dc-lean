module
public import AvailableChainFGSARun.Proofs.AncestorDeadlinesStore
public import AvailableChainFGSARun.Proofs.Protocol

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In : Type} {c : AppCodec In}

/-- [helper] The own-record step keeps the store by `recordOwn_st`. -/
theorem ancestorDeadlines_recordOwn (nd : Node p) (o : Obj p)
    (h : AncestorDeadlines nd.st) :
    AncestorDeadlines (((fgsa p c).recordOwn nd o).st) := by
  rw [recordOwn_st]
  exact h

/-- [helper] Restore clears the obligations and retains the clock. -/
theorem ancestorDeadlines_restore (d : Time × SimplexFG.RecordOnce) :
    AncestorDeadlines (((fgsa p c).restore d).st) := by
  exact ancestorDeadlines_initialAt p.n d.1

end AvailableChain.FGSA.Run
end
