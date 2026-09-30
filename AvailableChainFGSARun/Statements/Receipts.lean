module
public import AvailableChainFGSARun.Model.Protocol

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- The decoded block of a proposal object (plan T7.8). -/
def blockOf? (p : Params) (o : Obj p) : Option Block :=
  match (toWire p o).decode with
  | some (.block _ b _ _ _) => some b
  | _ => none

end AvailableChain.FGSA.Run
end
