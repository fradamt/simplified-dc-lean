module
public import AvailableChainFGSA.Model.Frame

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [R7] All signed rows of admitted proposals, in stored order. -/
def allBlockRows {n : Nat} (st : State n) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ _ _ _ rows) => some rows
    | _ => none)).flatten

/-- [R3; migration 05] The payload sum before its wire activation. -/
inductive RowPayload where
  | vote (body : RowBody)
  deriving DecidableEq, Repr

/-- The height pair of the vote payload. -/
def RowPayload.height_pair : RowPayload → NamedHeightPair
  | .vote body => body.height_pair

/-- The finality pair of the vote payload. -/
def RowPayload.finality_pair : RowPayload → Option FinalityPair
  | .vote body => body.finality_pair

/-- Delegate to the body check. Migration 06 changes that check. -/
def RowPayload.valid : RowPayload → Bool
  | .vote body => body.valid

/-- Decode the payload with the supplied signing identity. -/
def RowPayload.toRow {V : Type} (a : RowPayload) (i : V) : Row V :=
  ⟨i, a.height_pair, a.finality_pair⟩

/-- The vote tag and the complete body code. The active wire codec is unchanged. -/
def encRowPayload : RowPayload → Nat
  | .vote body => epair 0 (encRowBody body)

end AvailableChain.FGSA
end
