module
public import AvailableChainFGSA.Model.Spec.ACState

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-- [spec 1101–1104] Expire lock entries before any scheduled AC duty. -/
def expire (A : ACState n) (t : Time) : ACState n :=
  { A with locks := A.locks.filter (fun e => decide (t < e.2)) }

/-- [spec 1274–1283] `advance`: keep an in-tree record on an ancestor candidate. -/
def advance (tree : List AvailableChain.Block) (old : AvailableChain.Block)
    (candidate : Option AvailableChain.Block) : AvailableChain.Block :=
  match candidate with
  | none => old
  | some C => if old ∈ tree && AvailableChain.Block.preceq C old then old else C

/-- [spec 544–546] Append a new attestation once, in first-acceptance order.
Authentication and row validity are checked before this spec function. -/
def insertRow {n : Nat} (pool : List (RowWire n)) (a : RowWire n) : List (RowWire n) :=
  if a ∈ pool then pool else pool ++ [a]

/-- [spec 412–418, 527–541] Pure refusal shell. A failed FG step performs no AC step.
The supplied FG function must itself compute without writes on refusal. -/
def onBlock {σ α : Type} (future : Bool) (fg : σ → Option σ) (ac : α → α)
    (state : σ × α) : σ × α :=
  if future then state else
    match fg state.1 with
    | none => state
    | some next => (next, ac state.2)

/-- [spec 221–231, 370–375, 400–409] Pure tick order with scheduled steps as parameters.
Each step sees the previous step's result; no execution or delivery claim is made. -/
def tick {σ : Type} (setClock ac proposal attest : σ → σ) (state : σ) : σ :=
  attest (proposal (ac (setClock state)))

/-- [spec 924–945] Slot start, extended to integer slots for negative empty pools. -/
def slotTime (Δ : Time) (s : Int) : Time := 4 * Δ * s

/-- [spec 930–935] A scheduled phase at an offset from a slot start. -/
def phaseTime (Δ : Time) (s : Int) (offset : Int) : Time := slotTime Δ s + offset * Δ

-- Generate equations in their owning model module (BUILD B3a).
private theorem expire_eq_1_export :
    type_of% (@expire.eq_1) := @expire.eq_1
private theorem advance_eq_1_export :
    type_of% (@advance.eq_1) := @advance.eq_1
private theorem insertRow_eq_1_export :
    type_of% (@insertRow.eq_1) := @insertRow.eq_1
private theorem onBlock_eq_1_export :
    type_of% (@onBlock.eq_1) := @onBlock.eq_1
private theorem tick_eq_1_export :
    type_of% (@tick.eq_1) := @tick.eq_1
private theorem slotTime_eq_1_export :
    type_of% (@slotTime.eq_1) := @slotTime.eq_1
private theorem phaseTime_eq_1_export :
    type_of% (@phaseTime.eq_1) := @phaseTime.eq_1

end AvailableChain.FGSA.Spec
end
