module
public import AvailableChainPCSA.Model.Store

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The PC operations of the store (pcsa-decisions 3n/4; SAPC
`Model/Certificates.lean` templates). A PC enters the store only by assembly
from the ack pool: a received PC wire and a carried PC contribute their acks.
The ack trigger is the one function `ackTarget?`; a second, more general
trigger is a later addition beside it. -/

variable {n : Nat}

/-- [PC-SA M1; SAPC pcValid] A PC the store accepts: well formed, with a
target in the cumulative tree (path known) and in `act(Σ)`. -/
def pcValid (st : State n) (c : PC n) : Bool :=
  c.wellFormed && decide (c.target ∈ st.base.blocks) && activeCompatible st c.target

/-- [PC-SA M1; SAPC installPC] Install a PC: replace the held PC of its slot
when the new one ranks higher (keep the held one on a tie); else append. -/
def installPC (st : State n) (c : PC n) : State n :=
  if st.pcs.any (fun o => o.slot == c.slot) then
    { st with pcs := st.pcs.map (fun o =>
        if o.slot == c.slot then (preferPC (some o) c).getD o else o) }
  else { st with pcs := st.pcs ++ [c] }

/-- [PC-SA M1; SAPC firstPerSeat] Scan in receipt order; retain the first ack
of each seat. -/
def firstPerSeat (acks : List (AckWire n)) : List (AckWire n) :=
  acks.foldl (fun acc a =>
    if acc.any (fun old => old.seat? == a.seat?) then acc else acc ++ [a]) []

/-- [PC-SA M1] The pooled exact acks on `(s, b)`. -/
def acksOn (st : State n) (s : Slot) (b : Block) : List (AckWire n) :=
  st.ackPool.filter (fun a => match a.decode? with
    | some (s', _, b') => s' == s && b' == b
    | none => false)

/-- [PC-SA M1; SAPC assemblePC] Assemble `PC(s, b)` from the first `q_A` acks
of distinct seats in the pool, if the result is valid. -/
def assemblePC (st : State n) (s : Slot) (b : Block) : Option (PC n) :=
  let c : PC n := ⟨s, b, (firstPerSeat (acksOn st s b)).take (pcQuorum n)⟩
  if pcValid st c then some c else none

/-- [PC-SA M1; SAPC collectPCs] Assemble and install every PC the pool
supports, in the order of the pool's `(slot, target)` candidates. -/
def collectPCs (st : State n) : State n :=
  let candidates := (st.ackPool.filterMap (fun a =>
    a.decode?.map (fun x => (x.1, x.2.2)))).eraseDups
  candidates.foldl (fun acc sb =>
    match assemblePC acc sb.1 sb.2 with
    | none => acc
    | some c => installPC acc c) st

/-- [PC-SA M1] Pool one copy of a decodable ack. No PC assembly. -/
def poolAck (st : State n) (a : AckWire n) : State n :=
  match a.decode? with
  | some _ => if a ∈ st.ackPool then st else { st with ackPool := st.ackPool ++ [a] }
  | none => st

/-- [PC-SA M1; pcsa-decisions 3n/4] `N(s, B)`: the number of distinct seats
with a timely exact slot-`s` HEAD on `B`: the slot-`s` votes resolved before
`e_s` (the `early` cache the clock saves at `e_s`) whose target is the root
of `B`. -/
def nCount (st : State n) (s : Slot) (b : Block) : Nat :=
  (((GridCO.savedEarly st.base s).filter (fun o => GridCO.headTarget? o == some b.root)).filterMap
    GridCO.headSeat?).dedup.length

/-- [PC-SA M1; pcsa-decisions 3n/4] The ack trigger at `e_s`: the active
slot-`s` block `B` with `N(s, B) ≥ q_N`, if one is held; on more than one
(only with `≥ n/2` equivocating seats), the deepest with the greater root. -/
def ackTarget? (p : Params) (st : State p.n) (s : Slot) : Option Block :=
  (st.base.blocks.filter (fun b => b != .genesis && b.slot == s && activeCompatible st b &&
    decide (nQuorum p.n ≤ nCount st s b))).foldl (fun best b =>
      match best with
      | none => some b
      | some c => if deeper c b then some b else best) none

end AvailableChain.PCSA
end
