module
public import AvailableChainFGSA.Model.Store

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [spec 761–775, 457–461] The fast-write set of gate `s`, computed on the
active view before the gate: empty if the result is empty or vetoed; else the
non-genesis active prefixes of the result that pass the fast test `p(s,B) ≥ τ`.
A renewal counts also when the deadline does not change. -/
def fastSet (p : Params) (v : GridCO.State p.n) (s : Slot) : List Block :=
  match SA.confirmation p.toParams v s with
  | none => []
  | some h =>
      if v.obligations.any (fun row => !Block.compatible row.1 h) then [] else
        v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
          decide (SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams v s b))

/-- [spec 754–782; M7, DQ5] `update_confirmation`: if label `s` is not saved,
run the SA gate on the active view and record `fastWrite[s]`; then `S := F`
if `F ⋠ S`, also after an empty or vetoed gate. -/
def gateStep (p : Params) (st : State p.n) (s : Slot) : State p.n :=
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    { onView (fun v => SA.gate p.toParams v s) st with
      fastWrite := st.fastWrite ++ [(s, fastSet p (actView st) s)] }
  normalizeS st

/-- [spec 683–694, 709–752; M8] The tick before the gate: set the time and
expire leases; the freeze and early caches (on the active view; model-only,
DQ8); the release at `q_{s−1}` (on the active view). The step order and the
time tests are those of `GridCO.clock` (`GridCO/Model/Protocol.lean:485`). -/
def clockPre (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let q := p.toParams
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
    onView (fun v => GridCO.freeze q.engine v fSlot) st else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
    onView (fun v =>
      { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] }) st
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot then
    onView (fun v => SA.release q v qSlot) st else st

/-- [spec 683–694, 709–752; M8] The tick: `clockPre`, then the composite gate at
`d_{s−1}`. The duties are not here (Q1). -/
def clock (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let st := clockPre p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == SA.gateTime p.toParams dSlot then gateStep p st dSlot else st

end AvailableChain.FGSA
end
