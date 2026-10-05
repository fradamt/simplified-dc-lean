module
public import AvailableChainPCSA.Model.Store

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; pcsa-decisions R-a; GridCO admissionLevels] The lease levels
of a prefix at gate `s`: the one SA level when the prefix is slow admissible
(`J = {k}`: `k` consecutive saved results cover it). There is no τ fast lease. -/
def slowLevels (p : Params) {n : Nat} (v : GridCO.State n .root) (s : Slot) (b : Block) :
    List Nat :=
  if SA.Root.slowEligible p.toParams v s b then [SA.releaseThreshold p.toParams] else []

/-- [PC-SA M1; pcsa34-r3 3.7; GridCO gateFrom] The SA gate with the walk
from `a`, the slow lease loop only, and the effective leases: `pcT` is
`Σ.pc.target`. A genuine gate advances G. It advances S and writes
obligations only when the result is compatible with every live EFFECTIVE
target (compatible with `pcT`); a lease write needs the prefix compatible
with `pcT`. -/
def gateFrom (p : Params) {n : Nat} (a : Block) (pcT : Option Block)
    (v : GridCO.State n .root) (s : Slot) : GridCO.State n .root :=
  let pcOK := fun b => pcT.all (fun t => Block.compatible b t)
  let q := p.toParams.engine
  match SA.Root.confirmationFrom p.toParams a v s with
  | none => { v with genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s none }
  | some h =>
      let v := { v with
        goldfishRecord := GridCO.advance v.goldfishRecord h
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some h) }
      if v.obligations.any (fun row => pcOK row.1 && !Block.compatible row.1 h) then v else
        let v := { v with stableRecord := GridCO.advance v.stableRecord h }
        let prefixes := v.blocks.filter (fun b => b != .genesis && Block.preceq b h && pcOK b)
        prefixes.foldl (fun acc b =>
          (slowLevels p acc s b).foldl
            (fun acc g => GridCO.writeObligation acc b g
              (GridCO.gateTime q s + GridCO.lifetime q)) acc) v

/-- [PC-SA M1; FG-SA Clock.lean fastSet; pcsa-decisions R-l]
[spec 4e85ff34: 892–906, 588–592, 1280–1297] The fast-write set of gate
`s`, computed on the active view before the gate: empty if the result is empty
or vetoed (by an effective lease, as the gate guard); else the non-genesis
active prefixes of the result that pass the fast test `p(s,B) ≥ τ`. The
result is `genuine_result`: the walk from the anchor `a` (the gate passes
`Σ.F`). SOURCE-ONLY: no lease is written from it. -/
def fastSet (p : Params) (a : Block) (pcT : Option Block) (v : GridCO.State p.n .root)
    (s : Slot) : List Block :=
  let pcOK := fun b => pcT.all (fun t => Block.compatible b t)
  match SA.Root.confirmationFrom p.toParams a v s with
  | none => []
  | some h =>
      if v.obligations.any (fun row => pcOK row.1 && !Block.compatible row.1 h) then [] else
        v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
          decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v s b))

/-- [PC-SA M1; FG-SA Clock.lean gateStep; pcsa-decisions R-l]
[spec 885–913, 502–505; M7, DQ5] `update_confirmation`: if label `s` is not
saved, run the gate on the active view with the walk from `Σ.F`
(`genuine_result`) and record the source-only `fastWrite[s]`; then `S := F`
if `F ⋠ S`, also after an empty or vetoed gate. -/
def gateStep (p : Params) (st : State p.n) (s : Slot) : State p.n :=
  let a := eraseFG st.fg.F
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    { onView (fun v => gateFrom p a (pcTarget? st) v s) st with
      fastWrite := st.fastWrite ++ [(s, fastSet p a (pcTarget? st) (actView st) s)] }
  normalizeS st

/-- [PC-SA M1; FG-SA Clock.lean clockPre; pcsa-decisions R-f]
[spec 683–694, 709–752; M8] The tick before the gate: set the time and
expire leases; the freeze (on the active view) and the PC snapshot at `z_s`
(the latest held PC; written once per label, as `recordGenuine`; review fix
4); the early cache at `e_s` (on the active view; the ack
duty reads it); the release at `q_{s−1}` (on the active view). The step order
and the time tests are those of `GridCO.clockFrom`. -/
def clockPre (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let q := p.toParams
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
    { onView (fun v => GridCO.freeze q.engine v fSlot) st with
      pcSnapshot := if (st.pcSnapshot.find? (fun row => row.1 == fSlot)).isSome then
        st.pcSnapshot else st.pcSnapshot ++ [(fSlot, latestPC st)] } else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
    onView (fun v =>
      { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] }) st
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot then
    onView (fun v => SA.Root.release q v qSlot) st else st

/-- [PC-SA M1] [spec 683–694, 709–752; M8] The tick: `clockPre`, then the composite gate at
`d_{s−1}`. The duties are not here (Q1). -/
def clock (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let st := clockPre p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == SA.gateTime p.toParams dSlot then gateStep p st dSlot else st

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem clock_eq_1_export :
    type_of% (@clock.eq_1) := @clock.eq_1
private theorem clockPre_eq_1_export :
    type_of% (@clockPre.eq_1) := @clockPre.eq_1
private theorem gateStep_eq_1_export :
    type_of% (@gateStep.eq_1) := @gateStep.eq_1

end AvailableChain.PCSA
end
