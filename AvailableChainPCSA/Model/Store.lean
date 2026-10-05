module
public import AvailableChainPCSA.Model.Objects

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; FG-SA Store.lean State; pcsa-decisions 3n/4]
[spec 339–353, 486–503; M1] The composite node store. `base` holds the SA
fields and the erased cumulative tree (`Σ.T`, stamps, vote pool, saved results
`Σ.genuine`, leases `Σ.lease` as `obligations`, `S` as `stableRecord`). `base`
also has the model-only caches `frozen`, `early`, `releaseSnapshots`,
`goldfishRecord` (G) and `base.proposals`; the ack duty reads `early`. `fg`
holds `Σ.T` with rows and the FG caches `F, J, h_j, hmax`. `proposals` is the
authoritative store of exact admitted named proposal wires. `rowPool` is
`Σ.attestations`. `ackPool` is `Σ.acks` (one copy of each accepted exact
ack, at most two per seat and slot). `pcs` is `Σ.pcs`: the accepted usable
F-compatible PCs, assembled from the pool, never revoked by acks; `Σ.pc` is
`latestPC`. `pcSnapshot[s]` is `Σ.pc` frozen at `z_s`. There is no
`fastWrite` (R8′: the FG source is a frozen PC). -/
structure State (n : Nat) where
  base : GridCO.State n .root := GridCO.initial n .root
  fg : Store (Fin n) := Store.init
  proposals : List (Wire n) := []
  rowPool : List (RowWire n) := []
  ackPool : List (AckWire n) := []
  pcs : List (PC n) := []
  pcSnapshot : List (Slot × Option (PC n)) := []

variable {n : Nat}

/-- [PC-SA M1; DC NamedStore.bodies] The authoritative named-body domain. -/
def State.namedBodies (st : State n) : List (NamedProposal n) :=
  .genesis :: st.proposals.filterMap Wire.proposal?

/-- [PC-SA M1; DC Handlers] Require the exact recursive parent. -/
def namedParentHeld (st : State n) (N : NamedProposal n) : Bool :=
  decide (N.parent ∈ st.namedBodies)

-- ROOT-DIGEST-2: generate the equation in its home module (BUILD B3a).
private theorem namedParentHeld_eq_1_export :
    type_of% (@namedParentHeld.eq_1) := @namedParentHeld.eq_1

/-- [PC-SA M1; DC NamedBlocks] Resolve one distinct named parent by geometry. -/
def namedByErase? (st : State n) (H : Block) : Option (NamedProposal n) :=
  match (st.namedBodies.filter (fun N => N.erase == H)).eraseDups with
  | [N] => some N
  | _ => none

/-- [PC-SA M1] [spec 486–503] The initial store: every field has its initial value. -/
def initial (n : Nat) : State n := {}

/-- [PC-SA M1] [spec 711] The store slot `Σ.s`. -/
def State.slot (p : Params) (st : State p.n) : Slot := p.slotOf st.base.now

/-- [PC-SA M1; pcsa-decisions R-f] The rank order on erased blocks: `b` is
deeper than `best`, or as deep with the greater root. -/
def deeper (best b : Block) : Bool :=
  best.depth < b.depth || (best.depth == b.depth && best.root < b.root)

/-- [PC-SA M1; pcsa34-r3 2.3] The max-rank PC of a list, the first on a
tie (`preferPC`). -/
def bestPC (cs : List (PC n)) : Option (PC n) := cs.foldl preferPC none

/-- [PC-SA M1; pcsa34-r3 3.9] The max-rank held PC of slot `s`, if any. -/
def pcAt (st : State n) (s : Slot) : Option (PC n) :=
  bestPC (st.pcs.filter (fun c => c.slot == s))

/-- [PC-SA M1; pcsa34-r3 3.1] `Σ.pc`: the max-rank held PC by rank
`(slot, depth, root)`. -/
def latestPC (st : State n) : Option (PC n) := bestPC st.pcs

/-- [PC-SA M1; pcsa34-r3 3.1] A lease row is effective when its target is
compatible with `Σ.pc.target` (or there is no PC). -/
def effectiveLease (st : State n) (b : Block) : Bool :=
  (latestPC st).all (fun c => Block.compatible b c.target)

/-- [PC-SA M1; pcsa-decisions R-f] The PC frozen at `z_s`: `none` if no PC
was held, or the freeze did not run. -/
def pcSnapshotAt (st : State n) (s : Slot) : Option (PC n) :=
  ((st.pcSnapshot.find? (fun row => row.1 == s)).map Prod.snd).getD none

/-- [PC-SA M1] The target of the latest held PC. -/
def pcTarget? (st : State n) : Option Block := (latestPC st).map PC.target

/-- [PC-SA M1] [spec 558–561, 789–802] The outputs. -/
def finalized (st : State n) : FGBlock (Fin n) := st.fg.F
/-- [PC-SA M1; pcsa-decisions R-g] `get_confirmed`: the SA record `S` floored
on the PC target: `S` if the target is below `S`, else the target (also when
`S` conflicts with it), so `strong ⪯ available` by construction. -/
def confirmed (st : State n) : Block :=
  match pcTarget? st with
  | some b => if Block.preceq b st.base.stableRecord then st.base.stableRecord else b
  | none => st.base.stableRecord
/-- [PC-SA M1; pcsa-decisions 3n/4] The strong output: the latest PC target
(genesis without a PC). -/
def strong (st : State n) : Block := (pcTarget? st).getD .genesis
/-- [PC-SA M1] [spec 560–561] `get_stable` returns the same tip as `get_confirmed`. -/
def stable (st : State n) : Block := confirmed st

/-- [PC-SA M1] [spec 360–361] Membership in `act(Σ)` of an erased block: compatibility with F. -/
def activeCompatible (st : State n) (b : Block) : Bool :=
  Block.compatible b (eraseFG st.fg.F)

/-- [PC-SA M1] [spec 363–366; M2] The SA base as the SA code reads it: the stored state with
its block list filtered to `act(Σ)`. The temporary `headDomain` pins the cumulative
resolution domain. The other fields keep their stored values. -/
def actView (st : State n) : GridCO.State n .root :=
  { st.base with
    blocks := st.base.blocks.filter (activeCompatible st)
    headDomain := some (GridCO.resolutionTree st.base) }

/-- [PC-SA M1] [spec 363–366; M2] Run a GridCO step on the active view, then restore the
cumulative block list and its original resolution metadata. -/
def onView (f : GridCO.State n .root → GridCO.State n .root) (st : State n) : State n :=
  { st with base := { f (actView st) with
      blocks := st.base.blocks, headDomain := st.base.headDomain } }

/-- [PC-SA M1] [spec 565–566, 778–781, 890–892] `S := F` when `F ⋠ S`. -/
def normalizeS (st : State n) : State n :=
  if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st
  else { st with base := { st.base with stableRecord := eraseFG st.fg.F } }

/-- [PC-SA M1; FG-SA Store.lean reconcile; pcsa-decisions 3n/4]
[spec 474–484, 874–894; K1, K3] `reconcile_with_finality`: delete the leases
whose target conflicts with F; drop every held and frozen PC whose target
conflicts with F; empty each conflicting saved result and keep its label; then
`S := F` if `F ⋠ S`. It writes no other
field: not `fg`, not the blocks, stamps, pools or proposals, not
`goldfishRecord`. The ack pool is kept; a dropped PC cannot re-form while F
stands (`pcValid` needs `act(Σ)`). -/
def reconcile (st : State n) : State n :=
  let ok := activeCompatible st
  normalizeS { st with
    base := { st.base with
      obligations := st.base.obligations.filter (fun row => ok row.1)
      genuine := st.base.genuine.map (fun row => (row.1, row.2.filter ok)) }
    pcs := st.pcs.filter (fun c => ok c.target)
    pcSnapshot := st.pcSnapshot.map (fun row => (row.1, row.2.filter (fun c => ok c.target))) }

/-- [PC-SA M1] [spec 293–294] `Σ.lease[B]`: the deadline of the first lease row on `b`. -/
def leaseOf (st : State n) (b : Block) : Option Time :=
  (st.base.obligations.find? (fun row => row.1 == b)).map (fun row => row.2.2)

/-- [PC-SA M1] [spec 178–182; DQ9] DC `NamedReceipt.excludes` as a store predicate: a block
that conflicts with F. A stored finalized ancestor is not excluded. -/
def blockExcluded (st : State n) (b : Block) : Bool := !activeCompatible st b

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem State_namedBodies_eq_1_export :
    type_of% (@State.namedBodies.eq_1) := @State.namedBodies.eq_1
private theorem actView_eq_1_export :
    type_of% (@actView.eq_1) := @actView.eq_1
private theorem namedByErase_eq_1_export :
    type_of% (@namedByErase?.eq_1) := @namedByErase?.eq_1
private theorem normalizeS_eq_1_export :
    type_of% (@normalizeS.eq_1) := @normalizeS.eq_1
private theorem onView_eq_1_export :
    type_of% (@onView.eq_1) := @onView.eq_1

end AvailableChain.PCSA
end
