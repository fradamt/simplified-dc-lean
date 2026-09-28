module
public import AvailableChainFGSA.Model.Objects

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [spec 339–353, 486–503; M1] The composite node store. `base` holds the SA
fields and the erased cumulative tree (`Σ.T`, stamps, vote pool, saved results
`Σ.genuine`, leases `Σ.lease` as `obligations`, `S` as `stableRecord`). `base`
also has five model-only caches that no FG-SA duty or output reads: `frozen`,
`early`, `releaseSnapshots`, `goldfishRecord` (G) and `base.proposals` (DQ8).
`fg` holds `Σ.T` with rows and the FG caches `F, J, h_j, hmax`. `proposals`
holds the admitted proposal wires with their signed rows (for the HEAD merge and
row inclusion; MetaInv, Task 12). `rowPool` is `Σ.attestations`. `fastWrite` is
`Σ.fastWrite`. `σ[B]` is `derive p.E p.cfg B`, not a field. Λ is not a field
(DQ4). -/
structure State (n : Nat) where
  base : GridCO.State n := GridCO.initial n
  fg : Store (Fin n) := Store.init
  proposals : List (Wire n) := []
  rowPool : List (RowWire n) := []
  fastWrite : List (Slot × List Block) := []

variable {n : Nat}

/-- [spec 486–503] The initial store: every field has its initial value. -/
def initial (n : Nat) : State n := {}

/-- [spec 711] The store slot `Σ.s`. -/
def State.slot (p : Params) (st : State p.n) : Slot := p.slotOf st.base.now

/-- [spec 558–561, 789–802] The outputs. -/
def finalized (st : State n) : FGBlock (Fin n) := st.fg.F
/-- [spec 559–560] `get_confirmed`: the SA record `S`. -/
def confirmed (st : State n) : Block := st.base.stableRecord
/-- [spec 560–561] `get_stable` returns the same tip as `get_confirmed`. -/
def stable (st : State n) : Block := confirmed st

/-- [spec 360–361] Membership in `act(Σ)` of an erased block: compatibility with F. -/
def activeCompatible (st : State n) (b : Block) : Bool :=
  Block.compatible b (eraseFG st.fg.F)

/-- [spec 363–366; M2] The SA base as the SA code reads it: the stored state with
its block list filtered to `act(Σ)`. Every other field is the stored one. -/
def actView (st : State n) : GridCO.State n :=
  { st.base with blocks := st.base.blocks.filter (activeCompatible st) }

/-- [M2] Run a GridCO step on the active view, then keep the cumulative block
list. Used only with steps that do not change `blocks` (Task 7 proves it). -/
def onView (f : GridCO.State n → GridCO.State n) (st : State n) : State n :=
  { st with base := { f (actView st) with blocks := st.base.blocks } }

/-- [spec 565–566, 778–781, 890–892] `S := F` when `F ⋠ S`. -/
def normalizeS (st : State n) : State n :=
  if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st
  else { st with base := { st.base with stableRecord := eraseFG st.fg.F } }

/-- [spec 474–484, 874–894; K1, K3] `reconcile_with_finality`: delete the leases
whose target conflicts with F; filter every fastWrite set; empty each
conflicting saved result and keep its label; then `S := F` if `F ⋠ S`. It
writes no other field: not `fg`, not the blocks, stamps, pools or proposals,
not `goldfishRecord` (DQ8). -/
def reconcile (st : State n) : State n :=
  let ok := activeCompatible st
  normalizeS { st with
    base := { st.base with
      obligations := st.base.obligations.filter (fun row => ok row.1)
      genuine := st.base.genuine.map (fun row => (row.1, row.2.filter ok)) }
    fastWrite := st.fastWrite.map (fun row => (row.1, row.2.filter ok)) }

/-- [spec 293–294] `Σ.lease[B]`: the deadline of the first lease row on `b`. SA
writes one level only, so there is at most one row per target (CStoreInv
`leaseKeys`, Task 11). -/
def leaseOf (st : State n) (b : Block) : Option Time :=
  (st.base.obligations.find? (fun row => row.1 == b)).map (fun row => row.2.2)

/-- [spec 297–298, 457–461] `Σ.fastWrite[r]`, or `none` if the gate at `d_r` did
not run. There is at most one row per label (CStoreInv `fastDom`, Task 11). -/
def fastWriteAt (st : State n) (r : Slot) : Option (List Block) :=
  (st.fastWrite.find? (fun row => row.1 == r)).map Prod.snd

/-- [spec 178–182; DQ9] DC `NamedReceipt.excludes` as a store predicate: a block
that conflicts with F. A stored finalized ancestor is not excluded. -/
def blockExcluded (st : State n) (b : Block) : Bool := !activeCompatible st b

end AvailableChain.FGSA
end
