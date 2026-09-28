module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainKitFG.Correspondence

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- The states that the local steps reach from the initial state: ticks at any
times and deliveries of any wire objects, in any order. No engine, no run.
This is an OVER-approximation (audit M1, N3): it allows unchecked inputs
(`process` does not run `wellFormed`, DQ14) and repeated or backward clocks.
Every store fact of this plan holds on it. Exact spec simulation needs the
scheduled event order and checked inputs of T7; in particular no statement of
this plan claims that the GridCO release test equals the spec's release on an
arbitrary store (the equivocation set of `GridCO.releaseCount` reads all stored
label-r votes; the spec reads the votes stamped before `q_r`; the two agree at
the first scheduled release tick). -/
inductive Reachable (p : Params) : State p.n → Prop
  | init : Reachable p (initial p.n)
  | tick {st : State p.n} (t : Time) : Reachable p st → Reachable p (clock p st t)
  | deliver {st : State p.n} (o : Wire p.n) : Reachable p st → Reachable p (process p st o)

/-- [bp comp.outputNesting.v2; K2] `F ⪯ S` (erased). -/
def NestOK {n : Nat} (st : State n) : Prop :=
  Block.Preceq (eraseFG st.fg.F) st.base.stableRecord

/-- [bp bp.activeView.v1, bp.reconcile.v1] Every live lease target, saved
nonempty result and fastWrite member is compatible with F. -/
def SACompat {n : Nat} (st : State n) : Prop :=
  (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) ∧
  (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) ∧
  (∀ row ∈ st.fastWrite, ∀ b ∈ row.2, Block.Compatible b (eraseFG st.fg.F))

/-- [bp bp.leaseOrigins.v1 (fastWrite clause), bp.reconcile.v1 §6.3; K1; Opus M3]
The local fast-write origin invariant, relative to a block `Fb` (the erased F):
each member `B` of `fastWrite[r]` is below the saved body `C` of label `r`, or
below `Fb`. It needs no run: a gate writes a fresh label whose members are
prefixes of the saved result; reconcile keeps it (Task 9); no other step writes
`fastWrite` or `genuine`. -/
def FastOrigin {n : Nat} (Fb : Block) (st : State n) : Prop :=
  ∀ row ∈ st.fastWrite, ∀ B ∈ row.2,
    (∃ C, GridCO.savedGenuine st.base row.1 = some (some C) ∧ Block.Preceq B C) ∨
      Block.Preceq B Fb

/-- [bp bp.store.v1; K4 core; K1] The composite store invariant. `fg`: the FG
module's invariant (K4). `rootInj`: Σ.T is root-injective (DQ2). `baseTree`: the
base list is Σ.T erased. `Smem`: S is stored. `fastOrigin`, `fastDom`: the
fast-write origins (M3). `genuineKeys`, `leaseKeys`: one saved result per label
and one lease row per target, at the SA level (audit M4; used by `fastWriteAt`,
`leaseOf`). -/
structure CStoreInv (p : Params) (st : State p.n) : Prop where
  fg : KitFG.StoreInv p.E p.cfg st.fg
  rootInj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y
  baseTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b
  saCompat : SACompat st
  Smem : st.base.stableRecord ∈ st.base.blocks
  fastOrigin : FastOrigin (eraseFG st.fg.F) st
  fastDom : (st.fastWrite.map Prod.fst).Nodup ∧
    ∀ r ∈ st.fastWrite.map Prod.fst, (GridCO.savedGenuine st.base r).isSome
  genuineKeys : (st.base.genuine.map Prod.fst).Nodup
  leaseKeys : (st.base.obligations.map Prod.fst).Nodup ∧
    ∀ row ∈ st.base.obligations, row.2.1 = SA.releaseThreshold p.toParams

/-- [helper] The first three fields of `CStoreInv`: the FG invariant, root
injectivity of Σ.T, and the base list as Σ.T erased (Task 10). -/
def Inv0 (p : Params) (st : State p.n) : Prop :=
  KitFG.StoreInv p.E p.cfg st.fg ∧ (∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y) ∧
    (∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)

end AvailableChain.FGSA
end
