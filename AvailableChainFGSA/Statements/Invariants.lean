module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainFGSA.Statements.FinalityView

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

/-- [GLY E-11, §C.3; D14] Every live lease target is below the stored output.
For a GridCO obligation, `ℓ.1` is the target and `ℓ.2.2` is the deadline.
There is no honest premise. -/
def LeaseBelowOutputStore (p : Params) (st : State p.n) : Prop :=
  ∀ ℓ ∈ st.base.obligations, st.base.now < ℓ.2.2 → Block.Preceq ℓ.1 st.base.stableRecord

theorem LeaseBelowOutputStore_def (p : Params) (st : State p.n) :
    LeaseBelowOutputStore p st =
      (∀ ℓ ∈ st.base.obligations, st.base.now < ℓ.2.2 → Block.Preceq ℓ.1 st.base.stableRecord) := by
  rw [LeaseBelowOutputStore]

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
fast-write origins (M3). `rootInj` holds on every store (`FGBlock.root_injective`,
derived roots); the field stays (D6). `genuineKeys`, `leaseKeys`: one saved result per label
and one lease row per target, at the SA level (audit M4; used by `fastWriteAt`,
`leaseOf`). -/
structure CStoreInv (p : Params) (st : State p.n) : Prop where
  fg : KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg
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
  KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg ∧
    (∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y) ∧
    (∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)

/-- [bp bp.store.v1, bp.frame.v1; K4 metadata; audit M4] The local metadata
invariant. `wireTree`: every stored wire is a decoded proposal whose body packs
its signed rows (`rowsOk`, D9: the full stored content), whose rows all decode,
and whose FG block is in Σ.T, with the SAME ordered rows (`filterMap toRow?`).
`treeWire`: every non-genesis block of Σ.T has exactly one stored wire.
`stampKeys`: the block stamps are keyed by the base list, once each.
`pool*`: the row pool holds decoded rows without duplicates. `noGenesisWire`: no stored wire
carries genesis (G12 m1; with `treeWire` it gives `contentAgree_self`). -/
structure MetaInv (p : Params) (st : State p.n) : Prop where
  wireTree : ∀ o ∈ st.proposals, ∃ s b raw sup rows,
    o = ⟨.proposer s, .proposal b raw sup rows⟩ ∧ rowsOk b rows = true ∧
    (∀ a ∈ rows, (RowWire.decode? a).isSome) ∧
    ∃ B ∈ st.fg.TF, eraseFG B = b ∧ B.rows = rows.filterMap RowWire.toRow?
  treeWire : ∀ B ∈ st.fg.TF, B ≠ .genesis →
    ∃! o, o ∈ st.proposals ∧ Wire.block? o = some (eraseFG B)
  proposalsNodup : st.proposals.Nodup
  stampKeys : st.base.blockStamp.map Prod.fst = st.base.blocks
  blocksNodup : st.base.blocks.Nodup
  poolDecodes : ∀ a ∈ st.rowPool, (RowWire.decode? a).isSome
  poolNodup : st.rowPool.Nodup
  noGenesisWire : ∀ o ∈ st.proposals, Wire.block? o ≠ some .genesis

/-- [bp bp.carrier.v1; K5 cross-node; DQ3(b), which REVERSES comp D4; audit M2;
narrowed at G12] The content premise on two stores: stored proposal wires whose
blocks have equal roots have the same erased block (with its parent chain) and
the same ordered signed rows. The carried votes and the
support list are free: no cross-node proof reads them. With derived roots and
the content check `rowsOk` it is a theorem for any two stores with the metadata
invariant (`contentAgree`, `Proofs/CrossNode.lean`); no run premise is needed. -/
def ContentAgree {n : Nat} (st st' : State n) : Prop :=
  ∀ s b raw sup rows, (⟨.proposer s, .proposal b raw sup rows⟩ : Wire n) ∈ st.proposals →
  ∀ s' b' raw' sup' rows',
    (⟨.proposer s', .proposal b' raw' sup' rows'⟩ : Wire n) ∈ st'.proposals →
    b.root = b'.root → b = b' ∧ rows = rows'

end AvailableChain.FGSA
end
