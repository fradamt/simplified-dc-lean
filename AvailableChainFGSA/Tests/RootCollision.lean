module
public import AvailableChainFGSA.Proofs.CrossNode
public import AvailableChainFGSA.Tests.Smoke

@[expose] public section

namespace AvailableChain.FGSA.Tests.RootCollision

open AvailableChain.SimplexFG AvailableChain.FGSA.Tests

/-! [I9; r203 §8] The former root-collision witness, now a positive test. Before
I9 the GridCO root formula `s * (parent.root + 1)` gave the honest blocks
`ba = node(genesis, 4)` and `bb = node(node(genesis, 1), 2)` the same root, and
`ContentAgree` failed on the two stores. The root is now a function of the
content, and the body packs the signed rows (D9). The tests show:
(1) both stores are reachable, and `CStoreInv` and `MetaInv` hold there;
(2) `ba.root ≠ bb.root` by structure and root injectivity; `ContentAgree` holds
for the pair, and so does the conclusion of `rootInjectiveOn_across`;
(3) a node that holds `ba` accepts `c1` and then `bb`; a repeated `bb` is
refused as a duplicate. -/

/-- The store at time 20, with no block. -/
def stT : State pT.n := clock pT (initial 4) 20
/-- Honest slot-4 block on genesis: application value `0`, no rows. -/
def ba : Block := pb .genesis 4 0 []
/-- Honest slot-1 block on genesis. -/
def c1 : Block := pb .genesis 1 0 []
/-- Honest slot-2 block on `c1`. -/
def bb : Block := pb c1 2 0 []
def wa : Wire 4 := ⟨.proposer 4, .proposal ba [] [] []⟩
def w1 : Wire 4 := ⟨.proposer 1, .proposal c1 [] [] []⟩
def wb : Wire 4 := ⟨.proposer 2, .proposal bb [] [] []⟩
/-- A node that received only `ba`. -/
def stX : State pT.n := process pT stT wa
/-- A node that received `c1` and `bb`. -/
def stY : State pT.n := process pT (process pT stT w1) wb

/-- The honest proposer's blocks pass the content check with their (empty) rows. -/
example : rowsOk ba ([] : List (RowWire 4)) = true ∧ rowsOk c1 ([] : List (RowWire 4)) = true ∧
    rowsOk bb ([] : List (RowWire 4)) = true := by decide +kernel

theorem reachable_stX : Reachable pT stX := .deliver _ (.tick _ .init)
theorem reachable_stY : Reachable pT stY := .deliver _ (.deliver _ (.tick _ .init))

theorem wa_mem : wa ∈ stX.proposals := by decide +kernel
theorem wb_mem : wb ∈ stY.proposals := by decide +kernel
theorem fg_ba : ∃ X ∈ stX.fg.TF, eraseFG X = ba := by decide +kernel
theorem fg_bb : ∃ Y ∈ stY.fg.TF, eraseFG Y = bb := by decide +kernel
/-- (1) Both blocks are admitted: the stores are not trivial. -/
example : ba ∈ stX.base.blocks ∧ bb ∈ stY.base.blocks ∧ c1 ∈ stY.base.blocks := by
  decide +kernel

/-- (1) The local invariants hold at both stores. -/
example : CStoreInv pT stX ∧ MetaInv pT stX ∧ CStoreInv pT stY ∧ MetaInv pT stY :=
  ⟨storeInvariant pT _ reachable_stX, metadataInvariant pT _ reachable_stX,
    storeInvariant pT _ reachable_stY, metadataInvariant pT _ reachable_stY⟩

/-- (2) The two blocks have different parents, so they are different blocks, and
root injectivity gives different roots. No root value is computed. -/
theorem ba_root_ne_bb_root : ba.root ≠ bb.root :=
  fun h => absurd (Block.root_injective h) (by decide)

/-- (2) `ContentAgree` holds on this pair: it is a theorem on reachable stores. -/
theorem contentAgree_stX_stY : ContentAgree stX stY :=
  contentAgree_reachable pT reachable_stX reachable_stY

/-- (2) The conclusion of `rootInjectiveOn_across` holds for this pair. -/
example : ∀ {B₁ B₂ : FGBlock (Fin 4)}, B₁ ∈ stX.fg.TF → B₂ ∈ stY.fg.TF →
    KitFG.RootInjectiveOn B₁ B₂ :=
  fun h₁ h₂ => rootInjectiveOn_across pT stX stY (storeInvariant pT _ reachable_stX)
    (storeInvariant pT _ reachable_stY) (metadataInvariant pT _ reachable_stX)
    (metadataInvariant pT _ reachable_stY) contentAgree_stX_stY h₁ h₂

/-- The store of a node that holds `ba` and then receives `c1` and `bb`. -/
def stXY : State pT.n := process pT (process pT stX w1) wb

/-- (3) A node that holds `ba` accepts `c1` and then `bb`. -/
example : ba ∈ stXY.base.blocks ∧ c1 ∈ stXY.base.blocks ∧ bb ∈ stXY.base.blocks ∧
    wb ∈ stXY.proposals := by decide +kernel

/-- (3) A repeated `bb` is refused as a duplicate: nothing changes. -/
example : (process pT stXY wb).base.blocks = stXY.base.blocks ∧
    (process pT stXY wb).fg.TF = stXY.fg.TF ∧
    (process pT stXY wb).proposals = stXY.proposals := by decide +kernel

/-! ### Derived-root checks (r203 §8; Review Focus 2, 3, 5)

Each refusal has a companion that passes every other check, so the refusal
comes from the check that it names. -/

/-- Genesis versus a slot-0 node: a node root is never the genesis root, also at
slot 0 and in the FG view. -/
example : (pb .genesis 0 0 []).root ≠ Block.genesis.root ∧
    (pk .genesis 0 0 []).root ≠ (FGBlock.genesis : FGBlock (Fin 4)).root :=
  ⟨Block.root_ne_genesis_of_node _ _ _, FGBlock.root_ne_genesis_of_node _ _ _ _⟩

/-- The same parent and slot with different bodies give different roots. -/
example : (pb .genesis 1 0 []).root ≠ (pb .genesis 1 1 []).root :=
  fun h => absurd (Block.root_injective h) (by decide +kernel)

/-- A round-0 row of identity 0. -/
def ra : RowWire 4 := rw 0 0 (rowT 0)
/-- A slot-1 block that packs the row `ra`. -/
def bR : Block := pb .genesis 1 0 [ra]

/-- A wrong row list is refused, and both the base store and the FG store stay
unchanged: the wire carries the block `bR` (which packs `[ra]`) with no rows. The
companion wire with the right rows is accepted. -/
example : rowsOk bR ([] : List (RowWire 4)) = false ∧
    wellFormed pT ⟨.proposer 1, .proposal bR [] [] []⟩ = false ∧
    (process pT stT ⟨.proposer 1, .proposal bR [] [] []⟩).base.blocks = stT.base.blocks ∧
    (process pT stT ⟨.proposer 1, .proposal bR [] [] []⟩).fg.TF = stT.fg.TF ∧
    (process pT stT ⟨.proposer 1, .proposal bR [] [] []⟩).proposals = stT.proposals ∧
    rowsOk bR [ra] = true ∧ wellFormed pT ⟨.proposer 1, .proposal bR [] [] [ra]⟩ = true ∧
    bR ∈ (process pT stT ⟨.proposer 1, .proposal bR [] [] [ra]⟩).base.blocks := by
  decide +kernel

/-- A body with the right signed-row code and a wrong outer decoded-row list:
`encFGBody (packInner 0 [ra]) []`. The content check refuses it, and both stores
and the stored wires stay unchanged. (The companion with the right decoded rows
is `bR`, above.) -/
def bW : Block := .node .genesis 1 (encFGBody (packInner 0 [ra]) ([] : List (Row (Fin 4))))
example : appOf bW.body = 0 ∧ rowsOk bW [ra] = false ∧
    wellFormed pT ⟨.proposer 1, .proposal bW [] [] [ra]⟩ = false ∧
    (process pT stT ⟨.proposer 1, .proposal bW [] [] [ra]⟩).base.blocks = stT.base.blocks ∧
    (process pT stT ⟨.proposer 1, .proposal bW [] [] [ra]⟩).fg.TF = stT.fg.TF ∧
    (process pT stT ⟨.proposer 1, .proposal bW [] [] [ra]⟩).proposals = stT.proposals := by
  decide +kernel

/-- The action round is absent from signed content and packed roots. -/
example : rw 0 0 (rowT 0) = rw 1 0 (rowT 0) ∧
    (pb .genesis 1 0 [rw 0 0 (rowT 0)]).root = (pb .genesis 1 0 [rw 1 0 (rowT 0)]).root := by
  exact ⟨rfl, rfl⟩

end AvailableChain.FGSA.Tests.RootCollision
end
