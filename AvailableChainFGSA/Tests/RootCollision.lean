module
public import AvailableChainFGSA.Proofs.CrossNode
public import AvailableChainFGSA.Tests.Smoke

@[expose] public section

namespace AvailableChain.FGSA.Tests.RootCollision

open AvailableChain.SimplexFG AvailableChain.FGSA.Tests

/-! [DQ10/I9 limit, not a defect of the model; G13 Opus m4] Two honest blocks
with the same root under the GridCO root formula `s * (parent.root + 1)`:
`ba = node(genesis, 4)` has root `4 * 1 = 4`, and `bb = node(node(genesis, 1), 2)`
has root `2 * (1 + 1) = 4`. The tests show:
(1) both stores are reachable, and `CStoreInv` and `MetaInv` hold there;
(2) `ContentAgree` is false for the pair, and so is the conclusion of
`rootInjectiveOn_across`: the premise is load-bearing;
(3) a node that holds `ba` refuses the honest block `bb` (the DQ2 root test).
So on such a run the model differs from the spec, which idealizes distinct
roots (spec 167, 521), and the run form of K8 fails for `bb`. The report and
the T7 inputs record this. (G13 witness of the Opus audit.) -/

/-- The store at time 20, with no block. -/
def stT : State pT.n := clock pT (initial 4) 20
/-- Honest slot-4 block on genesis: root `4 * (0 + 1) = 4`. -/
def ba : Block := .node .genesis 4 ⟨4⟩
/-- Honest slot-1 block on genesis: root `1 * (0 + 1) = 1`. -/
def c1 : Block := .node .genesis 1 ⟨1⟩
/-- Honest slot-2 block on `c1`: root `2 * (1 + 1) = 4`. -/
def bb : Block := .node c1 2 ⟨4⟩
def wa : Wire 4 := ⟨.proposer 4, .proposal ba [] [] []⟩
def w1 : Wire 4 := ⟨.proposer 1, .proposal c1 [] [] []⟩
def wb : Wire 4 := ⟨.proposer 2, .proposal bb [] [] []⟩
/-- A node that received only `ba`. -/
def stX : State pT.n := process pT stT wa
/-- A node that received `c1` and `bb`. -/
def stY : State pT.n := process pT (process pT stT w1) wb

/-- The honest root formula of `GridCO.propose` gives these roots. -/
example : 4 * (Block.genesis.root.value + 1) = 4 ∧ 1 * (Block.genesis.root.value + 1) = 1 ∧
    2 * (c1.root.value + 1) = 4 := by decide

theorem reachable_stX : Reachable pT stX := .deliver _ (.tick _ .init)
theorem reachable_stY : Reachable pT stY := .deliver _ (.deliver _ (.tick _ .init))

theorem wa_mem : wa ∈ stX.proposals := by decide +kernel
theorem wb_mem : wb ∈ stY.proposals := by decide +kernel
/-- (1) Both blocks are admitted: the stores are not trivial. -/
example : ba ∈ stX.base.blocks ∧ bb ∈ stY.base.blocks ∧ c1 ∈ stY.base.blocks := by
  decide +kernel

/-- (1) The local invariants hold at both stores. -/
example : CStoreInv pT stX ∧ MetaInv pT stX ∧ CStoreInv pT stY ∧ MetaInv pT stY :=
  ⟨storeInvariant pT _ reachable_stX, metadataInvariant pT _ reachable_stX,
    storeInvariant pT _ reachable_stY, metadataInvariant pT _ reachable_stY⟩

/-- (2) `ContentAgree` is false on this honest fork. -/
theorem not_contentAgree : ¬ ContentAgree stX stY := by
  intro h
  have := (h 4 ba [] [] [] wa_mem 2 bb [] [] [] wb_mem (by decide)).1
  exact absurd this (by decide)

theorem fg_ba : ∃ X ∈ stX.fg.TF, eraseFG X = ba := by decide +kernel
theorem fg_bb : ∃ Y ∈ stY.fg.TF, eraseFG Y = bb := by decide +kernel

/-- (2) The conclusion of `rootInjectiveOn_across` is false for this pair. -/
example : ¬ (∀ {B₁ B₂ : FGBlock (Fin 4)}, B₁ ∈ stX.fg.TF → B₂ ∈ stY.fg.TF →
    KitFG.RootInjectiveOn B₁ B₂) := by
  intro h
  obtain ⟨X, hX, eX⟩ := fg_ba
  obtain ⟨Y, hY, eY⟩ := fg_bb
  have hr : X.root = Y.root := by
    rw [← eraseFG_root X, ← eraseFG_root Y, eX, eY]; rfl
  have hXY := h hX hY X Y (.inl (KitFG.preceq_refl X)) (.inr (KitFG.preceq_refl Y)) hr
  have he : eraseFG X = eraseFG Y := by rw [hXY]
  rw [eX, eY] at he
  exact absurd he (by decide)

/-- (3) A node that holds `ba` refuses the honest block `bb` (same root 4). -/
example : c1 ∈ (process pT (process pT stX w1) wb).base.blocks ∧
    bb ∉ (process pT (process pT stX w1) wb).base.blocks := by decide +kernel

end AvailableChain.FGSA.Tests.RootCollision
end
