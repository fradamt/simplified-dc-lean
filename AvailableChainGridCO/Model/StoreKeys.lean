module
public import AvailableChainGridCO.Model.Protocol

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

def writeKeys {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time) : State n :=
  keys.foldl (fun acc key => writeObligation acc key.1 key.2 limit) st

theorem writeKeys_def {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time) :
    writeKeys st keys limit =
      keys.foldl (fun acc key => writeObligation acc key.1 key.2 limit) st := by
  rw [writeKeys]

def gateWriteKeys (p : Params) {n : Nat} (st : State n)
    (r : Slot) (C : Block) : List (Block × Nat) :=
  (st.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
    (fun b => (admissionLevels p st r b).map (fun g => (b, g)))

theorem gateWriteKeys_def (p : Params) {n : Nat} (st : State n)
    (r : Slot) (C : Block) :
    gateWriteKeys p st r C =
      (st.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
        (fun b => (admissionLevels p st r b).map (fun g => (b, g))) := by
  rw [gateWriteKeys]

/-- The reference root idealization, on the ancestors of a local tree. Roots
are computed from block content, so the property holds for every tree
(`rootInjectiveBelow_all`). -/
def RootInjectiveBelow (tree : List Block) : Prop :=
  ∀ A C, (∃ B ∈ tree, Block.Preceq A B) →
    (∃ B ∈ tree, Block.Preceq C B) → A.root = C.root → A = C

end AvailableChain.GridCO
end
