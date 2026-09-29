module
public import Mathlib.Data.Finset.Basic
public import AvailableChainModel.Objects.Codec
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

namespace AvailableChain

/-- The root of a node block with parent root `pr`, slot `s` and body `x`.
The `+ 1` keeps every node root above `genesisRoot`. -/
def nodeRoot (pr : BlockId) (s : Slot) (x : Nat) : BlockId :=
  ⟨epair pr.value (epair s x) + 1⟩

/-- A structural chain block. Protocol wire objects belong to an instance.
A block has no proposer identity: the proposer of slot `s` signs with the
slot-scoped `Auth.proposer s` (see `Objects/Seats.lean`). A node carries a
body, not a root: `Block.root` computes the root from the content. -/
inductive Block where
  | genesis
  | node (parent : Block) (slot : Slot) (body : Nat)
deriving DecidableEq, Repr

namespace Block
def slot : Block → Slot
  | .genesis => 0
  | .node _ s _ => s

/-- The root is a function of the content: the parent's root, the slot and
the body. The block does not store it. -/
def root : Block → BlockId
  | .genesis => genesisRoot
  | .node p s x => nodeRoot p.root s x

/-- The body of a node block (`0` for genesis). -/
def body : Block → Nat
  | .genesis => 0
  | .node _ _ x => x

def parent? : Block → Option (Block)
  | .genesis => none
  | .node p _ _ => some p

def parent : Block → Block
  | .genesis => .genesis
  | .node p _ _ => p

def depth : Block → Nat
  | .genesis => 0
  | .node p _ _ => p.depth + 1

section Ancestry

/-- `B ⪯ C`, by walking from `C` to genesis. -/
def preceq (B : Block) : Block → Bool
  | .genesis => decide (B = Block.genesis)
  | C@(.node p _ _) => decide (B = C) || preceq B p

def prec (B C : Block) : Bool :=
  !decide (B = C) && preceq B C

def Preceq (B C : Block) : Prop := preceq B C = true

def Prec (B C : Block) : Prop := prec B C = true

instance (B C : Block) : Decidable (Preceq B C) :=
  inferInstanceAs (Decidable (preceq B C = true))

instance (B C : Block) : Decidable (Prec B C) :=
  inferInstanceAs (Decidable (prec B C = true))

def compatible (B C : Block) : Bool :=
  preceq B C || preceq C B

def Compatible (B C : Block) : Prop := compatible B C = true

end Ancestry

/-- A node root is not the genesis root, for every slot (slot `0` included). -/
theorem root_ne_genesis_of_node (p : Block) (s : Slot) (x : Nat) :
    (Block.node p s x).root ≠ genesisRoot := by
  simp [root, nodeRoot, genesisRoot]

/-- Distinct blocks have distinct roots. -/
theorem root_injective : Function.Injective Block.root := by
  intro B
  induction B with
  | genesis =>
    intro C h
    cases C with
    | genesis => rfl
    | node q t y => exact absurd h.symm (root_ne_genesis_of_node q t y)
  | node p s x ih =>
    intro C h
    cases C with
    | genesis => exact absurd h (root_ne_genesis_of_node p s x)
    | node q t y =>
      simp only [root, nodeRoot, BlockId.mk.injEq, Nat.add_right_cancel_iff] at h
      obtain ⟨hpq, hst⟩ := epair_inj h
      obtain ⟨rfl, rfl⟩ := epair_inj hst
      rw [ih (BlockId.ext hpq)]

end Block

/-! ### Store lookup by root

The lookup is over the image of `Block.root`, genesis included. This is a
resolved-block model: every carried parent is some `Block`, and the store
check `b.parent ∈ blocks` is equivalent to a lookup by its root. A root-only
wire needs more than these lemmas and a decoder: its adapter must also keep
authentication, dependencies, handler calls, refusals and proposal origin.
That refinement is open. -/

/-- The parent is in the store exactly when a stored block has its root. This
holds in the resolved-block model only; see the section note for what a
root-only wire needs. -/
theorem parent_mem_iff_root (b : Block) (blocks : List Block) :
    b.parent ∈ blocks ↔ ∃ p ∈ blocks, p.root = b.parent.root := by
  constructor
  · intro h
    exact ⟨b.parent, h, rfl⟩
  · rintro ⟨p, hp, hroot⟩
    rwa [← Block.root_injective hroot]

/-- A test `q` on the stored parent is the same test on the stored block that
the root lookup finds. Pass `q` explicitly. -/
theorem parent_mem_and_iff_root (b : Block) (blocks : List Block) (q : Block → Prop) :
    (b.parent ∈ blocks ∧ q b.parent) ↔ ∃ p ∈ blocks, p.root = b.parent.root ∧ q p := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨b.parent, h, rfl, hq⟩
  · rintro ⟨p, hp, hroot, hq⟩
    rw [← Block.root_injective hroot]
    exact ⟨hp, hq⟩

end AvailableChain
end
