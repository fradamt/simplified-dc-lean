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
ROOT-DIGEST W1; DC NamedBlocks. The proposer of slot `s` signs with the
slot-scoped `Auth.proposer s` (see `Objects/Seats.lean`). A node carries a
body and an explicit root. The run contract limits root collisions. -/
inductive Block where
  | genesis
  | node (parent : Block) (slot : Slot) (root : BlockId) (body : Nat)
deriving DecidableEq, Repr

namespace Block
def slot : Block → Slot
  | .genesis => 0
  | .node _ s _ _ => s

/-- [ROOT-DIGEST W1; DC NamedBlocks] Read the stored root. -/
def root : Block → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ => r

/-- The body of a node block (`0` for genesis). -/
def body : Block → Nat
  | .genesis => 0
  | .node _ _ _ x => x

def parent? : Block → Option (Block)
  | .genesis => none
  | .node p _ _ _ => some p

def parent : Block → Block
  | .genesis => .genesis
  | .node p _ _ _ => p

def depth : Block → Nat
  | .genesis => 0
  | .node p _ _ _ => p.depth + 1

section Ancestry

/-- `B ⪯ C`, by walking from `C` to genesis. -/
def preceq (B : Block) : Block → Bool
  | .genesis => decide (B = Block.genesis)
  | C@(.node p _ _ _) => decide (B = C) || preceq B p

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

/-- [ROOT-DIGEST W1; DC NamedRootCollisionFree] Scoped node/genesis separation. -/
theorem root_ne_genesis_of_node (p : Block) (s : Slot) (r : BlockId) (x : Nat)
    (hr : (Block.node p s r x).root = genesisRoot → Block.node p s r x = .genesis) :
    (Block.node p s r x).root ≠ genesisRoot := fun h => Block.noConfusion (hr h)

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
theorem parent_mem_iff_root (b : Block) (blocks : List Block)
    (hr : ∀ p ∈ blocks, p.root = b.parent.root → p = b.parent) :
    b.parent ∈ blocks ↔ ∃ p ∈ blocks, p.root = b.parent.root := by
  constructor
  · intro h
    exact ⟨b.parent, h, rfl⟩
  · rintro ⟨p, hp, hroot⟩
    rwa [← hr p hp hroot]

/-- A test `q` on the stored parent is the same test on the stored block that
the root lookup finds. Pass `q` explicitly. -/
theorem parent_mem_and_iff_root (b : Block) (blocks : List Block) (q : Block → Prop)
    (hr : ∀ p ∈ blocks, p.root = b.parent.root → p = b.parent) :
    (b.parent ∈ blocks ∧ q b.parent) ↔ ∃ p ∈ blocks, p.root = b.parent.root ∧ q p := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨b.parent, h, rfl, hq⟩
  · rintro ⟨p, hp, hroot, hq⟩
    rw [← hr p hp hroot]
    exact ⟨hp, hq⟩

private theorem Block.Compatible_eq_1_export : type_of% (@Block.Compatible.eq_1) :=
  @Block.Compatible.eq_1
private theorem Block.compatible_eq_1_export : type_of% (@Block.compatible.eq_1) :=
  @Block.compatible.eq_1

end AvailableChain
end
