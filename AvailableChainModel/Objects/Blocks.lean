module
public import Mathlib.Data.Finset.Basic
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

namespace AvailableChain

/-- A structural chain block. Protocol wire objects belong to an instance.
A block has no proposer identity: the proposer of slot `s` signs with the
slot-scoped `Auth.proposer s` (see `Objects/Seats.lean`). -/
inductive Block where
  | genesis
  | node (parent : Block) (slot : Slot) (root : BlockId)
deriving DecidableEq, Repr

namespace Block
def slot : Block → Slot
  | .genesis => 0
  | .node _ s _ => s

def root : Block → BlockId
  | .genesis => genesisRoot
  | .node _ _ r => r

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
end Block
end AvailableChain
end
