module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import AvailableChainModel.Objects.Identifiers
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.SimplexFG

open AvailableChain

abbrev Height := Nat

-- port: DC/DecoupledConsensusModel/Objects/NamedBlocks.lean:31–48
/-- The height pair of a row, bound to an entry. -/
inductive NamedHeightPair where
  | empty
  | vote (height : Height) (entry : BlockId) (timeout : Bool)
  deriving DecidableEq, Repr

namespace NamedHeightPair
/-- Targets and timeouts use the same height and entry match. -/
def matchesEntry (height : Height) (entry : BlockId) : NamedHeightPair → Bool
  | .empty => false
  | .vote h target _ => decide (h = height ∧ target = entry)
end NamedHeightPair

/-- The finality pair `(h_f, T_f)` (port: DC/DecoupledConsensusModel/Objects/Blocks.lean:60–66). -/
structure FinalityPair where
  height : Height
  target : BlockId
  deriving DecidableEq, Repr

/-- One FG row: signer, height pair, finality pair. No SG field. -/
structure Row (V : Type) where
  signer : V
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- A block as the FG reads it. The AP maps its blocks to this type later. -/
inductive FGBlock (V : Type) where
  | genesis
  | node (parent : FGBlock V) (slot : Slot) (root : BlockId) (rows : List (Row V))
  deriving DecidableEq, Repr

namespace FGBlock
variable {V : Type}
def slot : FGBlock V → Slot
  | .genesis => 0
  | .node _ s _ _ => s
def root : FGBlock V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ => r
def parent : FGBlock V → FGBlock V
  | .genesis => .genesis
  | .node p _ _ _ => p
def rows : FGBlock V → List (Row V)
  | .genesis => []
  | .node _ _ _ rs => rs

variable [DecidableEq V]
def preceq (A : FGBlock V) : FGBlock V → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node p _ _ _) => decide (A = B) || preceq A p
def Preceq (A B : FGBlock V) : Prop := preceq A B = true
instance (A B : FGBlock V) : Decidable (Preceq A B) :=
  inferInstanceAs (Decidable (preceq A B = true))
def compatible (A B : FGBlock V) : Bool := preceq A B || preceq B A
end FGBlock

-- port: DC/DecoupledConsensusModel/Protocol/Evidence.lean `chain_attestations`
/-- The rows carried by the chain that ends at `B`. -/
def chainRows {V : Type} [DecidableEq V] : FGBlock V → Finset (Row V)
  | .genesis => ∅
  | .node p _ _ rs => rs.toFinset ∪ chainRows p

-- port: DC/DecoupledConsensusModel/Objects/Weights.lean:49–78
/-- Fixed positive weights. FG-SA uses weight 1. -/
structure Electorate (V : Type) [Fintype V] where
  weight : V → Nat
  weight_pos : ∀ i, 0 < weight i

namespace Electorate
variable {V : Type} [Fintype V] [DecidableEq V]
def totalWeight (E : Electorate V) : Nat := ∑ i, E.weight i
def weightOf (E : Electorate V) (S : Finset V) : Nat := ∑ i ∈ S, E.weight i
/-- `q = ⌈2W/3⌉`; with unit weights this is FG-SA's `q_F = (2n+2) div 3`. -/
def q (E : Electorate V) : Nat := (2 * E.totalWeight + 2) / 3
def IsQuorum (E : Electorate V) (S : Finset V) : Prop := E.q ≤ E.weightOf S
end Electorate

example : (FGBlock.genesis : FGBlock (Fin 1)).preceq .genesis = true := by decide
example : (NamedHeightPair.vote 2 ⟨5⟩ true).matchesEntry 2 ⟨5⟩ = true := by decide
example : (⟨fun _ => 1, fun _ => Nat.one_pos⟩ : Electorate (Fin 4)).q = 3 := by decide

end AvailableChain.SimplexFG
end
