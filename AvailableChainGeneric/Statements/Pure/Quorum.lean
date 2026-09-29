module

@[expose] public section

/-! Generic Pure layer: the unit-weight quorum and the regime records `FaultQ`,
`FaultX` and `Batch` (GLY A.3, C.1; step-2 item I01, ruling D05). Definitions
only. Each record is a one-field `structure … : Prop`, so a proof reads the
field and needs no equation lemma. -/

namespace AvailableChain.Gen.Pure

/-- The unit-weight quorum `q_F = (2n+2) div 3`. The body is the body of
`AvailableChain.SimplexFG.Electorate.q` (AvailableChainSimplexFG/Objects.lean:209,
`(2 * E.totalWeight + 2) / 3`) with `E.totalWeight = n`, its value for unit
weights. -/
def qF (n : Nat) : Nat := (2 * n + 2) / 3

theorem qF_def (n : Nat) : qF n = (2 * n + 2) / 3 := by rw [qF]

/-- `a < q_F n`: one `q_F` set has an honest member (GLY C.1). -/
structure FaultQ (n a : Nat) : Prop where
  lt : a < qF n

/-- `a + n < 2 q_F n`: two `q_F` sets meet in an honest member (GLY C.1). -/
structure FaultX (n a : Nat) : Prop where
  lt : a + n < 2 * qF n

/-- `m < h`: an honest batch beats the rest (GLY C.1). -/
structure Batch (h m : Nat) : Prop where
  lt : m < h

end AvailableChain.Gen.Pure
