module
public import AvailableChainModel.Objects.Seats
public import AvailableChainSimplexFG.Objects

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 197–220; comp §4.2; model representation of the duty labels] Duty labels: the HEAD of
slot `s` and the fixed FG identity. -/
inductive Label where
  | head (s : Slot)
  | fg
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237] An FG row without its identity: the height pair and
the finality pair. The identity is the seat index of the fixed FG signature. -/
structure RowBody where
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237; model representation of a row without its signer] The body of an FG
row: the row without its signer. -/
def RowBody.ofRow {V : Type} (a : Row V) : RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[R2/R3] A row needs a positive height. A present finality pair must
have a smaller height. An empty height pair is not a valid sent row. -/
def RowBody.valid (a : RowBody) : Bool :=
  match a.height_pair with
  | .empty => false
  | .vote h _ _ => decide (1 ≤ h) &&
      (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[R3] The signed row payload. Finality rides on a vote at a greater height. -/
inductive RowPayload where
  | vote (body : RowBody)
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
The height pair of the vote payload. -/
def RowPayload.height_pair : RowPayload → NamedHeightPair
  | .vote body => body.height_pair

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
The finality pair of the vote payload. -/
def RowPayload.finality_pair : RowPayload → Option FinalityPair
  | .vote body => body.finality_pair

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
The input check for the vote payload. -/
def RowPayload.valid : RowPayload → Bool
  | .vote body => body.valid

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
Decode the payload with the supplied signing identity. -/
def RowPayload.toRow {V : Type} (a : RowPayload) (i : V) : Row V :=
  ⟨i, a.height_pair, a.finality_pair⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 225–228] A signed Goldfish vote, as a block carries it. -/
abbrev HeadWire (n : Nat) := Signed Label n Block
/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237] A signed FG row. Its auth is `.seat .fg i`. -/
abbrev RowWire (n : Nat) := Signed Label n RowPayload

namespace HeadWire
variable {n : Nat}
/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 225–228, 510–511; J1] The one auth decoder of a carried vote: label `s`,
seat `i`, head. -/
def decode? (o : HeadWire n) : Option (Slot × Fin n × Block) :=
  match o.auth with
  | .seat (.head s) i => some (s, i, o.payload)
  | _ => none
end HeadWire

namespace RowWire
variable {n : Nat}
/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[R1/R9] Decode the fixed FG seat and the full payload. -/
def decode? (a : RowWire n) : Option (Fin n × RowPayload) :=
  match a.auth with
  | .seat .fg i => some (i, a.payload)
  | _ => none
/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 230–237; M4] The FG row: the signer is the seat index of the fg-label
signature. The round is not a field of the FG row. -/
def toRow? (a : RowWire n) : Option (Row (Fin n)) :=
  a.decode?.map (fun x => x.2.toRow x.1)
/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 505–518; M12] The row input check: an FG signature and a valid body. -/
def valid (a : RowWire n) : Bool := (a.decode?.map (fun x => x.2.valid)).getD false
end RowWire

/-- [ROOT-DIGEST W1; DC NamedBlocks] The six full proposal fields.
The signed lists keep their order and duplicates. -/
structure DigestInput (n : Nat) where
  parent : BlockId
  slot : Slot
  app : Nat
  rows : List (RowWire n)
  raw : List (HeadWire n)
  support : List (HeadWire n)
  deriving DecidableEq, Repr

end AvailableChain.FGSA
end
