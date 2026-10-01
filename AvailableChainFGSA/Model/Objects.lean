module
public import AvailableChainSA.Model.Protocol
public import AvailableChainSimplexFG.Store
public import AvailableChainSimplexFG.Client

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [spec 265–335] FG-SA parameters: the SA parameters (`Δ`, `n`, `k`, `η`), the
round length `R ≥ 2` and the timeout delay `δ_t ≥ 0`
(`δ_t = 0` is allowed; no statement may need `δ_t > 0`). -/
structure Params extends SA.Params where
  R : Nat
  δt : Nat
  RLarge : 2 ≤ R

namespace Params
/-- [spec 154–158] Unit weights on the fixed identities `V = Fin n`. -/
def E (p : Params) : Electorate (Fin p.n) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
/-- [spec 283] The FG configuration: the timeout delay `δ_t`. -/
def cfg (p : Params) : FGConfig := ⟨p.δt⟩
/-- [spec 209] `round(s) = ⌊s / R⌋`. -/
def round (p : Params) (s : Slot) : Nat := s / p.R
/-- [spec 217–220] `a_r = T_r + 6Δ = d_{rR}`. -/
def actionTime (p : Params) (r : Nat) : Time := SA.gateTime p.toParams (r * p.R)
/-- [spec 711] `Σ.s = ⌊t / 4Δ⌋`, as `GridCO.admitProposal` computes it. -/
def slotOf (p : Params) (t : Time) : Slot := (t / (4 * p.Δ)).toNat
end Params

/-- [spec 197–220; comp §4.2; model representation of the duty labels] Duty labels: the HEAD of
slot `s` and the fixed FG identity. -/
inductive Label where
  | head (s : Slot)
  | fg
  deriving DecidableEq, Repr

/-- [spec 230–237] An FG row without its identity: the height pair and
the finality pair. The identity is the seat index of the fixed FG signature. -/
structure RowBody where
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- [spec 230–237; model representation of a row without its signer] The body of an FG
row: the row without its signer. -/
def RowBody.ofRow {V : Type} (a : Row V) : RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [R2/R3] A row needs a positive height. A present finality pair must
have a smaller height. An empty height pair is not a valid sent row. -/
def RowBody.valid (a : RowBody) : Bool :=
  match a.height_pair with
  | .empty => false
  | .vote h _ _ => decide (1 ≤ h) &&
      (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true

/-- [R3] The signed row payload. Finality rides on a vote at a greater height. -/
inductive RowPayload where
  | vote (body : RowBody)
  deriving DecidableEq, Repr

/-- The height pair of the vote payload. -/
def RowPayload.height_pair : RowPayload → NamedHeightPair
  | .vote body => body.height_pair

/-- The finality pair of the vote payload. -/
def RowPayload.finality_pair : RowPayload → Option FinalityPair
  | .vote body => body.finality_pair

/-- The input check for the vote payload. -/
def RowPayload.valid : RowPayload → Bool
  | .vote body => body.valid

/-- Decode the payload with the supplied signing identity. -/
def RowPayload.toRow {V : Type} (a : RowPayload) (i : V) : Row V :=
  ⟨i, a.height_pair, a.finality_pair⟩

/-- [spec 225–228] A signed Goldfish vote, as a block carries it. -/
abbrev HeadWire (n : Nat) := Signed Label n Block
/-- [spec 230–237] A signed FG row. Its auth is `.seat .fg i`. -/
abbrev RowWire (n : Nat) := Signed Label n RowPayload

namespace HeadWire
variable {n : Nat}
/-- [spec 225–228, 510–511; J1] The one auth decoder of a carried vote: label `s`,
seat `i`, head. -/
def decode? (o : HeadWire n) : Option (Slot × Fin n × Block) :=
  match o.auth with
  | .seat (.head s) i => some (s, i, o.payload)
  | _ => none
end HeadWire

namespace RowWire
variable {n : Nat}
/-- [R1/R9] Decode the fixed FG seat and the full payload. -/
def decode? (a : RowWire n) : Option (Fin n × RowPayload) :=
  match a.auth with
  | .seat .fg i => some (i, a.payload)
  | _ => none
/-- [spec 230–237; M4] The FG row: the signer is the seat index of the fg-label
signature. The round is not a field of the FG row. -/
def toRow? (a : RowWire n) : Option (Row (Fin n)) :=
  a.decode?.map (fun x => x.2.toRow x.1)
/-- [spec 505–518; M12] The row input check: an FG signature and a valid body. -/
def valid (a : RowWire n) : Bool := (a.decode?.map (fun x => x.2.valid)).getD false
end RowWire

/-- [spec 225–263; comp §4.2] The payloads. A proposal carries the erased block,
the previous-slot votes, the declared support subset and its own signed rows
(M3). -/
inductive Msg (n : Nat) where
  | head (target : Block)
  | proposal (b : Block) (view supportView : List (HeadWire n)) (rows : List (RowWire n))
  | row (body : RowPayload)
  deriving DecidableEq, Repr

/-- [spec 225–263; comp §4.2] A wire object: an auth and a payload. -/
abbrev Wire (n : Nat) := Signed Label n (Msg n)

/-- [spec 505–518, 804–857; J1; model representation of a decoded input] A decoded
wire. -/
inductive Input (n : Nat) where
  | vote (s : Slot) (i : Fin n) (target : Block)
  | row (i : Fin n) (body : RowPayload)
  | block (s : Slot) (b : Block) (raw support : List (HeadWire n)) (rows : List (RowWire n))
  deriving DecidableEq, Repr

/-- [spec 505–518; J1] The one auth decoder of a wire. Every handler and the input check read
a wire only through `Wire.decode`, `HeadWire.decode?` and `RowWire.decode?`. On
engine v2, a decode adapter to `Wire p.n` keeps the internal API; T7 sets the
scope of a native re-typing (Q1 boundary). -/
def Wire.decode {n : Nat} (o : Wire n) : Option (Input n) :=
  match o.auth, o.payload with
  | .seat (.head s) i, .head b => some (.vote s i b)
  | .seat .fg i, .row body => some (.row i body)
  | .proposer s, .proposal b raw sup rows => some (.block s b raw sup rows)
  | _, _ => none

/-- [spec 248–255; helper] The block of a proposal wire. -/
def Wire.block? {n : Nat} (o : Wire n) : Option Block :=
  match o.decode with
  | some (.block _ b _ _ _) => some b
  | _ => none

/-- [spec 248–263, 381–403; bp bp.carrier.v1] The geometric erasure of an FG block
(bp01 §2.1 `eraseFG`). The base body is the FG body code `encFGBody x rs`, so
the erasure keeps the root (`eraseFG_root`): both roots read the same content
with the same outer code. -/
def eraseFG {V : Type} [RowCodec V] : FGBlock V → Block
  | .genesis => .genesis
  | .node p s x rs => .node (eraseFG p) s (encFGBody x rs)

/-! ### Signed content in the base body (D9)

A proposal carries a base block and its signed rows. The base body packs an
application value and the ORDERED signed rows, so the rows
are part of the block identity. The FG view of the block reads the same
content: its body is the inner packed value and its rows are the decoded rows.
Every code is built from `epair` and `encList` (`Objects/Codec.lean`); a sum
is a pair of a constructor tag and its fields. -/

/-- The label code: tag `0` for a HEAD label, tag `1` for an FG label. -/
def encLabel : Label → Nat
  | .head s => epair 0 s
  | .fg => epair 1 0

/-- The auth code: tag `0` for a seat (label and index), tag `1` for a
proposer (slot), tag `2` for no auth. -/
def encAuth {n : Nat} : Auth Label n → Nat
  | .seat ℓ i => epair 0 (epair (encLabel ℓ) i.val)
  | .proposer s => epair 1 s
  | .none => epair 2 0

/-- The row-body code: the height pair and the optional finality pair. -/
def encRowBody (a : RowBody) : Nat :=
  epair (encHeightPair a.height_pair) (encOption encFinalityPair a.finality_pair)

/-- The vote tag and its complete body code. -/
def encRowPayload : RowPayload → Nat
  | .vote body => epair 0 (encRowBody body)

/-- The signed-row code: the complete auth (fixed label and seat) and the
body. -/
def encRowWire {n : Nat} (a : RowWire n) : Nat := epair (encAuth a.auth) (encRowPayload a.payload)

/-- The inner packed value: the application value and the ordered signed rows. -/
def packInner {n : Nat} (app : Nat) (rw : List (RowWire n)) : Nat :=
  epair app (encList encRowWire rw)

/-- The packed base body: the FG body code of the inner packed value and the
decoded rows. -/
def packBody {n : Nat} (app : Nat) (rw : List (RowWire n)) : Nat :=
  encFGBody (packInner app rw) (rw.filterMap RowWire.toRow?)

/-- The application value of a packed body (`appOf_packBody`). On a body that
is not packed the value has no meaning; `rowsOk` checks the full packing. -/
def appOf (x : Nat) : Nat := efst (efst (esnd x))

/-- [D9] The content check of a proposal: the base body is the packing of its
own application value with the carried signed rows. It is a full
reconstruction check of the body, not a root check. `wellFormed` and
`blockAccepted` use this same function. -/
def rowsOk {n : Nat} (b : Block) (rw : List (RowWire n)) : Bool :=
  b.body == packBody (appOf b.body) rw

/-- [spec 225–228; model representation of a carried vote in the SA base] The base
form of a carried vote: a HEAD seat of slot `s` becomes a
seat of base label `s`; any other auth becomes `.none`. -/
def baseHead {n : Nat} (o : HeadWire n) : GridCO.HeadWire n :=
  match o.decode? with
  | some (s, i, b) => ⟨.seat s i, b⟩
  | none => ⟨.none, o.payload⟩
/-- [spec 225–228, 821–823; model representation of a carried vote as an SA pool
vote] The base form of a carried vote as a GridCO vote wire. -/
def baseVote {n : Nat} (o : HeadWire n) : GridCO.Wire n := GridCO.fromHead (baseHead o)
/-- [spec 1240–1249; helper] A base vote as a composite carried vote (for the proposer's lists).
It reads the GridCO accessors; it matches no auth. -/
def liftHead? {n : Nat} (o : GridCO.Wire n) : Option (HeadWire n) := do
  let s ← GridCO.headLabel? o
  let i ← GridCO.headSeat? o
  let b ← GridCO.headTarget? o
  pure ⟨.seat (.head s) i, b⟩
/-- [spec 248–255, 820–823; model representation of a proposal in the SA base] The
base proposal of a decoded composite proposal (as SA-PC `baseProposal`). -/
def baseProposal {n : Nat} (s : Slot) (b : Block) (raw support : List (HeadWire n)) :
    GridCO.Wire n :=
  ⟨.proposer s, .proposal b (raw.map baseHead) (support.map baseHead)⟩

end AvailableChain.FGSA
end
