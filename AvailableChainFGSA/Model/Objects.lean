module
public import AvailableChainSA.Model.Protocol
public import AvailableChainFGSA.Model.ProposalContent
public import AvailableChainSimplexFG.Store
public import AvailableChainSimplexFG.Client

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [spec 265–335] FG-SA parameters: the SA parameters (`Δ`, `n`, `k`, `η`), the
round length `R ≥ 2`, window capacity `K_W ≥ 2`, and timeout delay `δ_t ≥ 0`
(`δ_t = 0` is allowed; no statement may need `δ_t > 0`). -/
structure Params extends SA.Params where
  R : Nat
  δt : Nat
  RLarge : 2 ≤ R
  /-- The protocol window parameter (spec: `K_W ≥ 2`, user decision 2026-10-01).
  The default is not a fixed protocol value. -/
  K_W : Nat := 2
  kWLarge : 2 ≤ K_W := by decide
  /-- [ROOT-DIGEST W1; DC NamedBlocks] Fixed digest of the full proposal. -/
  digest : DigestInput n → BlockId

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

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 248–263, 381–403; bp bp.carrier.v1] The geometric erasure of an FG block
(bp01 §2.1 `eraseFG`). The base body is the FG body code `encFGBody x rs`, so
the erasure copies the stored digest (`eraseFG_root`). -/
def eraseFG {V : Type} [RowCodec V] : FGBlock V → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (eraseFG p) s r (encFGBody x rs)

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

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[D9] The content check of a proposal: the base body is the packing of its
own application value with the carried signed rows. It is a full
reconstruction check of the body, not a root check. `contentOk` adds the digest check for both
  admission paths. -/
def rowsOk {n : Nat} (b : Block) (rw : List (RowWire n)) : Bool :=
  b.body == packBody (appOf b.body) rw

/-- [ROOT-DIGEST W1; DC NamedBlocks] Recover the full digest input. -/
def proposalInput {n : Nat} (b : Block) (raw support : List (HeadWire n))
    (rows : List (RowWire n)) : DigestInput n :=
  ⟨b.parent.root, b.slot, appOf b.body, rows, raw, support⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks] Check the BODY codec and the supplied digest. -/
def contentOk (p : Params) (b : Block) (raw support : List (HeadWire p.n))
    (rows : List (RowWire p.n)) : Bool :=
  rowsOk b rows && b.root == p.digest (proposalInput b raw support rows)

/-- [ROOT-DIGEST W1; DC NamedBlocks] Construct a proposal with its full digest. -/
def proposalBlock (p : Params) (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) : Block :=
  .node H s (p.digest ⟨H.root, s, app, rows, raw, support⟩) (packBody app rows)

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
