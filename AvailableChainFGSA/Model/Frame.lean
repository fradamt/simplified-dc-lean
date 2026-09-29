module
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Model.Clock

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [spec 616–633] The live frame: the FG module's store controls. -/
def controls (p : Params) (st : State p.n) : Controls (Fin p.n) := storeControls p.E p.cfg st.fg
/-- [spec 1033–1037] `get_filtered_block_tree(Σ)`. -/
def fullTree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  storeFrame p.E p.cfg st.fg st.fg.TF
/-- [spec 1025–1037; model representation of a block set as the erased base list]
The erasure of an FG block set, in the order of the base list. -/
def erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

/-- [spec 648–655, 1086–1098] `live_root`: the deepest live lease target in the
full filtered tree (ties: the greater root), else the FG root Z. -/
def liveRoot (p : Params) (st : State p.n) : Block :=
  let tree := fullTree p st
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ B ∈ tree, eraseFG B = row.1) then some row.1 else none)
  targets.foldl (fun best b =>
    if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b else best)
    (eraseFG (controls p st).Z)

/-- [spec 1063–1072] `goldfish_eligible` with the band floor: the parent's state
height is below `lo`, or a strict majority, or the store's current slot. -/
def eligible (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) (b : Block) :
    Bool :=
  decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧ hOf p.E p.cfg P < (controls p st).lo) ||
    decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
    b.slot == st.slot p

/-- [spec 1074–1107] `get_head_in_tree`: GHOST from the live root over `tree`. -/
def headInTree (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n)) : Block :=
  GridCO.ghost (liveRoot p st) tree (GridCO.goldfishScore st.base.blocks raw support)
    (eligible p st raw support)

/-- [spec 1109–1114] `get_head`: the full filtered tree. -/
def getHead (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) : Block :=
  headInTree p st (erasedList st (fullTree p st)) raw support

/-- [spec 190–193, 1288–1293; helper] The admitted slot-`s` proposals, with their
vote lists. These stay readable when the block leaves `act(Σ)` (spec 190–193). -/
def proposalsAt {n : Nat} (st : State n) (s : Slot) :
    List (List (HeadWire n) × List (HeadWire n)) :=
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ b raw sup _) => if b.slot = s then some (raw, sup) else none
    | _ => none)

/-- [spec 598–606, 1219–1226] `voter_processed_block_tree(Σ, s)`: blocks of Σ.T
received before `z_{s−1}`, and every ancestor of an admitted slot-`s` proposal. -/
def voterBlocks (p : Params) (st : State p.n) (s : Slot) : Finset (FGBlock (Fin p.n)) :=
  st.fg.TF.filter (fun B =>
    decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
    decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P))

/-- [spec 606–612, 1283–1294] The HEAD raw merge: pool votes of slot `s − 1`
received before `z_{s−1}`, and the slot-`(s−1)` votes of every admitted slot-`s`
proposal. -/
def headVotes (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1))
  (frozenArm ++ carried).eraseDups

/-- [spec 423–430, 1286–1293] The HEAD support merge: pool votes resolved
before `z_{s−1}` against the CURRENT `act(Σ)`; the declared support of every
admitted slot-`s` proposal whose head is in Σ.T with a valid slot. -/
def headSupport (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
    GridCO.headLabel? o == some (s - 1) &&
      match GridCO.headTarget? o with
      | some h => GridCO.blockKnown st.base h && decide (h.slot ≤ s - 1)
      | none => false)
  (frozenArm ++ carried).eraseDups

/-- [spec 1276–1302] `goldfish_vote` at `v_s`: genesis at slot 0; else the head
of the filtered voter view (live controls, M9) from the live root. Condition
(G6 O-m3): the spec sets `s ← Σ.s` (spec 1278), and `eligible` reads `Σ.s`, so
this agrees with the spec only when `s = st.slot p`; the caller (T7) must
guarantee it. -/
def headVote (p : Params) (st : State p.n) (s : Slot) : Block :=
  if s = 0 then .genesis else
    headInTree p st (erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)))
      (headVotes p st s) (headSupport p st s)

/-- [spec 1240–1243] The proposer's votes: every slot-`(s−1)` pool vote; the
support: those that resolve now (active head, valid slot). -/
def proposerVotes {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  GridCO.votesAt st.base (s - 1)
/-- [spec 1240–1243] The proposer's support: the pool votes that resolve now
(head in `act(Σ)`, valid slot). -/
def proposerSupport {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  (proposerVotes st s).filter (fun o => match GridCO.headTarget? o with
    | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s - 1)
    | none => false)

/-- [spec 552–553, 1264–1265; helper] The signed rows of the stored blocks on the chain
of `H`. -/
def chainWireRows {n : Nat} (st : State n) (H : Block) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ b _ _ rows) => if Block.preceq b H then some rows else none
    | _ => none)).flatten
/-- [spec 550–551, 1261–1263; helper] The rows with a round in `I` of the stored blocks
of a slot in a round of `I`. -/
def blockWireRows (p : Params) (st : State p.n) (I : Nat → Bool) : List (RowWire p.n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ b _ _ rows) =>
        if I (p.round b.slot) then some (rows.filter (fun a => (a.round?.map I).getD false))
        else none
    | _ => none)).flatten

/-- [spec 544–556, 1255–1274] `proposal_attestations(Σ, H)`: pool rows and
stored-block rows of the window `I = [max 0 (r − w_F), r]`, without rows on the
chain of `H`; per identity and round, every pool row, then distinct block rows
until there are two. Rows are grouped by their decoded `(round, identity)`, as in
`admitRow` (G6 O-m6). -/
def proposalRows (p : Params) (st : State p.n) (H : Block) : List (RowWire p.n) :=
  let r := p.round (st.slot p)
  let inI : Nat → Bool := fun r' => decide (r ≤ r' + p.wF) && decide (r' ≤ r)
  let onChain := chainWireRows st H
  let A := st.rowPool.filter (fun a => (a.round?.map inI).getD false && !decide (a ∈ onChain))
  let A' := (blockWireRows p st inI).filter (fun a => !decide (a ∈ onChain) && !decide (a ∈ A))
  A'.foldl (fun acc a =>
    let key := fun (x : RowWire p.n) => x.decode?.map (fun y => (y.1, y.2.1))
    if decide (a ∈ acc) || 2 ≤ (acc.filter (fun x => key x == key a)).length then acc
    else acc ++ [a]) A

/-- [spec 1236–1253; DQ10] `propose_block` at `t_s`, `s > 0`. The root formula
is GridCO's; it is not a content code and it can collide (DQ10). Condition
(G6 O-m3): the spec sets `s ← Σ.s` (spec 1238), and `eligible` and
`proposalRows` read `Σ.s`, so this agrees with the spec only when
`s = st.slot p`; the caller (T7) must guarantee it. -/
def propose (p : Params) (st : State p.n) (s : Slot) : Option (Msg p.n) :=
  if s = 0 then none else
    let raw := proposerVotes st s
    let sup := proposerSupport st s
    let H := getHead p st raw sup
    some (.proposal (.node H s ⟨s * (H.root.value + 1)⟩) (raw.filterMap liftHead?)
      (sup.filterMap liftHead?) (proposalRows p st H))

/-- [spec 1318–1323] The finality head: `get_head` with the current-slot votes
and their active resolved subset. -/
def fgHead (p : Params) (st : State p.n) : Block :=
  let s := st.slot p
  let raw := GridCO.votesAt st.base s
  let sup := raw.filter (fun o => match GridCO.headTarget? o with
    | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s)
    | none => false)
  getHead p st raw sup

/-- [spec 1324–1326; helper] The stored FG block of an erased block (exact under CStoreInv:
Task 11, `fgBlockOf_spec`). -/
def fgBlockOf {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun B => decide (eraseFG B = b))
/-- [spec 260–262, 1327–1335; DQ13] The deepest member (depth of the erasure);
ties: the greater root. `deepest ∅ = none`. For a nonempty set, `none` only if
two distinct maximal candidates share both depth and root; a tie between
members that are not maximal does not cause `none`. For a nonempty subset of
Σ.T, the result is `some` (Task 11, `deepest_spec`). -/
def deepest {n : Nat} (X : Finset (FGBlock (Fin n))) : Option (FGBlock (Fin n)) :=
  pickPair X (fun B => decide (∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
    ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value)))

/-- [spec 666–677, 1327–1335] `C_fg`: the deepest block of the full filtered
tree that is in `fastWrite[rR]` and has a lease deadline after now. The set is
the one of the scheduled gate `d_{rR}`; there is no older set and no fallback. -/
def fgSource (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  let r := p.round (st.slot p)
  let fw := (fastWriteAt st (r * p.R)).getD []
  deepest ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
    match leaseOf st (eraseFG B) with
    | some d => decide (st.base.now < d)
    | none => false))

/-- [spec 1315–1338] `get_fg_vote`: the source and the head fields of the
finality head. The fallback fields are unreachable under CStoreInv (Task 11,
`fgHead_stored`, `fgBlockOf_spec`). -/
def fgInputs (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) × HeadFields :=
  (fgSource p st, match fgBlockOf st (fgHead p st) with
    | some Hd => HeadFields.ofBlock p.E p.cfg Hd
    | none => ⟨0, genesisRoot, 0⟩)

/-- [spec 1304–1313, 1391–1399; DQ4, M13] `attest` without emission: the row
body and the new record (a projection of the client: no `σ.nj`, no
`Λ.timeouts`). The identity `i` is supplied by the caller (Q1). -/
def attest (p : Params) (st : State p.n) (Λ : Record) (i : Fin p.n) : RowBody × Record :=
  let x := fgInputs p st
  let y := createRow p.E p.cfg Λ i x.1 x.2
  (RowBody.ofRow y.1, y.2)

end AvailableChain.FGSA
end
