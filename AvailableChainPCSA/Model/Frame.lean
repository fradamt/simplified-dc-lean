module
public import AvailableChainPCSA.Model.Handlers
public import AvailableChainPCSA.Model.Clock
public import AvailableChainPCSA.Model.RowCore
public import AvailableChainFGSA.Model.WindowViews
public import AvailableChainKitFG.ClientOnce

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1] [spec 616–633] The live frame: the FG module's store controls. -/
def controls (p : Params) (st : State p.n) : Controls (Fin p.n) :=
  KitFG.storeControlsView (FGSA.heightView p) st.fg
/-- [PC-SA M1] [spec 1033–1037] `get_filtered_block_tree(Σ)`. -/
def fullTree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  KitFG.storeFrameView (FGSA.heightView p) st.fg st.fg.TF
/-- [PC-SA M1] [spec 1025–1037; model representation of a block set as the erased base list]
The erasure of an FG block set, in the order of the base list. -/
def erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

/-- [PC-SA M1; pcsa34-r3 3.3 frame_active] A PC is frame-active when its
target is in the full filtered tree. -/
def frameActive (p : Params) (st : State p.n) (c : PC p.n) : Bool :=
  decide (∃ B ∈ fullTree p st, eraseFG B = c.target)

/-- [PC-SA M1; FG-SA Frame.lean liveRoot; pcsa34-r3 3.3 live_root, R6]
[spec 648–655, 1086–1098] `live_root` with the PC view `c`: the root is the
view target when the view is frame-active, else the FG root `Z`; then the
deepest of the root and the live lease targets in the tree that are
compatible with the root, deeper than it, and compatible with `Σ.pc.target`
(the effective leases; ties: the greater root). Non-effective leases are
ignored, not deleted. -/
def liveRoot (p : Params) (st : State p.n) (c : Option (PC p.n)) : Block :=
  let tree := fullTree p st
  let inTree := fun b => decide (∃ B ∈ tree, eraseFG B = b)
  let z := eraseFG (controls p st).Z
  let root := match c with
    | some c => if frameActive p st c then c.target else z
    | none => z
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && inTree row.1 && Block.compatible row.1 root &&
        root.depth < row.1.depth && effectiveLease st row.1 then some row.1 else none)
  targets.foldl (fun best b => if deeper best b then b else best) root

/-- [PC-SA M1] [spec 1063–1072] `goldfish_eligible` with the band floor: the parent's state
height is below `lo`, or a strict majority, or the store's current slot. -/
def eligible (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root))
    (b : Block) :
    Bool :=
  decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧
      (FGSA.heightView p P).h < (controls p st).lo) ||
    decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
    b.slot == st.slot p

/-- [PC-SA M1] [spec 1074–1107] `get_head_in_tree`: GHOST from the live root (PC view `c`)
over `tree`. -/
def headInTree (p : Params) (st : State p.n) (c : Option (PC p.n)) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) : Block :=
  GridCO.ghost (liveRoot p st c) tree (GridCO.goldfishScore st.base.blocks raw support)
    (eligible p st raw support)

/-- [PC-SA M1] [spec 1109–1114] `get_head`: the full filtered tree, from the PC view `c`. -/
def getHead (p : Params) (st : State p.n) (c : Option (PC p.n))
    (raw support : List (GridCO.Wire p.n .root)) : Block :=
  headInTree p st c (erasedList st (fullTree p st)) raw support

/-- [PC-SA M1] [spec 190–193, 1288–1293; helper] The admitted slot-`s` proposals, with their
vote lists. These stay readable when the block leaves `act(Σ)` (spec 190–193). -/
def proposalsAt {n : Nat} (st : State n) (s : Slot) :
    List (List (HeadWire n) × List (HeadWire n)) :=
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) => if N.slot = s then some (N.raw, N.support) else none
    | _ => none)

/-- [PC-SA M1; pcsa-decisions R-f] The valid PCs carried by the admitted
slot-`s` proposals, in stored order. -/
def carriedPCs {n : Nat} (st : State n) (s : Slot) : List (PC n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) => if N.slot = s then N.pc else none
    | _ => none)).filter (pcValid st)

/-- [PC-SA M1; pcsa34-r3 3.3 view] `view(Σ, s)`: the PC frozen at `z_{s−1}`
and the PCs carried by the held slot-`s` proposals, the highest by rank (the
frozen one on a tie). -/
def voterPC {n : Nat} (st : State n) (s : Slot) : Option (PC n) :=
  (carriedPCs st s).foldl preferPC (pcSnapshotAt st (s - 1))

/-- [PC-SA M1; pcsa34-r3 3.4 A2] The view filter of an ack on `b` at `e_s`:
`view(s)` is empty, or not frame-active, or its target is below `b`. -/
def viewOK (p : Params) (st : State p.n) (s : Slot) (b : Block) : Bool :=
  match voterPC st s with
  | none => true
  | some c => !frameActive p st c || Block.preceq c.target b

/-- [PC-SA M1; pcsa34-r3 3.4, 3.8] The ack rule at `e_s`: the N target
(A1: `holdsN` on the active view, so held and F-compatible) when it passes
the view filter (A2). A6 (one ack per seat and slot) is the duty schedule:
one `ackAction s`, one object per label and seat. No veto, no continuity
rule, no lease condition, nothing the gate writes. -/
def ackFor (p : Params) (st : State p.n) (s : Slot) : Option Block :=
  (nTarget? p st s).filter (viewOK p st s)

/-- [PC-SA M1] [spec 598–606, 1219–1226] `voter_processed_block_tree(Σ, s)`: blocks of Σ.T
received before `z_{s−1}`, and every ancestor of an admitted slot-`s` proposal. -/
def voterBlocks (p : Params) (st : State p.n) (s : Slot) : Finset (FGBlock (Fin p.n)) :=
  st.fg.TF.filter (fun B =>
    decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
    decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P))

/-- [PC-SA M1] [spec 606–612, 1283–1294] The HEAD raw merge: pool votes of slot `s − 1`
received before `z_{s−1}`, and the slot-`(s−1)` votes of every admitted slot-`s`
proposal. -/
def headVotes (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n .root) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1))
  (frozenArm ++ carried).eraseDups

/-- [PC-SA M1] [spec 423–430, 1286–1293] The HEAD support merge: pool votes resolved
before `z_{s−1}` against the CURRENT `act(Σ)`; the declared support of every
admitted slot-`s` proposal whose head is in Σ.T with a valid slot. -/
def headSupport (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n .root) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
    GridCO.headLabel? o == some (s - 1) &&
      match GridCO.resolvedHead? st.base o with
      | some h => decide (h.slot ≤ s - 1)
      | none => false)
  (frozenArm ++ carried).eraseDups

/-- [PC-SA M1; FG-SA Frame.lean headVote; pcsa-decisions R-f]
[spec 1276–1302] `goldfish_vote` at `v_s`: genesis at slot 0; else the head
of the filtered voter view (live controls, M9) from the live root of the
slot-`s` PC view. Condition (G6 O-m3): the spec sets `s ← Σ.s`, and `eligible`
reads `Σ.s`, so this agrees with the spec only when `s = st.slot p`; the
caller (T7) must guarantee it. -/
def headVote (p : Params) (st : State p.n) (s : Slot) : Block :=
  if s = 0 then .genesis else
    headInTree p st (voterPC st s)
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
      (headVotes p st s) (headSupport p st s)

/-- [PC-SA M1] [spec 1240–1243] The proposer's votes: every slot-`(s−1)` pool vote. -/
def proposerVotes {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n .root) :=
  GridCO.votesAt st.base (s - 1)
/-- [PC-SA M1] [spec 1240–1243] The proposer's support: the pool votes that resolve now
(head in `act(Σ)`, valid slot). -/
def proposerSupport {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n .root) :=
  (proposerVotes st s).filter (fun o => match GridCO.resolvedHead? (actView st) o with
    | some h => decide (h.slot ≤ s - 1)
    | none => false)

/-- [PC-SA M1] [spec 552–553, 1264–1265; helper] The signed rows of the stored blocks on the chain
of `H`. -/
def chainWireRows {n : Nat} (st : State n) (H : Block) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
    | _ => none)).flatten
/-- [PC-SA M1] [R7] All rows carried in admitted blocks. -/
def blockWireRows {n : Nat} (st : State n) : List (RowWire n) := allBlockRows st

/-- [PC-SA M1] [R7] Select held, parent-valid rows absent from the parent chain at the
current slot. `proposalRowsFor` exposes this same selector above Frame. -/
def proposalRows (p : Params) (st : State p.n) (H : Block) : List (RowWire p.n) :=
  proposalRowsCore p chainWireRows
    (fun st b => pickPair st.fg.TF (fun B => decide (eraseFG B = b)))
    allBlockRows st (st.slot p) H

/-- [PC-SA M1; FG-SA Frame.lean propose; pcsa-decisions R-e, R-f]
[spec 1236–1253; D5, D9] `propose_block` at `t_s`, `s > 0`. It selects the
geometric head from the live root of the latest held PC, and the signed rows.
It resolves the head to one distinct stored named parent and constructs the
full proposal, carrying the latest PC. A missing or ambiguous named parent
gives `none`. The body packs application value `0` and the signed rows.
Condition (G6 O-m3): the spec sets `s ← Σ.s`, and `eligible` and
`proposalRows` read `Σ.s`, so this agrees with the spec only when
`s = st.slot p`; the caller (T7) must guarantee it. -/
def propose (p : Params) (st : State p.n) (s : Slot) : Option (Msg p.n) :=
  if s = 0 then none else
    let c := latestPC st
    let raw := proposerVotes st s
    let sup := proposerSupport st s
    let H := getHead p st c raw sup
    let rows := proposalRows p st H
    let rawWire := raw.filterMap liftHead?
    let supportWire := sup.filterMap liftHead?
    (namedByErase? st H).map (fun P =>
      .proposal (namedProposal p P s 0 rawWire supportWire rows c))

/-- [PC-SA M1] [spec 1318–1323] The finality head: `get_head` from the latest
held PC with the current-slot votes and their active resolved subset. -/
def fgHead (p : Params) (st : State p.n) : Block :=
  let s := st.slot p
  let raw := GridCO.votesAt st.base s
  let sup := raw.filter (fun o => match GridCO.resolvedHead? (actView st) o with
    | some h => decide (h.slot ≤ s)
    | none => false)
  getHead p st (latestPC st) raw sup

/-- [PC-SA M1] [spec 1324–1326; helper] The stored FG block of an erased block. -/
def fgBlockOf {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun B => decide (eraseFG B = b))

/-- [PC-SA M1; FG-SA Frame.lean fgSource; pcsa34-r3 3.9, R8]
[spec 666–677, 1327–1335] `C_fg`: the target of the max-rank frame-active
held PC of the opening slot `rR` of the current round; else no row. There is
no lease condition and no fallback. -/
def fgSource (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  let r := p.round (st.slot p)
  match bestPC ((st.pcs.filter (fun c => c.slot == r * p.R)).filter (frameActive p st)) with
  | some c => pickPair (fullTree p st) (fun B => decide (eraseFG B = c.target))
  | none => none

/-- [PC-SA M1] [spec 1315–1338] `get_fg_vote`: the source and the head fields of the
finality head. -/
def fgInputs (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) × HeadFields :=
  (fgSource p st, match fgBlockOf st (fgHead p st) with
    | some Hd => FGSA.Window.headFields p p.K_W Hd
    | none => ⟨0, genesisRoot, 0⟩)

/-- [PC-SA M1] [R2/R3/R4] The send-once client action. A suppressed row keeps the
complete durable record. The caller supplies the signing identity. -/
def attest (p : Params) (st : State p.n) (Λ : RecordOnce) (i : Fin p.n) :
    Option RowPayload × RecordOnce :=
  let x := fgInputs p st
  let y := createRowOnce p.E p.cfg Λ i x.1 x.2
  (y.1.map (fun a => .vote (RowBody.ofRow a)), y.2)

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem propose_eq_1_export :
    type_of% (@propose.eq_1) := @propose.eq_1

end AvailableChain.PCSA
end
