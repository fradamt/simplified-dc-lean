module
public import AvailableChainFGSA.Model.Handlers

@[expose] public section

namespace AvailableChain.FGSA.Tests

open AvailableChain.SimplexFG

/-- The test parameters: Δ = 1, n = 4, k = 2, R = 2, w_F = 1, δ_t = 1.
`pT.cfg` is the FG module's `cfg1` and `pT.E` is its `E4`, so the FG test
blocks `B1`, `B2`, `B3`, `B1'` of `AvailableChainSimplexFG` apply.
`pT.n` reduces to `4`, so `State 4` and `State pT.n` are one type. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, wF := 1, δt := 1, RLarge := by decide, wFPos := by decide }

/-- A signed FG row of round `r` by identity `i`. -/
def rw (r : Nat) (i : Fin 4) (a : Row (Fin 4)) : RowWire 4 :=
  ⟨.seat (.fg r) i, RowBody.ofRow a⟩

example : eraseFG B1 = Block.node .genesis 1 ⟨1⟩ := by decide
example : (rw 0 2 (rowT 2)).decode? = some (0, 2, RowBody.ofRow (rowT 2)) := by decide
example : (rw 0 2 (rowT 2)).toRow? = some (rowT 2) := by decide
example : (rw 0 2 (rowT 2)).round? = some 0 := by decide
/-- `a_r = d_{rR}` (spec 217–220): with R = 2, `a_1 = d_2 = 4·2 + 6 = 14`. -/
example : pT.actionTime 1 = 14 := by decide
example : (Label.fg 1).actTime pT = 14 ∧ (Label.head 3).actTime pT = 13 := by decide
/-- At `a_1 = 14` the store slot is `rR + 1 = 3`, still round 1 (spec 1306, 1317). -/
example : pT.slotOf 14 = 3 ∧ pT.round 3 = 1 := by decide
/-- The base form of a carried vote: a HEAD seat of slot `s` is a seat of base
label `s`; an FG seat is not a base signature. -/
example : baseHead (n := 4) ⟨.seat (.head 3) 1, .genesis⟩ = ⟨.seat 3 1, .genesis⟩ ∧
    baseHead (n := 4) ⟨.seat (.fg 3) 1, .genesis⟩ = ⟨.none, .genesis⟩ := by decide
/-- One row check (M12; spec 234–237): height 0 fails; height 1 and the empty
pair pass; a row with a HEAD signature fails. -/
example : (RowBody.mk (.vote 0 genesisRoot false) none).valid = false ∧
    (RowBody.mk (.vote 1 genesisRoot false) none).valid = true ∧
    (RowBody.mk .empty none).valid = true ∧
    RowWire.valid (n := 4) ⟨.seat (.head 0) 2, RowBody.mk .empty none⟩ = false := by decide
example : Wire.decode (n := 4) ⟨.seat (.fg 1) 2, .row (RowBody.ofRow (rowT 2))⟩ =
    some (.row 1 2 (RowBody.ofRow (rowT 2))) ∧
    Wire.decode (n := 4) ⟨.seat (.head 1) 2, .row (RowBody.ofRow (rowT 2))⟩ = none := by decide

/-- G1: the positive row checks. An FG row at height 1 passes; an FG row at
height 0 fails. -/
example : (rw 0 2 (rowT 2)).valid = true ∧
    RowWire.valid (n := 4) ⟨.seat (.fg 0) 2, RowBody.mk (.vote 0 genesisRoot false) none⟩ =
      false := by decide

/-- A carried HEAD vote of slot 3 by seat 1 for `B1`, and an FG signature on a
HEAD payload. -/
def hv : HeadWire 4 := ⟨.seat (.head 3) 1, eraseFG B1⟩
def hf : HeadWire 4 := ⟨.seat (.fg 3) 1, eraseFG B1⟩

/-- G1: the decoders of a vote and a proposal; a wrong auth gives `none`. -/
example : hv.decode? = some (3, 1, eraseFG B1) ∧ hf.decode? = none := by decide
example : Wire.decode (n := 4) ⟨.seat (.head 3) 1, .head (eraseFG B1)⟩ =
      some (.vote 3 1 (eraseFG B1)) ∧
    Wire.decode (n := 4) ⟨.proposer 2, .proposal (eraseFG B1) [hv] [hv] [rw 0 2 (rowT 2)]⟩ =
      some (.block 2 (eraseFG B1) [hv] [hv] [rw 0 2 (rowT 2)]) ∧
    Wire.decode (n := 4) ⟨.proposer 2, .head (eraseFG B1)⟩ = none ∧
    Wire.decode (n := 4) ⟨.seat (.head 2) 1, .proposal (eraseFG B1) [] [] []⟩ = none ∧
    Wire.decode (n := 4) ⟨.seat (.fg 1) 2, .head (eraseFG B1)⟩ = none := by decide
/-- G1: `Wire.block?` gives the block of a proposal and `none` for a vote. -/
example : Wire.block? (n := 4) ⟨.proposer 2, .proposal (eraseFG B1) [] [] []⟩ =
      some (eraseFG B1) ∧
    Wire.block? (n := 4) ⟨.seat (.head 3) 1, .head (eraseFG B1)⟩ = none := by decide
/-- G1: `liftHead?` inverts `baseVote` on a HEAD vote; it gives `none` for a
base proposal. -/
example : liftHead? (baseVote hv) = some hv ∧
    liftHead? (n := 4) ⟨.proposer 2, .proposal (eraseFG B1) [] []⟩ = none := by decide
/-- G1: `baseProposal` maps each carried vote by `baseHead`: a HEAD seat keeps its
slot and seat; an FG seat becomes `.none`. -/
example : baseProposal 2 (eraseFG B1) [hv, hf] [hv] =
    ⟨.proposer 2, .proposal (eraseFG B1) [⟨.seat 3 1, eraseFG B1⟩, ⟨.none, eraseFG B1⟩]
      [⟨.seat 3 1, eraseFG B1⟩]⟩ := by decide

/-! Task 3: store, active view, reconcile, outputs. -/

def b1 : Block := eraseFG B1
def b1' : Block := eraseFG B1'
/-- F = B1 (the FG store of the FG module's G02 test), with a lease, a saved
result and a fast write on the conflicting `b1'`, and S = b1'. -/
def stR0 : State 4 :=
  { fg := stF, base := { GridCO.initial 4 with
      blocks := [.genesis, b1, eraseFG B2, eraseFG B3, b1'],
      genuine := [(1, some b1'), (2, some .genesis)],
      obligations := [(b1', 2, 100)], stableRecord := b1' },
    fastWrite := [(1, [b1'])] }

/-- Reconcile deletes the lease, empties the conflicting result but keeps its
label, keeps the compatible result, filters fastWrite, and sets S := F (spec 874–894). -/
example : (reconcile stR0).base.obligations = [] ∧
    (reconcile stR0).base.genuine = [(1, none), (2, some .genesis)] ∧
    (reconcile stR0).fastWrite = [(1, [])] ∧
    (reconcile stR0).base.stableRecord = b1 ∧
    (reconcile stR0).base.blocks = stR0.base.blocks := by decide
/-- act(Σ) keeps the cumulative list but drops `b1'` (spec 360–361). -/
example : b1' ∈ stR0.base.blocks ∧ b1' ∉ (actView stR0).blocks ∧
    b1 ∈ (actView stR0).blocks := by decide
/-- A compatible S ahead of F stays (spec 565). -/
example : (normalizeS
      { stR0 with base := { stR0.base with stableRecord := eraseFG B3 } }).base.stableRecord =
    eraseFG B3 := by decide
example : blockExcluded stR0 b1' = true ∧ blockExcluded stR0 .genesis = false := by decide

/-- G3 coverage: the initial store (spec 486–503) and the outputs (spec 558–561). -/
example : (initial 4).fg = Store.init ∧ (initial 4).base.stableRecord = .genesis ∧
    (initial 4).fastWrite = [] ∧ (initial 4).rowPool = [] := by decide
example : finalized stR0 = B1 ∧ confirmed stR0 = b1' ∧ stable stR0 = b1' := by decide
/-- G3 coverage: the lease and fastWrite reads (spec 293–298). -/
example : leaseOf stR0 b1' = some 100 ∧ leaseOf stR0 b1 = none ∧
    fastWriteAt stR0 1 = some [b1'] ∧ fastWriteAt stR0 2 = none := by decide
/-- G3 coverage: reconcile keeps a compatible lease, also on F and below F, and
writes no FG, proposal, row-pool or G field (spec 474–484). -/
example : (reconcile { stR0 with base := { stR0.base with
      obligations := [(b1', 2, 100), (.genesis, 2, 50), (b1, 2, 60)] } }).base.obligations =
    [(.genesis, 2, 50), (b1, 2, 60)] := by decide
example : (reconcile stR0).fg = stR0.fg ∧ (reconcile stR0).proposals = stR0.proposals ∧
    (reconcile stR0).rowPool = stR0.rowPool ∧
    (reconcile stR0).base.goldfishRecord = stR0.base.goldfishRecord := by decide
/-- G3 coverage: `onView` runs the step on `act(Σ)` (its last active block is
`B3`, not `b1'`) and then restores the cumulative list (M2). -/
example : (onView (fun v => { v with goldfishRecord := v.blocks.getLastD .genesis })
      stR0).base.goldfishRecord = eraseFG B3 ∧
    (onView (fun v => { v with goldfishRecord := v.blocks.getLastD .genesis })
      stR0).base.blocks = stR0.base.blocks := by decide

/-! Task 4: handlers. -/

def rowsOf (r : Nat) (B : FGBlock (Fin 4)) : List (RowWire 4) :=
  B.rows.map (fun a => ⟨.seat (.fg r) a.signer, RowBody.ofRow a⟩)
def wProp (B : FGBlock (Fin 4)) (r : Nat) (raw : List (HeadWire 4) := []) : Wire 4 :=
  ⟨.proposer B.slot, .proposal (eraseFG B) raw [] (rowsOf r B)⟩
/-- Now = 12: slot 3, round 1. -/
def st0 : State pT.n := { base := { GridCO.initial 4 with now := 12 } }
def stA : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) st0

/-- The FG part is the FG module's store after the same blocks (K4). -/
example : stA.fg.TF = stF.TF ∧ stA.fg.F = B1 ∧ stA.fg.J = stF.J ∧
    stA.fg.h_j = stF.h_j ∧ stA.fg.h_max = stF.h_max := by decide
/-- The base holds the erased tree (spec 355–358). -/
example : stA.base.blocks = [.genesis, b1, eraseFG B2, eraseFG B3] := by decide
/-- F moved to B1: S := F (spec 890–892). -/
example : stA.base.stableRecord = b1 := by decide

/-- Review Focus 2 (audit N1). A label-2 vote and a fresh round-1 row: separate
calls admit both at stA (slot 3, round 1). -/
def v2 : HeadWire 4 := ⟨.seat (.head 2) 0, eraseFG B2⟩
def rF : RowWire 4 := ⟨.seat (.fg 1) 3, ⟨.vote 1 ⟨77⟩ true, none⟩⟩
example : (process pT stA ⟨v2.auth, .head v2.payload⟩).base.votes ≠ stA.base.votes ∧
    (admitRow pT stA rF).rowPool = stA.rowPool ++ [rF] := by decide
/-- A checked slot-3 block on genesis conflicts with F = B1. It carries `v2` and
`rF`. Refusal of `F ⋠ B` before unpacking (spec 808, 535–536): no block, no
stamp, no carried vote, no row, no FG change, no stored wire. -/
def wX : Wire 4 := ⟨.proposer 3, .proposal (.node .genesis 3 ⟨99⟩) [v2] [] [rF]⟩
example : wellFormed pT wX = true := by decide
example : (process pT stA wX).base.blocks = stA.base.blocks ∧
    (process pT stA wX).base.votes = stA.base.votes ∧
    (process pT stA wX).base.blockStamp = stA.base.blockStamp ∧
    (process pT stA wX).rowPool = stA.rowPool ∧
    (process pT stA wX).fg.TF = stA.fg.TF ∧
    (process pT stA wX).proposals = stA.proposals := by decide
/-- A duplicate block changes nothing (spec 806–807). -/
example : (process pT stA (wProp B2 1)).base.blocks = stA.base.blocks ∧
    (process pT stA (wProp B2 1)).proposals = stA.proposals ∧
    (process pT stA (wProp B2 1)).rowPool = stA.rowPool := by decide
/-- A row from the block's future (spec 815–817): a slot-1 block (round 0) with a
round-1 row fails the input check and is refused by the handler. -/
def wFut : Wire 4 := ⟨.proposer 1, .proposal (.node .genesis 1 ⟨98⟩) [] [] [rw 1 2 (rowT 2)]⟩
example : wellFormed pT wFut = false ∧ (process pT st0 wFut).fg.TF = st0.fg.TF := by decide
/-- Review Focus 9 (M12): the same height-0 row fails alone and in a block; the
height-1 row passes in both forms. -/
def r0 : RowWire 4 := ⟨.seat (.fg 1) 2, ⟨.vote 0 genesisRoot false, none⟩⟩
def r1 : RowWire 4 := ⟨.seat (.fg 1) 2, ⟨.vote 1 genesisRoot false, none⟩⟩
example : wellFormed pT ⟨r0.auth, .row r0.payload⟩ = false ∧
    wellFormed pT ⟨.proposer 3, .proposal (.node .genesis 3 ⟨97⟩) [] [] [r0]⟩ = false ∧
    wellFormed pT ⟨r1.auth, .row r1.payload⟩ = true ∧
    wellFormed pT ⟨.proposer 3, .proposal (.node .genesis 3 ⟨97⟩) [] [] [r1]⟩ = true := by decide

/-- A handler-integration fixture (NOT a reachable state: the lease, the saved
result and the fast write on `b1'` are set by hand). `B1'` enters while
F = genesis; then `B1`, `B2`, `B3` move F to `B1`, and reconcile runs inside the
handler. -/
def stR1 : State pT.n :=
  let st := process pT st0 (wProp B1' 0)
  { st with
      base := { st.base with
        genuine := [(1, some b1')], obligations := [(b1', 2, 100)], stableRecord := b1' }
      fastWrite := [(1, [b1'])] }
def stR2 : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) stR1
example : stR2.fg.F = B1 ∧ stR2.base.obligations = [] ∧
    GridCO.savedGenuine stR2.base 1 = some none ∧ stR2.fastWrite = [(1, [])] ∧
    stR2.base.stableRecord = b1 ∧ b1' ∈ stR2.base.blocks ∧
    b1' ∉ (actView stR2).blocks := by decide

/-- DQ2: a new block whose root is already stored is refused. -/
example : (process pT stA ⟨.proposer 3, .proposal (.node b1 3 B2.root) [] [] []⟩).fg.TF
    = stA.fg.TF := by decide
/-- The row pool admits at most two distinct rows per identity and round
(spec 433–439, 852–855), and only rows in the window (spec 848–851). -/
def rA (h : Nat) : RowWire 4 := ⟨.seat (.fg 1) 0, ⟨.vote h genesisRoot false, none⟩⟩
example : ([rA 1, rA 2, rA 3].foldl (admitRow pT) st0).rowPool = [rA 1, rA 2] := by decide
example : (admitRow pT st0 ⟨.seat (.fg 2) 0, ⟨.empty, none⟩⟩).rowPool = [] := by decide

/-- G4 coverage: temporary refusals (spec 806–807). A block whose parent is not
stored, and a block from a future slot (`4 > Σ.s = 3`), change nothing. -/
example : (process pT st0 (wProp B2 1)).fg.TF = st0.fg.TF ∧
    (process pT st0 (wProp B2 1)).base.blocks = st0.base.blocks ∧
    (process pT stA ⟨.proposer 4, .proposal (.node b1 4 ⟨96⟩) [] [] []⟩).fg.TF = stA.fg.TF := by
  decide
/-- G4 coverage: the slot-3 block signed by the slot-2 proposer key fails the
input check and the handler refuses it (spec 511–512, 810–812). -/
example : wellFormed pT ⟨.proposer 2, .proposal (.node b1 3 ⟨95⟩) [] [] []⟩ = false ∧
    (process pT stA ⟨.proposer 2, .proposal (.node b1 3 ⟨95⟩) [] [] []⟩).fg.TF = stA.fg.TF := by
  decide
/-- G4 coverage: a slot-1 vote at slot 3 is outside the vote window (spec 834–835);
a wire that does not decode changes nothing and fails the input check. -/
example : (process pT stA ⟨.seat (.head 1) 0, .head b1⟩).base.votes = stA.base.votes ∧
    (process pT stA ⟨.proposer 3, .head b1⟩).base.votes = stA.base.votes ∧
    (process pT stA ⟨.proposer 3, .head b1⟩).fg.TF = stA.fg.TF ∧
    wellFormed pT ⟨.proposer 3, .head b1⟩ = false := by decide
/-- G4 coverage: an accepted slot-3 block on `B2` passes its carried vote `v2`
to the vote pool (spec 820–821) and stores its wire. -/
def wY : Wire 4 := ⟨.proposer 3, .proposal (.node (eraseFG B2) 3 ⟨96⟩) [v2] [] []⟩
example : baseVote v2 ∈ (process pT stA wY).base.votes ∧ baseVote v2 ∉ stA.base.votes ∧
    (process pT stA wY).proposals = stA.proposals ++ [wY] ∧
    Block.node (eraseFG B2) 3 ⟨96⟩ ∈ (process pT stA wY).base.blocks := by decide
/-- G4 coverage: the pool refuses the rows of `B1` in `stR2` (they duplicate the
rows of `B1'`), but the FG block `B1` keeps them (spec 540–541). The pool holds
the three round-0 rows of `B1'` and the six round-1 rows of `B2`, `B3`. -/
example : B1 ∈ stR2.fg.TF ∧ B1.rows.length = 3 ∧ stR2.rowPool.length = 9 := by decide

end AvailableChain.FGSA.Tests
end
