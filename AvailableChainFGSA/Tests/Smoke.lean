module
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Model.Frame

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
result and a fast write on the conflicting `b1'`, and S = b1'. A hand-set,
NOT reachable fixture: `b1'` is in `base.blocks` but `B1'` is not in `fg.TF`,
so the correspondence "base list = Σ.T erased" (CStoreInv `baseTree`) does not
hold. Use it only for the Task 3 read and reconcile tests, never with an
invariant. -/
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
/-- G3: `Σ.s = ⌊t / 4Δ⌋` (spec 711); with Δ = 1, times 0, 13 and 16 give slots 0, 3, 4. -/
example : State.slot pT (initial 4) = 0 ∧
    State.slot pT { base := { GridCO.initial 4 with now := 13 } } = 3 ∧
    State.slot pT { base := { GridCO.initial 4 with now := 16 } } = 4 := by decide

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

/-! Task 5: clock and composite gate. -/

/-- An empty gate at d_2 = 14 (no votes): the result is saved as empty, the fast
set of label 2 is created empty, and S := F runs after the gate (spec 756–781). -/
def stG : State pT.n :=
  { stA with base := { stA.base with now := 14, stableRecord := .genesis } }
example : GridCO.savedGenuine (gateStep pT stG 2).base 2 = some none ∧
    fastWriteAt (gateStep pT stG 2) 2 = some [] ∧
    (gateStep pT stG 2).base.stableRecord = b1 := by decide
/-- Evaluate once: a second gate of label 2 writes nothing new (spec 756). -/
example : (gateStep pT (gateStep pT stG 2) 2).fastWrite = (gateStep pT stG 2).fastWrite := by decide
/-- The clock at 14 runs the gate of slot 2 and keeps the FG part (spec 718–720). -/
example : fastWriteAt (clock pT stA 14) 2 = some [] ∧ (clock pT stA 14).fg.F = stA.fg.F := by decide

/-- [helper] A state at a new time (no clock step runs). -/
def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }
/-- A label-2 HEAD vote of seat `i` for `B2`. -/
def hv2 (i : Fin 4) : Wire 4 := ⟨.seat (.head 2) i, .head (eraseFG B2)⟩
/-- `B1`, `B2` admitted at now = 8 (stamps 8 < e_2 = 10); F stays genesis
(`B2` justifies `B1`; nothing finalizes it). -/
def stS0 : State pT.n := [wProp B1 0, wProp B2 1].foldl (process pT) (atTime {} 8)
/-- Two label-2 votes for `B2` at now = 9 (stamps 9 < e_2), then now = 14 = d_2. -/
def stS : State pT.n := atTime ([hv2 0, hv2 1].foldl (process pT) (atTime stS0 9)) 14

/-- Successful fast gate (spec 756–777, 457–461). By hand: both votes resolve
before e_2 = 10 and are late participants (stamps < d_2 = 14), so the scores are
b1: 2, b2: 2, and 2·2 > 2; the GHOST walk from genesis gives b2. The admission
level is τ = ⌈4/2⌉ = 2 ≤ p(2, B) = 2 for b1 and b2. The deadline is
d_2 + L = 14 + (4k − 1)Δ = 14 + 7 = 21. No lease exists, so there is no veto;
S := advance(genesis, b2) = b2. -/
example : GridCO.savedGenuine (gateStep pT stS 2).base 2 = some (some (eraseFG B2)) ∧
    fastWriteAt (gateStep pT stS 2) 2 = some [b1, eraseFG B2] ∧
    leaseOf (gateStep pT stS 2) b1 = some 21 ∧
    leaseOf (gateStep pT stS 2) (eraseFG B2) = some 21 ∧
    (gateStep pT stS 2).base.stableRecord = eraseFG B2 := by decide

/-- `B1'` is admitted too at now = 8, and a lease on `b1'` is set by hand. -/
def stV : State pT.n :=
  let st := atTime ([hv2 0, hv2 1].foldl (process pT)
    (atTime ([wProp B1 0, wProp B2 1, wProp B1' 0].foldl (process pT) (atTime {} 8)) 9)) 14
  { st with base := { st.base with obligations := [(b1', 2, 100)] } }
/-- Vetoed gate (spec 759–762). By hand: `b1'` has no support, so the result is
still b2 and it is saved; the live lease on `b1'` conflicts with b2, so the gate
writes no lease and `fastWrite[2] = ∅`. F is genesis, so `S := F` leaves S
(genesis) unchanged. -/
example : stV.fg.F = .genesis ∧
    GridCO.savedGenuine (gateStep pT stV 2).base 2 = some (some (eraseFG B2)) ∧
    fastWriteAt (gateStep pT stV 2) 2 = some [] ∧
    (gateStep pT stV 2).base.obligations = [(b1', 2, 100)] ∧
    (gateStep pT stV 2).base.stableRecord = .genesis := by decide

/-- Fast renewal with an unchanged deadline (spec 457–461). By hand: the gate
renews b1 with `max(100, 21) = 100`, and b1 still enters `fastWrite[2]`. -/
def stN : State pT.n := { stS with base := { stS.base with obligations := [(b1, 2, 100)] } }
example : leaseOf (gateStep pT stN 2) b1 = some 100 ∧
    fastWriteAt (gateStep pT stN 2) 2 = some [b1, eraseFG B2] := by decide

/-- Slow-only renewal (spec 457–461; SA slow arming). One label-2 vote (seat 0)
and a saved label-1 result b2. By hand: score 1 and one late voter give
2·1 > 1, so the result is b2; `p(2, b1) = 1 < τ = 2`, but `slowEligible` holds
(k = 2 ≤ 3; the label-1 result covers b1 and b2). So b1 gets a lease with
deadline 21, and `fastWrite[2] = ∅`. -/
def stW : State pT.n :=
  let st := atTime ([hv2 0].foldl (process pT) (atTime stS0 9)) 14
  { st with base := { st.base with genuine := [(1, some (eraseFG B2))] } }
example : leaseOf (gateStep pT stW 2) b1 = some 21 ∧
    fastWriteAt (gateStep pT stW 2) 2 = some [] := by decide

/-- G5 coverage: expiry (spec 713, 736–742). After the gate, both leases have the
deadline 21. At t = 20 no step runs (f_4 = 19, e_4 = 18, q_3 = 17, d_3 = 18),
and both leases stay; at t = 21 they expire (a lease expires at the first tick
at or after its deadline). No tick at 20 or 21 is a gate, so fastWrite stays. -/
example : (clock pT (gateStep pT stS 2) 20).base.obligations.length = 2 ∧
    (clock pT (gateStep pT stS 2) 21).base.obligations = [] ∧
    (clock pT (gateStep pT stS 2) 21).fastWrite = (gateStep pT stS 2).fastWrite := by decide
/-- G5 coverage: release at q_2 = 13 (spec 714–716, 744–752). The two label-2 votes for
b2 resolve before 13 and conflict with `b1'`, so 2 ≥ τ seats release the lease on
`b1'`; the lease on b1 is compatible with b2 and stays. -/
def stQ : State pT.n :=
  { stS with base := { stS.base with now := 12, obligations := [(b1', 2, 100), (b1, 2, 100)] } }
example : (clock pT stQ 13).base.obligations = [(b1, 2, 100)] := by decide
/-- G5 coverage: the model-only freeze and early caches (DQ8) run at f_2 = 11
and e_2 = 10 for label 2. -/
example : ((clock pT stS 11).base.frozen.map Prod.fst) = [2] ∧
    ((clock pT stS 10).base.early.map Prod.fst) = [2] := by decide

/-- G4: the lower bound of the row window (spec 848–851). At now = 16 the slot
is 4 and the round is 2; with w_F = 1 the window is [1, 2]. A round-0 row is
refused; a round-1 row (the bound) is admitted. -/
example : (admitRow pT (atTime {} 16) ⟨.seat (.fg 0) 0, ⟨.empty, none⟩⟩).rowPool = [] ∧
    (admitRow pT (atTime {} 16) ⟨.seat (.fg 1) 0, ⟨.empty, none⟩⟩).rowPool =
      [⟨.seat (.fg 1) 0, ⟨.empty, none⟩⟩] := by decide
/-- G4: a vote of a label above Σ.s = 3 is refused (spec 834–835); a label-3 vote
is admitted. -/
example : (process pT st0 ⟨.seat (.head 4) 0, .head b1⟩).base.votes = st0.base.votes ∧
    (process pT st0 ⟨.seat (.head 3) 0, .head b1⟩).base.votes = [⟨.seat 3 0, .head b1⟩] := by
  decide

/-! Task 6: frame reads and duties. -/

/-- The FG action of round 1 at a_1 = 14, after the empty gate of slot 2:
fastWrite[2] is empty, so C_fg is none and the height pair is empty; there is
no fallback to S, the root, a slow lease or an older set (spec 669–677). -/
def stC0 : State pT.n := clock pT stA 14
example : fastWriteAt stC0 2 = some [] ∧ (fgInputs pT stC0).1 = none ∧
    (attest pT stC0 Record.initial 0).1.height_pair = .empty := by decide
/-- With a live fast write on B2 (set by hand), C_fg = B2 (the deepest member
of fastWrite[2] in the full filtered tree with a lease after a_1). -/
def stC1 : State pT.n :=
  { stC0 with
      fastWrite := [(2, [eraseFG B2])]
      base := { stC0.base with obligations := [(eraseFG B2, 2, 21)] } }
example : (fgInputs pT stC1).1 = some B2 := by decide
/-- An expired lease does not count (spec 1329: `lease[B] > Σ.t`). -/
example : (fgInputs pT
      { stC1 with base := { stC1.base with obligations := [(eraseFG B2, 2, 14)] } }).1 =
    none := by decide
/-- Band eligibility (spec 1068): at v_4 = 17 with no votes, the HEAD walks from
Z = F = B1 (no lease). B2 is eligible because σ[B1].h = 2 < lo = 3; B3 is not
(σ[B2].h = 3, no majority, not current). -/
example : headVote pT { stA with base := { stA.base with now := 17 } } 4 = eraseFG B2 := by decide
/-- DQ13: `deepest` breaks a depth tie by the greater root (spec 260–262). -/
example : deepest ({.node .genesis 1 ⟨5⟩ [], .node .genesis 2 ⟨9⟩ []} : Finset (FGBlock (Fin 4)))
    = some (.node .genesis 2 ⟨9⟩ []) := by decide

/-- (a) Review Focus 7 (spec 423–430): resolution at read time. `B1'` enters at
now = 8, and a label-2 vote of seat 0 for `b1'` at now = 9 (before
z_2 = f_2 = 11). While F = genesis, the HEAD of slot 3 has the vote in both
merges. After `B1`, `B2`, `B3` at now = 12 move F to `B1`, `b1'` leaves `act(Σ)`:
the vote stays in the raw merge (stamp 9 < 11), but the frozen support tests the
CURRENT `act(Σ)` and drops it; no slot-3 proposal declares support. -/
def vH : GridCO.Wire 4 := ⟨.seat 2 0, .head b1'⟩
def stH0 : State pT.n :=
  atTime (process pT (atTime ([wProp B1' 0].foldl (process pT) (atTime {} 8)) 9)
    ⟨.seat (.head 2) 0, .head b1'⟩) 12
def stH : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) stH0
example : vH ∈ headVotes pT stH0 3 ∧ vH ∈ headSupport pT stH0 3 ∧
    stH.fg.F = B1 ∧ vH ∈ headVotes pT stH 3 ∧ headSupport pT stH 3 = [] := by decide

/-- (b) spec 190–193 (audit N1): a slot-3 proposal `X` on `b1'` carries a label-2
vote of seat 1 for `b1'`. `X` is admitted at now = 12 while F = genesis (its vote
enters the pool with stamp 12 ≥ z_2 = 11, so the frozen arm does not hold it).
Then `B1`, `B2`, `B3` move F to `B1`: `X` leaves `act(Σ)`, but its carried vote
stays in the raw merge of the slot-3 HEAD through the proposal arm. -/
def vX : HeadWire 4 := ⟨.seat (.head 2) 1, b1'⟩
def xB : Block := .node b1' 3 ⟨96⟩
def stX : State pT.n :=
  [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT)
    (process pT (atTime ([wProp B1' 0].foldl (process pT) (atTime {} 8)) 12)
      ⟨.proposer 3, .proposal xB [vX] [] []⟩)
example : stX.fg.F = B1 ∧ xB ∈ stX.base.blocks ∧ xB ∉ (actView stX).blocks ∧
    baseVote vX ∈ headVotes pT stX 3 := by decide

/-- (c) spec 544–556, 1255–1274: `proposal_attestations` for H = b2 at slot 3
(round 1, w_F = 1, I = {0, 1}). The pool holds the rows of B1, B2, B3 and two
round-1 rows `q 1`, `q 2` of identity 3. A new slot-3 block `Y` on b2 carries a
third identity-3 row `q 3`; the pool refuses it (two rows already). By hand: the
rows of B1 and B2 are on the chain of b2 and are dropped; the pool rows B3, `q 1`,
`q 2` stay in pool order; the block row `q 3` is dropped because identity 3
already has two pool rows in round 1. -/
def q (h : Nat) : RowWire 4 := ⟨.seat (.fg 1) 3, ⟨.vote h genesisRoot false, none⟩⟩
def yB : Block := .node (eraseFG B2) 3 ⟨95⟩
def stP : State pT.n :=
  process pT ([q 1, q 2].foldl (admitRow pT) stA) ⟨.proposer 3, .proposal yB [] [] [q 3]⟩
/-- Fallback (plan Global Constraints, R1): plain `decide` and the `Bool` form
both reach the elaborator's recursion limit on `stP`; the kernel check works. -/
example : yB ∈ stP.base.blocks ∧ q 3 ∉ stP.rowPool ∧
    proposalRows pT stP (eraseFG B2) = rowsOf 1 B3 ++ [q 1, q 2] := by decide +kernel

/-- G6 coverage: `live_root` (spec 648–655, 1086–1098). In `stA` (Z = F = B1,
now 12) a live lease on b2 makes b2 the live root (deeper than b1); an expired
lease (deadline 12) and a lease on a block outside the full filtered tree
(`b1'`) do not count, so the live root is Z = b1. -/
example : liveRoot pT { stA with base := { stA.base with obligations := [(eraseFG B2, 2, 100)] } } =
      eraseFG B2 ∧
    liveRoot pT { stA with base := { stA.base with obligations := [(eraseFG B2, 2, 12)] } } = b1 ∧
    liveRoot pT { stA with base := { stA.base with obligations := [(b1', 2, 100)] } } = b1 := by
  decide
/-- G6 coverage: `propose_block` at t_4 = 16 (spec 1236–1253). No slot-3 votes.
The head walk from Z = b1 takes b2 (band: σ[B1].h = 2 < lo = 3) and stops (b3:
σ[B2].h = 3, no majority, slot 3 ≠ Σ.s = 4). The root is 4 · (5 + 1) = 24. The
rows (I = {1, 2}): the rows of B1 (round 0) and B2 (on the chain of b2) drop;
the pool rows of B3 stay; the block rows add nothing new. -/
example : propose pT (atTime stA 16) 4 =
    some (.proposal (.node (eraseFG B2) 4 ⟨24⟩) [] [] (rowsOf 1 B3)) := by decide
/-- G6 coverage: the finality head (spec 1318–1323) at `stA` (slot 3): the walk
reaches b3 (current slot), and the head fields are those of `B3`. -/
example : fgHead pT stA = eraseFG B3 ∧
    (fgInputs pT stA).2 = HeadFields.ofBlock pT.E pT.cfg B3 := by decide
/-- G6 coverage: `attest` with a source (spec 1304–1313, 1379–1387). In `stC1`
the source is B2 and the finality head is b3. σ[B3] has h_j = h_F = 2, so there
is no finality pair; with the initial record the height pair is the target
vote `(σ[B2].h, σ[B2].T_h.root) = (3, …)`. -/
example : (attest pT stC1 Record.initial 0).1.finality_pair = none ∧
    (attest pT stC1 Record.initial 0).1.height_pair =
      .vote 3 (derive pT.E pT.cfg B2).T_h.root false := by decide

end AvailableChain.FGSA.Tests
end
