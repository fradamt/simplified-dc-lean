module
public import AvailableChainPCSA.Model.Frame
public import AvailableChainPCSA.Model.RowSelection

@[expose] public section

/-! PC-SA M1 smoke test (3n/4 version, pcsa34-r3, pcsa34-v2-delta (5)):
`n = 4`, `k = 3`, `R = 2`, `Δ = 1`, `q_N = 3`, `q_A = 2`. A slot-1 block,
exact slot-1 HEADs, the tick at `e_1 = 6`, the ack rule, acks, the PC, the
outputs, the carried PC, reconcile, and the gate at `d_1 = 10`. Every check
is `decide` (no `native_decide`). -/

namespace AvailableChain.PCSA.Tests

open AvailableChain.SimplexFG

/-- The finite digest table over the PC-SA digest input (the FG-SA digest reads
its embedding). -/
def digestTable : List (DigestInput 4 × BlockId) :=
  [ (⟨genesisRoot, 1, 0, [], [], [], none⟩, ⟨1⟩),
    (⟨genesisRoot, 1, 1, [], [], [], none⟩, ⟨2⟩),
    (⟨⟨1⟩, 2, 0, [], [], [], none⟩, ⟨5⟩),
    (⟨⟨2⟩, 2, 1, [], [], [], none⟩, ⟨6⟩) ]

/-- Positive IDs; 4095 is outside the finite table. -/
def fixtureDigest (d : FGSA.DigestInput 4) : BlockId :=
  ((digestTable.find? (fun e => e.1.toFGSA == d)).map Prod.snd).getD ⟨4095⟩

/-- The test parameters: Δ = 1, n = 4, k = 3, R = 2, δ_t = 1. `pT.n` reduces to
`4`, so `State 4` and `State pT.n` are one type. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 3, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fixtureDigest }

/-- The slot-1 block with no rows and application value `0`. -/
def B1 : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ (packInner 0 ([] : List (RowWire 4))) []
def b1 : Block := eraseFG B1
/-- A conflicting slot-1 sibling (application value `1`). -/
def B1' : FGBlock (Fin 4) := .node .genesis 1 ⟨2⟩ (packInner 1 ([] : List (RowWire 4))) []
def b1' : Block := eraseFG B1'
/-- The named proposals: no carried HEADs, rows or PC. -/
def N1 : NamedProposal 4 := .node .genesis 1 ⟨1⟩ b1.body [] [] [] none
def N1' : NamedProposal 4 := .node .genesis 1 ⟨2⟩ b1'.body [] [] [] none
def w1 : Wire 4 := ⟨.proposer 1, .proposal N1⟩
def w1' : Wire 4 := ⟨.proposer 1, .proposal N1'⟩

/-- [helper] A state at a new time (no clock step runs). -/
def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }
/-- A slot-1 HEAD of seat `i` on `b`. -/
def hvOn (b : Block) (i : Fin 4) : Wire 4 := ⟨.seat (.head 1) i, .head b.root⟩
def hv (i : Fin 4) : Wire 4 := hvOn b1 i
/-- A slot-1 exact ack of seat `i` on `b1`. -/
def ak (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 1) i, b1.root⟩
def akWire (i : Fin 4) : Wire 4 := ⟨.seat (.ack 1) i, .ack b1.root⟩
/-- The PC the two acks form. -/
def pc1 : PC 4 := ⟨1, b1, [ak 0, ak 1]⟩

/-- `B1` delivered at `t_1 = 4`. -/
def st4 : State pT.n := process pT (atTime {} 4) w1
/-- Three exact HEADs at `v_1 = 5`. -/
def st5 : State pT.n := [hv 0, hv 1, hv 2].foldl (process pT) (atTime st4 5)
/-- The tick at `e_1 = 6`: the early cache of slot 1 (and the empty gate of slot 0). -/
def st6 : State pT.n := clock pT st5 6
/-- Two acks delivered after `e_1`. -/
def stA : State pT.n := [akWire 0, akWire 1].foldl (process pT) st6
/-- Three HEADs delivered at 6 = `e_1` (stamp 6, not timely); the tick at 6. -/
def st6late : State pT.n := clock pT ([hv 0, hv 1, hv 2].foldl (process pT) (atTime st4 6)) 6
/-- The ticks `z_1 = 7`, `8`, `q_1 = 9`, `d_1 = 10`. -/
def st10 : State pT.n := [(7 : Time), 8, 9, 10].foldl (clock pT) stA

/-- (b) `B1` and `B1'` delivered at 4; two HEADs on each at 5; the tick at 6. -/
def st6split : State pT.n :=
  clock pT ([hv 0, hv 1, hvOn b1' 2, hvOn b1' 3].foldl (process pT)
    (atTime ([w1, w1'].foldl (process pT) (atTime {} 4)) 5)) 6
/-- (c) Seat 2 also votes `b1'` (an unresolved second HEAD); the tick at 6. -/
def st6equiv : State pT.n := clock pT (process pT st5 (hvOn b1' 2)) 6
/-- (A2) Both blocks held, three HEADs on `b1`, the tick at 6; the frozen view
of slot 0 is set by hand. -/
def st6both : State pT.n :=
  clock pT ([hv 0, hv 1, hv 2].foldl (process pT)
    (atTime ([w1, w1'].foldl (process pT) (atTime {} 4)) 5)) 6
/-- A slot-2 HEAD of seat `i` on `b`. -/
def hv2 (b : Block) (i : Fin 4) : Wire 4 := ⟨.seat (.head 2) i, .head b.root⟩
/-- A slot-1 exact ack of seat `i` on `b1'`. -/
def ak' (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 1) i, b1'.root⟩
def akWire' (i : Fin 4) : Wire 4 := ⟨.seat (.ack 1) i, .ack b1'.root⟩
/-- (A2, reachable) `PC(1, b1')` from seats 2 and 3 at 6, the freeze at `z_1 = 7`
(snapshot = that PC); at 8 a hand-built slot-2 block `X2` on `b1` (a faulty
proposer, no carried PC) or `Y2` on `b1'`; three slot-2 HEADs on it at 9;
the tick at `e_2 = 10`. -/
def stPC' : State pT.n := clock pT ([akWire' 2, akWire' 3].foldl (process pT) st6both) 7
def X2 : NamedProposal 4 := .node N1 2 ⟨5⟩ b1.body [] [] [] none
def Y2 : NamedProposal 4 := .node N1' 2 ⟨6⟩ b1'.body [] [] [] none
def st10x : State pT.n :=
  clock pT ([hv2 X2.erase 0, hv2 X2.erase 1, hv2 X2.erase 2].foldl (process pT)
    (atTime (process pT (atTime stPC' 8) ⟨.proposer 2, .proposal X2⟩) 9)) 10
def st10y : State pT.n :=
  clock pT ([hv2 Y2.erase 0, hv2 Y2.erase 1, hv2 Y2.erase 2].foldl (process pT)
    (atTime (process pT (atTime stPC' 8) ⟨.proposer 2, .proposal Y2⟩) 9)) 10

/-- The block is admitted: the erased tree, the FG tree, F unchanged; the
proposal and an ack pass the input check. -/
theorem block_admitted : st4.base.blocks = [.genesis, b1] ∧ st4.fg.TF = {.genesis, B1} ∧
    st4.fg.F = .genesis ∧ wellFormed pT w1 = true ∧ wellFormed pT (akWire 0) = true := by
  decide +kernel

/-- (a) Three exact timely HEADs give `N(1, b1) = 3 ≥ q_N = 3`, `holdsN`, and
`ackFor = some b1` at `e_1` (the count reads stamps, not the cache: it holds
at `st5` too). HEADs stamped at `e_1` are not timely: no ack. -/
theorem n_holds : nCount pT (actView st6) 1 b1 = 3 ∧ nQuorum 4 = 3 ∧
    holdsN pT (actView st6) 1 b1 = true ∧ nTarget? pT st6 1 = some b1 ∧
    ackFor pT st6 1 = some b1 ∧ ackFor pT st5 1 = some b1 := by decide +kernel
theorem n_late : nCount pT (actView st6late) 1 b1 = 0 ∧ ackFor pT st6late 1 = none := by
  decide +kernel

/-- (b) Two HEADs on `b1` and two on `b1'`: no N target, no ack. -/
theorem n_split : nCount pT (actView st6split) 1 b1 = 2 ∧
    nCount pT (actView st6split) 1 b1' = 2 ∧ ackFor pT st6split 1 = none := by decide +kernel

/-- (c) A seat with two slot-1 HEADs is excluded from `nCount`: no ack. -/
theorem n_equivocator : nCount pT (actView st6equiv) 1 b1 = 2 ∧
    ackFor pT st6equiv 1 = none := by decide +kernel

/-- (A2, reachable) The frozen view of slot 2 is `PC(1, b1')`, frame-active:
the N target `X2` on `b1` fails the view filter (no ack); `Y2` on `b1'`
passes (ack). -/
theorem view_filter : pcSnapshotAt stPC' 1 = [⟨1, b1', [ak' 2, ak' 3]⟩] ∧
    frameActive pT st10x ⟨1, b1', [ak' 2, ak' 3]⟩ = true ∧
    nTarget? pT st10x 2 = some X2.erase ∧ viewOK pT st10x 2 X2.erase = false ∧
    ackFor pT st10x 2 = none ∧
    nTarget? pT st10y 2 = some Y2.erase ∧ ackFor pT st10y 2 = some Y2.erase := by
  decide +kernel

/-- (review fix 1, D4) h1 holds two distinct unresolved acks of the faulty
seat 3 at slot 1; the relayed `PC(1, b1) = {seat 0, seat 3}` is still
installed whole (through its acks), although seat 3's ack would be refused
as a loose ack. A malformed PC (one ack) is ignored. -/
def stF : State pT.n :=
  [⟨.seat (.ack 1) 3, .ack ⟨50⟩⟩, ⟨.seat (.ack 1) 3, .ack ⟨51⟩⟩].foldl (process pT) st6
def pcF : PC 4 := ⟨1, b1, [ak 0, ak 3]⟩
theorem pc_whole : (process pT stF ⟨.seat (.ack 1) 3, .ack b1.root⟩).ackPool = stF.ackPool ∧
    (process pT stF ⟨.none, .pc pcF⟩).pcs = [pcF] ∧
    (process pT stF ⟨.none, .pc ⟨1, b1, [ak 0]⟩⟩).pcs = [] := by decide +kernel

/-- (review fix 2) A silent slot-2 proposer: all slot-2 HEADs are on `b1`
(slot 1), `N_2(b1) = 3` holds, but `b1` is not a slot-2 block: no N target,
no ack; and an ack of slot 2 on `b1` is refused at acceptance. -/
def st10s : State pT.n :=
  clock pT ([hv2 b1 0, hv2 b1 1, hv2 b1 2].foldl (process pT) (atTime stA 9)) 10
theorem silent_proposer : nCount pT (actView st10s) 2 b1 = 3 ∧ nTarget? pT st10s 2 = none ∧
    ackFor pT st10s 2 = none ∧
    (process pT st10s ⟨.seat (.ack 2) 0, .ack b1.root⟩).ackPool = st10s.ackPool := by
  decide +kernel

/-- (review fix 4) A repeated freeze tick writes the snapshot once. -/
theorem snapshot_once : (clock pT (clock pT stA 7) 7).pcSnapshot = [(1, [pc1])] := by
  decide +kernel

/-- (review fix 5) A block carrying a malformed PC is refused. -/
theorem carried_pc_wellFormed :
    (process pT (atTime stA 8) ⟨.proposer 2, .proposal (.node N1 2 ⟨5⟩ b1.body [] [] []
      (some ⟨1, b1, [ak 0]⟩))⟩).proposals = stA.proposals := by decide +kernel

/-- (d) One ack forms no PC; two acks form `PC(1, b1)` (`q_A = 2`), the
latest PC; a third ack is pooled but the held PC does not change. -/
theorem pc_formed : pcQuorum 4 = 2 ∧ latestPC (process pT st6 (akWire 0)) = none ∧
    stA.ackPool = [ak 0, ak 1] ∧ stA.pcs = [pc1] ∧ latestPC stA = some pc1 ∧
    pcAt stA 1 = some pc1 ∧ pcValid stA pc1 = true ∧
    (process pT stA (akWire 2)).pcs = [pc1] ∧
    (process pT stA (akWire 2)).ackPool = [ak 0, ak 1, ak 2] := by decide +kernel

/-- Ack acceptance: a future slot is refused; a seat's third distinct ack is
refused, its second is pooled. -/
theorem ack_acceptance :
    (process pT st6 ⟨.seat (.ack 2) 0, .ack b1.root⟩).ackPool = [] ∧
    (process pT stA ⟨.seat (.ack 1) 0, .ack b1'.root⟩).ackPool = [ak 0, ak 1,
      ⟨.seat (.ack 1) 0, b1'.root⟩] ∧
    (process pT (process pT stA ⟨.seat (.ack 1) 0, .ack b1'.root⟩)
      ⟨.seat (.ack 1) 0, .ack ⟨77⟩⟩).ackPool = [ak 0, ak 1, ⟨.seat (.ack 1) 0, b1'.root⟩] := by
  decide +kernel

/-- (e) The available output takes the PC target before the gate (`S =
genesis`), also when `S` conflicts with it; the strong output is the target. -/
theorem available_floor : stA.base.stableRecord = .genesis ∧ confirmed stA = b1 ∧
    strong stA = b1 ∧ stable stA = b1 ∧
    confirmed { stA with base := { stA.base with stableRecord := b1' } } = b1 ∧
    confirmed st6 = .genesis := by decide +kernel

/-- (g) Reconcile drops a PC that conflicts with F, keeps the ack pool, and the
PC cannot re-form while F stands. -/
theorem reconcile_drops :
    (reconcile { stA with fg := { stA.fg with F := B1' } }).pcs = [] ∧
    (reconcile { stA with fg := { stA.fg with F := B1' } }).ackPool = stA.ackPool ∧
    (collectPCs (reconcile { stA with fg := { stA.fg with F := B1' } })).pcs = [] ∧
    (reconcile { stA with fg := { stA.fg with F := B1' } }).base.stableRecord = b1' ∧
    (reconcile stA).pcs = [pc1] := by decide +kernel

/-- The slot-1 gate at `d_1 = 10` saves the genuine result `b1` and advances
`S`; no lease (`J = {k}`, `k = 3` needs three results); the PC snapshot of
`z_1 = 7` holds `pc1`; the output stays `b1`. -/
theorem gate_saves : GridCO.savedGenuine st10.base 1 = some (some b1) ∧
    st10.base.stableRecord = b1 ∧ st10.base.obligations = [] ∧
    pcSnapshotAt st10 1 = [pc1] ∧ voterPC pT st10 2 = some pc1 ∧
    confirmed st10 = b1 := by decide +kernel

/-- (f) The slot-2 proposal at `t_2 = 8` walks from the PC target and carries
the PC; delivered, it is the carried view of slot 2. -/
def prop2 : NamedProposal 4 :=
  match propose pT (atTime stA 8) 2 with
  | some (.proposal N) => N
  | _ => .genesis
def st8 : State pT.n := process pT (atTime stA 8) ⟨.proposer 2, .proposal prop2⟩

theorem proposal_carries : liveRoot pT (atTime stA 8) (some pc1) = b1 ∧
    prop2.pc = some pc1 ∧ prop2.parent = N1 ∧ prop2.slot = 2 ∧
    wellFormed pT ⟨.proposer 2, .proposal prop2⟩ = true ∧
    st8.base.blocks = [.genesis, b1, prop2.erase] ∧
    carriedPCs st8 2 = [pc1] ∧ voterPC pT st8 2 = some pc1 := by decide +kernel

/-- The slot-2 proposal with NO PC (acks never delivered), delivered at 8. -/
def prop2n : NamedProposal 4 :=
  match propose pT (atTime st6 8) 2 with
  | some (.proposal N) => N
  | _ => .genesis
def st8n : State pT.n := process pT (atTime st6 8) ⟨.proposer 2, .proposal prop2n⟩
/-- Three slot-2 HEADs on the slot-2 block at `v_2 = 9`, then the ticks to
`a_1 = d_2 = 14`: with the PC (`st14`) and without any PC (`st14n`). -/
def st14 : State pT.n :=
  [(10 : Time), 11, 12, 13, 14].foldl (clock pT)
    ([hv2 prop2.erase 0, hv2 prop2.erase 1, hv2 prop2.erase 2].foldl (process pT) (atTime st8 9))
def st14n : State pT.n :=
  [(10 : Time), 11, 12, 13, 14].foldl (clock pT)
    ([hv2 prop2n.erase 0, hv2 prop2n.erase 1, hv2 prop2n.erase 2].foldl (process pT)
      (atTime st8n 9))

/-- A slot-2 exact ack of seat `i` on the slot-2 proposal `prop2`. -/
def akWire2 (i : Fin 4) : Wire 4 := ⟨.seat (.ack 2) i, .ack prop2.erase.root⟩
def ak2 (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 2) i, prop2.erase.root⟩
def pc2 : PC 4 := ⟨2, prop2.erase, [ak2 0, ak2 1]⟩
/-- An honest opening of round 1 (slot 2): the three HEADs at `v_2 = 9`, the
tick at `e_2 = 10`, two acks delivered at 10, the ticks `z_2 = 11` to
`a_1 = d_2 = 14`. -/
def st14h : State pT.n :=
  [(11 : Time), 12, 13, 14].foldl (clock pT)
    ([akWire2 0, akWire2 1].foldl (process pT)
      (clock pT ([hv2 prop2.erase 0, hv2 prop2.erase 1, hv2 prop2.erase 2].foldl (process pT)
        (atTime st8 9)) 10))

/-- (R8′) The gate writes no fast set and no lease at `d_1`; the FG source
of round 0 at `d_1 = 10` is `none` (no PC frozen at `z_0`). -/
theorem gate_no_fast : st10.base.obligations = [] ∧ pcSnapshotAt st10 0 = [] ∧
    fgSource pT st10 = none := by decide +kernel

/-- (R8′) At `a_1 = 14`: an honest opening freezes `PC(2)` at `z_2` and the
source is its target `prop2`; a faulty opening with no `PC(2)` freezes `PC(1)`,
in the window `(0, 2]`, and the source is `b1`; with no PC in the window the
source is `none`. -/
theorem source_from_pc :
    st14h.pcs = [pc1, pc2] ∧ pcSnapshotAt st14h 2 = [pc1, pc2] ∧
    (fgSource pT st14h).map eraseFG = some prop2.erase ∧
    st14.pcs = [pc1] ∧ pcSnapshotAt st14 2 = [pc1] ∧
    (fgSource pT st14).map eraseFG = some b1 ∧
    st14n.pcs = [] ∧ pcSnapshotAt st14n 2 = [] ∧ fgSource pT st14n = none := by
  decide +kernel

/-- A slot-2 exact ack of seat `i` on `Y2` (the slot-2 block on `b1'`). -/
def akWireY (i : Fin 4) : Wire 4 := ⟨.seat (.ack 2) i, .ack Y2.erase.root⟩
def akY (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 2) i, Y2.erase.root⟩
def pcY : PC 4 := ⟨2, Y2.erase, [akY 0, akY 1]⟩
/-- (D7, C2) Both slot-1 blocks held, `PC(1, b1)` at 6, the freeze at 7, `Y2`
on `b1'` at 8, `PC(2, Y2)` from acks at 10, the ticks to 14; then the FG
store justifies `B1` by hand (`J := B1`, `h_j := 1`, `h_max := 2`: every
fixture block has FG height 1, so there is no contest, `Z = B1` and the band
floor is 1): the tree holds `b1` and not `Y2`. The max-rank frozen PC
`PC(2, Y2)` is stranded; the older window PC `PC(1, b1)` is frame-active. -/
def st14d : State pT.n :=
  [(11 : Time), 12, 13, 14].foldl (clock pT)
    ([akWireY 0, akWireY 1].foldl (process pT)
      ([(9 : Time), 10].foldl (clock pT)
        (process pT
          (atTime (clock pT (clock pT ([akWire 0, akWire 1].foldl (process pT) st6both) 7) 8) 8)
          ⟨.proposer 2, .proposal Y2⟩)))
def stD7 : State pT.n :=
  { st14d with fg := { st14d.fg with J := B1, h_j := 1, h_max := 2 } }

/-- (D7) The source and the view filter first, then take the maximum: the
source at `a_1` is `b1` (`PC(1, b1)`), not the stranded `PC(2, Y2)`; the
view of slot 3 is `PC(1, b1)`; the proposer's view is the same; `Σ.pc` (the
output floor) stays `PC(2, Y2)`. -/
theorem source_filter_first :
    st14d.pcs = [pc1, pcY] ∧ pcSnapshotAt stD7 2 = [pc1, pcY] ∧
    latestPC stD7 = some pcY ∧ frameActive pT stD7 pcY = false ∧
    frameActive pT stD7 pc1 = true ∧
    (fgSource pT stD7).map eraseFG = some b1 ∧
    voterPC pT stD7 3 = some pc1 ∧ proposerPC pT stD7 = some pc1 ∧
    strong stD7 = Y2.erase := by
  decide +kernel

/-- (D5) The snapshot of `z_1 = 7` is taken at the tick, before the deliveries
of time 7: a PC assembled from acks delivered at `z_1` itself is held but is
not in the snapshot; acks delivered before `z_1` are. -/
theorem snapshot_boundary :
    pcSnapshotAt (clock pT stA 7) 1 = [pc1] ∧
    pcSnapshotAt ([akWire 0, akWire 1].foldl (process pT) (clock pT st6 7)) 1 = [] ∧
    ([akWire 0, akWire 1].foldl (process pT) (clock pT st6 7)).pcs = [pc1] := by
  decide +kernel

/-- (h) The label code separates the three constructors (small slots); the
ack-slot hook reads the ack label only. -/
theorem encLabel_small : ∀ s < 6, ∀ s' < 6,
    encLabel (.head s) ≠ encLabel (.ack s') ∧ encLabel (.head s) ≠ encLabel .fg ∧
    encLabel (.ack s') ≠ encLabel .fg ∧
    (encLabel (.head s) = encLabel (.head s') → s = s') ∧
    (encLabel (.ack s) = encLabel (.ack s') → s = s') := by decide +kernel

/-- (h) The ack-slot hook reads the ack label only. -/
theorem ackSlot_cases (s : Slot) : Label.ackSlot? (.ack s) = some s ∧
    Label.ackSlot? (.head s) = none ∧ Label.ackSlot? .fg = none := ⟨rfl, rfl, rfl⟩

/-- (h) The label code is injective. -/
theorem encLabel_injective : Function.Injective encLabel := by
  intro a b h
  cases a <;> cases b
  all_goals
    first
    | rfl
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); omega)
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); rw [h'.2])

#print axioms gate_saves
#print axioms proposal_carries
#print axioms source_from_pc
#print axioms source_filter_first
#print axioms encLabel_injective

end AvailableChain.PCSA.Tests
end
