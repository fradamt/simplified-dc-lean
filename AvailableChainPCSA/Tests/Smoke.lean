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
    (⟨genesisRoot, 1, 1, [], [], [], none⟩, ⟨2⟩) ]

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
def withView (st : State pT.n) (b : Block) : State pT.n :=
  { st with pcSnapshot := [(0, some ⟨1, b, []⟩)] }

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

/-- (A2) A frame-active frozen view on the sibling blocks the ack; a view on
`b1` itself does not. -/
theorem view_filter : frameActive pT st6both ⟨1, b1', []⟩ = true ∧
    viewOK pT (withView st6both b1') 1 b1 = false ∧
    ackFor pT (withView st6both b1') 1 = none ∧
    ackFor pT (withView st6both b1) 1 = some b1 := by decide +kernel

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
    pcSnapshotAt st10 1 = some pc1 ∧ voterPC st10 2 = some pc1 ∧
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
    carriedPCs st8 2 = [pc1] ∧ voterPC st8 2 = some pc1 := by decide +kernel

/-- The slot-2 proposal with NO PC (acks never delivered), delivered at 8. -/
def prop2n : NamedProposal 4 :=
  match propose pT (atTime st6 8) 2 with
  | some (.proposal N) => N
  | _ => .genesis
def st8n : State pT.n := process pT (atTime st6 8) ⟨.proposer 2, .proposal prop2n⟩
/-- Three slot-2 HEADs on the slot-2 block at `v_2 = 9`, then the ticks to
`a_1 = d_2 = 14`: with the PC (`st14`) and without any PC (`st14n`). -/
def hv2 (b : Block) (i : Fin 4) : Wire 4 := ⟨.seat (.head 2) i, .head b.root⟩
def st14 : State pT.n :=
  [(10 : Time), 11, 12, 13, 14].foldl (clock pT)
    ([hv2 prop2.erase 0, hv2 prop2.erase 1, hv2 prop2.erase 2].foldl (process pT) (atTime st8 9))
def st14n : State pT.n :=
  [(10 : Time), 11, 12, 13, 14].foldl (clock pT)
    ([hv2 prop2n.erase 0, hv2 prop2n.erase 1, hv2 prop2n.erase 2].foldl (process pT)
      (atTime st8n 9))

/-- (R-l) The gate at `d_1` writes the source-only `fastWrite[1] = [b1]` and
no lease; the empty gate of slot 0 wrote `[]`. -/
theorem fastWrite_gate : fastWriteAt st10 1 = some [b1] ∧ fastWriteAt st10 0 = some [] ∧
    fastWriteAt st10 2 = none ∧ st10.base.obligations = [] := by decide +kernel

/-- (R-l) An honest opening of round 1 (slot 2): at `a_1 = 14` the source is
the slot-2 proposal (`fastWrite[2] = [b1, b2]`, deepest frame-active member);
the PC is not the source. With no PC at all the source still exists. -/
theorem source_from_fastWrite :
    fastWriteAt st14 2 = some [b1, prop2.erase] ∧ st14.pcs = [pc1] ∧
    (fgSource pT st14).map eraseFG = some prop2.erase ∧
    fastWriteAt st14n 2 = some [b1, prop2n.erase] ∧ st14n.pcs = [] ∧
    (fgSource pT st14n).map eraseFG = some prop2n.erase ∧
    fgSource pT st10 = none := by decide +kernel

/-- (R-l) Reconcile filters the fastWrite sets by F. -/
theorem fastWrite_reconcile :
    (reconcile { st10 with fg := { st10.fg with F := B1' } }).fastWrite = [(0, []), (1, [])] := by
  decide +kernel

/-- (D5) The snapshot of `z_1 = 7` is taken at the tick, before the deliveries
of time 7: a PC assembled from acks delivered at `z_1` itself is held but is
not in the snapshot; acks delivered before `z_1` are. -/
theorem snapshot_boundary :
    pcSnapshotAt (clock pT stA 7) 1 = some pc1 ∧
    pcSnapshotAt ([akWire 0, akWire 1].foldl (process pT) (clock pT st6 7)) 1 = none ∧
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
#print axioms source_from_fastWrite
#print axioms encLabel_injective

end AvailableChain.PCSA.Tests
end
