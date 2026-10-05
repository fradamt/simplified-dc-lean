module
public import AvailableChainPCSA.Model.Frame
public import AvailableChainPCSA.Model.RowSelection

@[expose] public section

/-! PC-SA M1 smoke test (3n/4 version, pcsa-decisions.md): `n = 4`, `k = 3`,
`R = 2`, `Δ = 1`. A slot-1 block, three exact slot-1 HEADs, the early cache at
`e_1 = 6`, two acks, the PC, the outputs, reconcile, and the gate at `d_1 = 10`.
Every check is `decide` (no `native_decide`). -/

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
/-- The named proposal of `B1`: no carried HEADs, rows or PC. -/
def N1 : NamedProposal 4 := .node .genesis 1 ⟨1⟩ b1.body [] [] [] none
def w1 : Wire 4 := ⟨.proposer 1, .proposal N1⟩

/-- [helper] A state at a new time (no clock step runs). -/
def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }
/-- A slot-1 HEAD of seat `i` on `b1`. -/
def hv (i : Fin 4) : Wire 4 := ⟨.seat (.head 1) i, .head b1.root⟩
/-- A slot-1 exact ack of seat `i` on `b1`. -/
def ak (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 1) i, b1⟩
def akWire (i : Fin 4) : Wire 4 := ⟨.seat (.ack 1) i, .ack b1⟩
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
/-- The ticks `z_1 = 7`, `8`, `q_1 = 9`, `d_1 = 10`. -/
def st10 : State pT.n := [(7 : Time), 8, 9, 10].foldl (clock pT) stA

/-- The block is admitted: the erased tree, the FG tree, F unchanged. -/
theorem block_admitted : st4.base.blocks = [.genesis, b1] ∧ st4.fg.TF = {.genesis, B1} ∧
    st4.fg.F = .genesis ∧ wellFormed pT w1 = true := by decide +kernel

/-- The input check of an ack: an exact ack on a slot-1 block; genesis is refused. -/
theorem ack_wellFormed : wellFormed pT (akWire 0) = true ∧
    wellFormed pT ⟨.seat (.ack 1) 0, .ack .genesis⟩ = false ∧
    wellFormed pT ⟨.seat (.ack 2) 0, .ack b1⟩ = false := by decide +kernel

/-- Three exact timely HEADs give `N(1, b1) = 3 ≥ q_N = 3`; the trigger names `b1`. -/
theorem n_holds : nCount st6 1 b1 = 3 ∧ nQuorum 4 = 3 ∧ ackTarget? pT st6 1 = some b1 ∧
    ackTarget? pT st5 1 = none := by decide +kernel

/-- One ack forms no PC; two acks form `PC(1, b1)` (`q_A = 2`). -/
theorem pc_formed : pcQuorum 4 = 2 ∧ latestPC (process pT st6 (akWire 0)) = none ∧
    stA.ackPool = [ak 0, ak 1] ∧ stA.pcs = [pc1] ∧ latestPC stA = some pc1 ∧
    pcAt stA 1 = some pc1 := by decide +kernel

/-- A third ack does not change the PC (never revoked, first `q_A` seats). -/
theorem pc_stable : (process pT stA (akWire 2)).pcs = [pc1] := by decide +kernel

/-- The available output takes the PC target before the gate (`S = genesis`),
also when `S` conflicts with it; the strong output is the target. -/
theorem available_floor : stA.base.stableRecord = .genesis ∧ confirmed stA = b1 ∧
    strong stA = b1 ∧ stable stA = b1 ∧
    confirmed { stA with base := { stA.base with stableRecord := b1' } } = b1 ∧
    confirmed st6 = .genesis := by decide +kernel

/-- Reconcile drops a PC that conflicts with F, keeps the ack pool, and the
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

/-- The label code separates the three constructors (small slots). -/
theorem encLabel_small : ∀ s < 6, ∀ s' < 6,
    encLabel (.head s) ≠ encLabel (.ack s') ∧ encLabel (.head s) ≠ encLabel .fg ∧
    encLabel (.ack s') ≠ encLabel .fg ∧
    (encLabel (.head s) = encLabel (.head s') → s = s') ∧
    (encLabel (.ack s) = encLabel (.ack s') → s = s') := by decide +kernel

/-- The label code is injective. -/
theorem encLabel_injective : Function.Injective encLabel := by
  intro a b h
  cases a <;> cases b
  all_goals
    first
    | rfl
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); omega)
    | (have h' := epair_inj (show epair _ _ = epair _ _ from h); rw [h'.2])

#print axioms gate_saves
#print axioms encLabel_injective

end AvailableChain.PCSA.Tests
end
