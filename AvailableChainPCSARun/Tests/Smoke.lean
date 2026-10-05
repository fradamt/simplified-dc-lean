module
public import AvailableChainPCSARun.Model.Protocol

@[expose] public section

/-! PC-SA M1 run smoke test: the ack duty at `e_s` and its payload. The
fixtures repeat the store smoke test (`AvailableChainPCSA/Tests/Smoke.lean`):
a test imports only its own library (check-layers TEST-SCOPE, TEST-USE). -/

namespace AvailableChain.PCSA.Run.Tests

open AvailableChain.SimplexFG

/-- The finite digest table over the PC-SA digest input. -/
def digestTable : List (DigestInput 4 × BlockId) :=
  [ (⟨genesisRoot, 1, 0, [], [], [], none⟩, ⟨1⟩) ]

/-- Positive IDs; 4095 is outside the finite table. -/
def fixtureDigest (d : FGSA.DigestInput 4) : BlockId :=
  ((digestTable.find? (fun e => e.1.toFGSA == d)).map Prod.snd).getD ⟨4095⟩

/-- The test parameters: Δ = 1, n = 4, k = 3, R = 2, δ_t = 1. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 3, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fixtureDigest }

def B1 : FGBlock (Fin 4) := .node .genesis 1 ⟨1⟩ (packInner 0 ([] : List (RowWire 4))) []
def b1 : Block := eraseFG B1
def N1 : NamedProposal 4 := .node .genesis 1 ⟨1⟩ b1.body [] [] [] none
def w1 : Wire 4 := ⟨.proposer 1, .proposal N1⟩
def atTime (st : State pT.n) (t : Time) : State pT.n :=
  { st with base := { st.base with now := t } }
def hv (i : Fin 4) : Wire 4 := ⟨.seat (.head 1) i, .head b1.root⟩
def ak (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 1) i, b1⟩
def akWire (i : Fin 4) : Wire 4 := ⟨.seat (.ack 1) i, .ack b1⟩
/-- `B1` at `t_1 = 4`; three exact HEADs at `v_1 = 5`; the tick at `e_1 = 6`;
two acks. -/
def st5 : State pT.n :=
  [hv 0, hv 1, hv 2].foldl (process pT) (atTime (process pT (atTime {} 4) w1) 5)
def st6 : State pT.n := clock pT st5 6
def stA : State pT.n := [akWire 0, akWire 1].foldl (process pT) st6

/-- At `e_1 = 6 = a_0` the duties are the FG action of round 0 and the ack of
slot 1; the HEAD action is not due. -/
theorem duties_e1 : duties pT 6 = [.fgAction 0, .ackAction 1] ∧
    RunDuty.ackAction 1 ∈ duties pT 6 ∧ RunDuty.headAction 1 ∉ duties pT 6 := by
  decide +kernel

/-- The ack of slot `s` is due at `e_s` for every `p` and `s`. -/
theorem ack_due (p : Params) (s : Slot) :
    RunDuty.ackAction s ∈ duties p (SA.earlyTime p.toParams s) :=
  (duties_spec p _ _).mpr rfl

/-- At `e_1` the ack duty sends the exact ack on `b1`; before the early cache
it sends nothing. -/
theorem ack_sent :
    act pT unitCodec ⟨st6, RecordOnce.initial⟩ (.ackAction 1) () = some (.ack b1) ∧
    act pT unitCodec ⟨st5, RecordOnce.initial⟩ (.ackAction 1) () = none := by
  decide +kernel

/-- The sent ack decodes to the ack input and is pooled on delivery. -/
theorem ack_roundtrip :
    (toWire pT (ofAck pT (ak 0))).decode = some (.ack 1 0 b1) ∧
    processedS pT stA (ofAck pT (ak 0)) = true ∧
    processedS pT st6 (ofAck pT (ak 0)) = false := by
  decide +kernel

#print axioms ack_sent

end AvailableChain.PCSA.Run.Tests
end
