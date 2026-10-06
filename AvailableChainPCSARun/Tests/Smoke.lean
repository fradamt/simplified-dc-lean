module
public import AvailableChainPCSARun.Model.Protocol

@[expose] public section

/-! PC-SA M1 run smoke test: the ack duty at `e_s` and its payload
(pcsa34-v2-delta (5) check (i)). The fixtures repeat the store smoke test
(`AvailableChainPCSA/Tests/Smoke.lean`): a test imports only its own library
(check-layers TEST-SCOPE, TEST-USE). -/

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
def ak (i : Fin 4) : AckWire 4 := ⟨.seat (.ack 1) i, b1.root⟩
def akWire (i : Fin 4) : Wire 4 := ⟨.seat (.ack 1) i, .ack b1.root⟩
/-- `B1` at `t_1 = 4`; three exact HEADs at `v_1 = 5`; the tick at `e_1 = 6`;
two acks. -/
def st5 : State pT.n :=
  [hv 0, hv 1, hv 2].foldl (process pT) (atTime (process pT (atTime {} 4) w1) 5)
def st6 : State pT.n := clock pT st5 6
/-- Three HEADs stamped at `e_1 = 6` (not timely); the tick at 6. -/
def st6late : State pT.n :=
  clock pT ([hv 0, hv 1, hv 2].foldl (process pT) (atTime (process pT (atTime {} 4) w1) 6)) 6
def stA : State pT.n := [akWire 0, akWire 1].foldl (process pT) st6

/-- (i) At `e_1 = 6 = a_0` the duties are the FG action of round 0 and the ack
of slot 1 (`R = 2`: the action of round `r` is at `e_{rR+1}`); at `e_2 = 10`
the ack alone; at `e_3 = 14 = a_1` the FG action of round 1 and the ack of
slot 3. The HEAD action is never due at `e_s`. -/
theorem duties_early : duties pT (SA.earlyTime pT.toParams 1) = [.fgAction 0, .ackAction 1] ∧
    duties pT (SA.earlyTime pT.toParams 2) = [.ackAction 2] ∧
    duties pT (SA.earlyTime pT.toParams 3) = [.fgAction 1, .ackAction 3] ∧
    RunDuty.headAction 1 ∉ duties pT 6 := by
  decide +kernel

/-- The ack of slot `s` is due at `e_s` for every `p` and `s`, and at no other
time (A6: one ack action per slot; `duties_nodup` gives one per tick). -/
theorem ack_due (p : Params) (s : Slot) :
    RunDuty.ackAction s ∈ duties p (SA.earlyTime p.toParams s) :=
  (duties_spec p _ _).mpr rfl
theorem ack_once (p : Params) (s : Slot) (t : Time) :
    RunDuty.ackAction s ∈ duties p t ↔ SA.earlyTime p.toParams s = t :=
  duties_spec p _ t

/-- At `e_1` the ack duty sends the exact ack on the root of `b1`; with late
HEADs it sends nothing. -/
theorem ack_sent :
    act pT unitCodec ⟨st6, RecordOnce.initial⟩ (.ackAction 1) () = some (.ack b1.root) ∧
    act pT unitCodec ⟨st6late, RecordOnce.initial⟩ (.ackAction 1) () = none := by
  decide +kernel

/-- The sent ack decodes to the ack input and is pooled on delivery. -/
theorem ack_roundtrip :
    (toWire pT (ofAck pT (ak 0))).decode = some (.ack 1 0 b1.root) ∧
    processedS pT stA (ofAck pT (ak 0)) = true ∧
    processedS pT st6 (ofAck pT (ak 0)) = false := by
  decide +kernel

#print axioms ack_sent

end AvailableChain.PCSA.Run.Tests
end
