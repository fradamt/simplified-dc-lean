module
public import AvailableChainFGSA.Model.Objects

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

end AvailableChain.FGSA.Tests
end
