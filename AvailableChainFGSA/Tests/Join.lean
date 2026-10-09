module
public import AvailableChainFGSA.Proofs.Join

@[expose] public section

namespace AvailableChain.FGSA.JoinTests

abbrev p : Params :=
  { Δ := 1, n := 3, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun _ => ⟨99⟩ }

def storeAt (w t : Time) : State 3 :=
  { restartTime := some w, base := { GridCO.initial 3 .root with now := t } }

/-- Equality joins; one unit later waits for one more slot. -/
theorem join_boundary : joinedNow p (storeAt 4 8) = true ∧ joinedNow p (storeAt 5 8) = false ∧
    joinedNow p (storeAt 5 12) = true := by decide +kernel

/-- Integer subtraction at slot zero and the initial epoch. -/
theorem join_slot_zero : joinedNow p (storeAt 0 0) = false ∧ joinedNow p (storeAt (-4) 0) = true ∧
    joinedNow p (initial 3) = true := by decide +kernel

def lockedStore : State 3 :=
  { storeAt 5 4 with base := { (storeAt 5 4).base with
    obligations := [(.genesis, 2, 20), (.genesis, 2, 4)] } }

/-- The release-time tick keeps the live lock and expires the other lock. -/
theorem release_unjoined : (clockPre p lockedStore 5).base.obligations = [(.genesis, 2, 20)] ∧
    (clockPre p lockedStore 5).base.releaseSnapshots = [] := by decide +kernel

/-- A suppressed gate saves empty data, with no new lock or output write. -/
theorem gate_unjoined : GridCO.savedGenuine (gateStep p lockedStore 0).base 0 = some none ∧
    (gateStep p lockedStore 0).fastWrite = [(0, [])] ∧
    (gateStep p lockedStore 0).base.obligations = lockedStore.base.obligations ∧
    (gateStep p lockedStore 0).base.stableRecord = lockedStore.base.stableRecord ∧
    (gateStep p lockedStore 0).fg = lockedStore.fg := by decide +kernel

end AvailableChain.FGSA.JoinTests
end
