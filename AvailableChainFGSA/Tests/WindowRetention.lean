module
public import AvailableChainFGSA.Proofs.WindowRetention

@[expose] public section

namespace AvailableChain.FGSA.Window.RetentionTests

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

abbrev retentionParams : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

def retentionTargets (h : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h X.root false, none⟩, ⟨1, .vote h X.root false, none⟩,
   ⟨2, .vote h X.root false, none⟩]

def retentionFirst : FGBlock (Fin 4) := .node .genesis 1 0 (retentionTargets 1 .genesis)
def retentionSecond : FGBlock (Fin 4) :=
  .node retentionFirst 2 0 (retentionTargets 2 retentionFirst)
def retentionThird : FGBlock (Fin 4) :=
  .node retentionSecond 3 0 (retentionTargets 3 retentionSecond)

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

/-- K = 2 retains the older key after one newer justification. -/
example : (derive retentionParams 2 retentionSecond).W =
    [⟨1, .genesis, ∅⟩, ⟨2, retentionFirst, ∅⟩] := by decide +kernel

example : ∃ d ∈ (derive retentionParams 2 retentionSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ (∅ : Finset (Fin 4)) ⊆ d.Q :=
  window_retained_of_scalar retentionParams 2 (by decide) retentionFirst retentionSecond
    (by decide +kernel) ⟨1, .genesis, ∅⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The birth-count corollary uses the one real child after the fresh key. -/
example : ∃ d ∈ (derive retentionParams 2 retentionSecond).W,
    d.j = 1 ∧ d.X = .genesis ∧ (∅ : Finset (Fin 4)) ⊆ d.Q := by
  apply window_retained_fresh_one_newer retentionParams 2 (by decide)
    retentionFirst retentionSecond (by decide +kernel) ⟨1, .genesis, ∅⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {retentionSecond} (by decide +kernel)
  intro C j X hAC hCP _
  by_cases hC : C = retentionSecond
  · exact Finset.mem_singleton.mpr hC
  · have hCA : FGBlock.Preceq C retentionFirst := preceq_parent_of_preceq_node hCP hC
    exact (hAC.2 (preceq_antisymm hAC.1 hCA)).elim

/-- Capacity removes the old key with no finality coverage. -/
example : (derive retentionParams 2 retentionThird).W =
      [⟨2, retentionFirst, ∅⟩, ⟨3, retentionSecond, ∅⟩] ∧
    (¬ ∃ d ∈ (derive retentionParams 2 retentionThird).W, d.j = 1 ∧ d.X = .genesis) ∧
    (derive retentionParams 2 retentionThird).h_F = 0 := by decide +kernel

def retentionLaterRows : List (Row (Fin 4)) :=
  [⟨0, .vote 3 retentionSecond.root false, some ⟨2, retentionFirst.root⟩⟩,
   ⟨1, .vote 3 retentionSecond.root false, some ⟨2, retentionFirst.root⟩⟩,
   ⟨2, .vote 3 retentionSecond.root false, some ⟨2, retentionFirst.root⟩⟩]
def retentionLater : FGBlock (Fin 4) := .node retentionThird 4 0 retentionLaterRows

/-- Later finality covers the evicted key through F and h_F. The key stays absent. -/
example : (¬ ∃ d ∈ (derive retentionParams 2 retentionLater).W,
      d.j = 1 ∧ d.X = .genesis) ∧
    1 ≤ (derive retentionParams 2 retentionLater).h_F ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) (derive retentionParams 2 retentionLater).F ∧
    (derive retentionParams 2 retentionLater).F = retentionFirst := by decide +kernel

def retentionCurrent : Row (Fin 4) :=
  ⟨0, .vote 3 retentionSecond.root false, some ⟨1, genesisRoot⟩⟩
def retentionStale : Row (Fin 4) :=
  ⟨1, .vote 2 retentionFirst.root false, some ⟨1, genesisRoot⟩⟩
def retentionMixed : FGBlock (Fin 4) :=
  .node retentionSecond 3 1 [retentionCurrent, retentionStale]

/-- Both R6W arms add bits to the same older entry. Both bodies pass R3. -/
example : heightMatch (derive retentionParams 2 retentionSecond) retentionCurrent = true ∧
    staleUseful (derive retentionParams 2 retentionSecond) retentionStale = true ∧
    (RowBody.ofRow retentionCurrent).valid = true ∧
    (RowBody.ofRow retentionStale).valid = true ∧
    (derive retentionParams 2 retentionMixed).W =
      [⟨1, .genesis, {1, 0}⟩, ⟨2, retentionFirst, ∅⟩] := by decide +kernel

def retentionReadyRows : List (Row (Fin 4)) :=
  [⟨0, .vote 4 retentionThird.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨1, .vote 4 retentionThird.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨2, .vote 4 retentionThird.root false, some ⟨1, genesisRoot⟩⟩,
   ⟨0, .vote 4 retentionThird.root false, some ⟨3, retentionSecond.root⟩⟩,
   ⟨1, .vote 4 retentionThird.root false, some ⟨3, retentionSecond.root⟩⟩,
   ⟨2, .vote 4 retentionThird.root false, some ⟨3, retentionSecond.root⟩⟩]
def retentionReady : FGBlock (Fin 4) := .node retentionThird 4 0 retentionReadyRows

/-- With K = 3, entries 1 and 3 are ready. Entry 2 has no finality QC,
but the selected descendant covers it. The new height-4 entry starts empty. -/
example : (certificateFolded retentionParams 3 retentionReady).W =
      [⟨1, .genesis, {2, 1, 0}⟩, ⟨2, retentionFirst, ∅⟩,
       ⟨3, retentionSecond, {2, 1, 0}⟩] ∧
    (derive retentionParams 3 retentionReady).h_F = 3 ∧
    (derive retentionParams 3 retentionReady).F = retentionSecond ∧
    FGBlock.Preceq retentionFirst (derive retentionParams 3 retentionReady).F ∧
    (derive retentionParams 3 retentionReady).W = [⟨4, retentionThird, ∅⟩] := by decide +kernel

def retentionPremature : Row (Fin 4) :=
  ⟨3, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩
def retentionBirthRows : List (Row (Fin 4)) :=
  retentionTargets 1 .genesis ++ [retentionPremature]
def retentionBirth : FGBlock (Fin 4) := .node .genesis 1 0 retentionBirthRows

/-- STOP 4: rowValidW omits R3. All rows pass it on the parent state,
but the exact row carried at birth has no bit in the retained new entry. -/
example : (∀ a ∈ retentionBirthRows, rowValidW (derive retentionParams 2 .genesis)
      ⟨.seat .fg a.signer, .vote (RowBody.ofRow a)⟩ = true) ∧
    retentionPremature ∈ retentionBirth.rows ∧
    retentionPremature.finality_pair = some ⟨1, genesisRoot⟩ ∧
    (derive retentionParams 2 retentionBirth).W = [⟨1, .genesis, ∅⟩] ∧
    retentionPremature.signer ∉ (∅ : Finset (Fin 4)) ∧
    (RowBody.ofRow retentionPremature).valid = false := by decide +kernel

end AvailableChain.FGSA.Window.RetentionTests
end
