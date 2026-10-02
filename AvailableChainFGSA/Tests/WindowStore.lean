module
public import AvailableChainFGSA.Proofs.WindowStore

public section

namespace AvailableChain.FGSA.Window.StoreTests

open AvailableChain.SimplexFG hiding derive acceptViable update_finality on_block

abbrev params : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

private def targets (h : Height) (X : FGBlock (Fin 4)) : List (Row (Fin 4)) :=
  [⟨0, .vote h X.root false, none⟩, ⟨1, .vote h X.root false, none⟩,
   ⟨2, .vote h X.root false, none⟩]

private def first : FGBlock (Fin 4) := .node .genesis 1 0 (targets 1 .genesis)
private def second : FGBlock (Fin 4) := .node first 2 0 (targets 2 first)
private def third : FGBlock (Fin 4) := .node second 3 0 (targets 3 second)
private def olderFinality : FGBlock (Fin 4) := .node third 4 0
  [⟨0, .empty, some ⟨2, first.root⟩⟩, ⟨1, .empty, some ⟨2, first.root⟩⟩,
   ⟨2, .empty, some ⟨2, first.root⟩⟩]

private def before : SimplexFG.Store (Fin 4) :=
  [first, second, third].foldl (on_block params 2) SimplexFG.Store.init

set_option maxRecDepth 8192
set_option exponentiation.threshold 8192

example : params.E.q = 3 ∧ ∀ i, params.E.weight i = 1 := by decide

/-- The older pair remains in the window below the latest justification. -/
example : (derive params 2 third).W = [⟨2, first, ∅⟩, ⟨3, second, ∅⟩] ∧
    before.F = .genesis ∧ before.J = second ∧
    FGBlock.Preceq first before.J ∧ first ≠ before.J := by decide +kernel

/-- A reachable store accepts the older entry; the old store step keeps genesis. -/
example : (on_block params 2 before olderFinality).F = first ∧
    (on_block params 2 before olderFinality).J = second ∧
    (SimplexFG.on_block params.E params.cfg before olderFinality).F = .genesis := by
  decide +kernel

/-- Duplicate and missing-parent refusals leave the whole store unchanged. -/
example : on_block params 2 before second = before ∧
    on_block params 2 SimplexFG.Store.init second = SimplexFG.Store.init := by decide +kernel

private def sameSlot : FGBlock (Fin 4) := .node third 3 0 []
private def conflict : FGBlock (Fin 4) := .node .genesis 5 1 []

/-- Parent-slot and incompatible-finality refusals leave the store unchanged. -/
example : on_block params 2 before sameSlot = before ∧
    on_block params 2 (on_block params 2 before olderFinality) conflict =
      on_block params 2 before olderFinality := by decide +kernel

/-- Compare one update from exactly the same input, including the inserted block. -/
example : let st := { before with TF := insert olderFinality before.TF }
    (update_finality params 2 st olderFinality).h_max =
      (SimplexFG.update_finality params.E params.cfg st olderFinality).h_max ∧
    ((update_finality params 2 st olderFinality).h_j,
      (update_finality params 2 st olderFinality).J) =
      ((SimplexFG.update_finality params.E params.cfg st olderFinality).h_j,
        (SimplexFG.update_finality params.E params.cfg st olderFinality).J) := by decide +kernel

end AvailableChain.FGSA.Window.StoreTests
end
