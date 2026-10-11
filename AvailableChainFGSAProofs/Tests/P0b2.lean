module
public import AvailableChainFGSA.Proofs.WindowInvariant
public import AvailableChainKitFG.WindowInvariant

set_option linter.privateModule false

namespace AvailableChain.FGSA.Tests.P0b2

open AvailableChain.SimplexFG
open AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def B1 : FGBlock (Fin p.n) :=
  .node .genesis 1 ⟨10⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def B2 : FGBlock (Fin p.n) :=
  .node B1 2 ⟨11⟩ 0 [⟨0, .vote 2 B1.root false, none⟩]
private def B3 : FGBlock (Fin p.n) :=
  .node B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]

/-- The unchanged FG-SA premises supply the full refinement record. -/
private theorem complete_refinement (p : Params) (K : Nat) (hK : 2 ≤ K) :
    HeightFoldRefinement p.E p.cfg FGSA.Window.projectHeight FGSA.Window.initial
      (FGSA.Window.transition p K) (FGSA.Window.derive p K) where
  initial_height := (FGSA.Window.heightRefinement p K hK).initial_height
  derive_genesis := (FGSA.Window.heightRefinement p K hK).derive_genesis
  derive_node := (FGSA.Window.heightRefinement p K hK).derive_node
  step_height := (FGSA.Window.heightRefinement p K hK).step_height

private theorem height_projection (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) :
    FGSA.Window.projectHeight (FGSA.Window.derive p K B) =
      KitFG.Window.projectHeight (SimplexFG.Window.derive p.E p.cfg K B) :=
  (FGSA.Window.windowHeightBridge p K hK B).trans
    (KitFG.Window.windowHeightBridge p.E p.cfg K hK B).symm

/-- The same non-genesis finalization occurs in both folds, with the same retained entry. -/
private theorem inhabited_adapter :
    (FGSA.Window.derive p 2 B3).F = B1 ∧
    (SimplexFG.Window.derive p.E p.cfg 2 B3).F = B1 ∧
    (FGSA.Window.derive p 2 B3).W = [⟨3, B2, ∅⟩] ∧
    (SimplexFG.Window.derive p.E p.cfg 2 B3).W = [⟨3, B2, ∅⟩] := by
  decide +kernel

private theorem closed_cover :
    FGBlock.Preceq B1 (FGSA.Window.derive p 2 B3).F ∧
      2 ≤ (FGSA.Window.derive p 2 B3).h_F := by
  exact FGSA.Window.window_finality_of_cover p 2 (by decide)
    B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]
    ⟨2, B1, ∅⟩ (by decide +kernel) {0} (by unfold Electorate.IsQuorum; decide +kernel) (by
      intro i hi
      have hi' : i = 0 := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨_, List.mem_singleton_self _, rfl, rfl⟩)

/-- Every field of the existing height law record remains available. -/
private theorem complete_height (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGHeightLaws p.E (fun B => FGSA.Window.projectHeight (FGSA.Window.derive p K B)) where
  one_le_h := (FGSA.Window.windowHeightLaws p K hK).one_le_h
  h_mono := (FGSA.Window.windowHeightLaws p K hK).h_mono
  node_cases := (FGSA.Window.windowHeightLaws p K hK).node_cases
  entry_preceq := (FGSA.Window.windowHeightLaws p K hK).entry_preceq
  entry_same_height := (FGSA.Window.windowHeightLaws p K hK).entry_same_height
  entry_idem := (FGSA.Window.windowHeightLaws p K hK).entry_idem
  entry_plateau := (FGSA.Window.windowHeightLaws p K hK).entry_plateau
  justified_preceq_entry := (FGSA.Window.windowHeightLaws p K hK).justified_preceq_entry
  justified_below_height := (FGSA.Window.windowHeightLaws p K hK).justified_below_height
  target_sub_progress := (FGSA.Window.windowHeightLaws p K hK).target_sub_progress
  target_origin := (FGSA.Window.windowHeightLaws p K hK).target_origin
  progress_origin := (FGSA.Window.windowHeightLaws p K hK).progress_origin
  height_crossing := (FGSA.Window.windowHeightLaws p K hK).height_crossing
  justification_certificate := (FGSA.Window.windowHeightLaws p K hK).justification_certificate

#print axioms complete_refinement
#print axioms height_projection
#print axioms inhabited_adapter
#print axioms closed_cover
#print axioms complete_height

end AvailableChain.FGSA.Tests.P0b2
