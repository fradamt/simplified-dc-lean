module
public import AvailableChainKitFG.HeightCoreDef
public import AvailableChainKitFG.NoEarlyMixed
public import AvailableChainKitFG.RowHistory

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- A crossing before maturity justifies the entry through the bridge. -/
theorem no_mixed_cross_before_maturity_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {U X : FGBlock V} (y : Height)
    (hX : X ≠ .genesis)
    (hUX : FGBlock.Preceq U X.parent)
    (hU : (v U).h = y)
    (hentry : (v U).T_h = U)
    (hparent : (v X.parent).h = y)
    (hearly : X.slot < U.slot + cfg.timeoutDelay)
    (hcross : (v X).h = y + 1) :
    (v X).J = U ∧ (v X).h_j = y := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hU hentry hparent hcross ⊢
  exact no_mixed_cross_before_maturity E cfg y hX hUX hU hentry hparent hearly hcross

/-- The bridge preserves the first height crossing edge. -/
theorem first_height_crossing_edge_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {D P : FGBlock V} (y : Height)
    (hDP : FGBlock.Preceq D P)
    (hD : (v D).h = y)
    (hP : y < (v P).h) :
    ∃ C : FGBlock V,
      C ≠ .genesis ∧
      FGBlock.Preceq D C.parent ∧
      FGBlock.Preceq C P ∧
      (v C.parent).h = y ∧
      (v C).h = y + 1 := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hD hP ⊢
  exact first_height_crossing_edge E cfg y hDP hD hP

/-- A crossing retains an honest matching row under the faulty-weight bound. -/
theorem crossing_honest_matching_row_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (faulty : Finset V) {C : FGBlock V} (y : Height)
    (hC : C ≠ .genesis)
    (hparent : (v C.parent).h = y)
    (hcross : (v C).h = y + 1)
    (hcap : E.weightOf faulty < E.q) :
    ∃ (W : FGBlock V) (a : Row V),
      FGBlock.Preceq W C ∧ a ∈ W.rows ∧
      a.signer ∉ faulty ∧
      a.height_pair.matchesEntry y (v C.parent).T_h.root = true := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hparent hcross ⊢
  exact crossing_honest_matching_row E cfg faulty y hC hparent hcross hcap

/-- Equal endpoint heights retain justification through the bridge. -/
theorem justification_eq_on_plateau_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {D P : FGBlock V}
    (hDP : FGBlock.Preceq D P)
    (hh : (v D).h = (v P).h) :
    (v P).J = (v D).J ∧ (v P).h_j = (v D).h_j := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hh ⊢
  exact justification_eq_on_plateau E cfg hDP hh

/-- A matching height occurrence retains its ancestry and height keys. -/
theorem height_occurrence_keys_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {u : Row V} {W P U : FGBlock V}
    {y : Height} {χ : Bool}
    (occ : u ∈ W.rows)
    (path : FGBlock.Preceq W P)
    (heightMatch :
      u.height_pair =
        .vote (v W.parent).h (v W.parent).T_h.root χ)
    (name : u.height_pair = .vote y U.root χ)
    (entry : (v U).h = y ∧ (v U).T_h = U)
    (endpoint : (v P).h = y) :
    FGBlock.Preceq U W.parent ∧
    (v W.parent).h = (v P).h ∧
    (v W.parent).T_h.root = (v P).T_h.root := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at heightMatch entry endpoint ⊢
  exact height_occurrence_keys E cfg occ path heightMatch name entry endpoint

end AvailableChain.KitFG
end
