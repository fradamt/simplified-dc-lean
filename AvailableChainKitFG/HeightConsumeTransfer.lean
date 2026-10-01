module
public import AvailableChainKitFG.HeightCoreDef
public import AvailableChainKitFG.HeightConsume

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Target coverage transfers through the one-step height bridge. -/
theorem transition_target_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (hb : HeightStepBridge E cfg π step)
    (w : Ω) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (π w).target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote (π w).h (π w).T_h.root false) :
    (π (step w B rs)).h = (π w).h + 1 ∧
    (π (step w B rs)).J = (π w).T_h ∧
    (π (step w B rs)).h_j = (π w).h := by
  let σ : ChainState V :=
    { L := (π w).L, s := (π w).s, h := (π w).h, T_h := (π w).T_h,
      target_participation := (π w).target_participation, progress := (π w).progress,
      h_j := (π w).h_j, J := (π w).J, F := .genesis, h_F := 0, finalize := ∅ }
  have hσ : π w = heightOf σ := rfl
  rw [hb w σ B rs hσ]
  exact transition_target_of_cover E cfg σ B rs S hS hcover

/-- Mature progress coverage transfers through the one-step height bridge. -/
theorem transition_progress_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (hb : HeightStepBridge E cfg π step)
    (w : Ω) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (π w).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (π w).h (π w).T_h.root = true)
    (hmature : (π w).T_h.slot + cfg.timeoutDelay ≤ B.slot) :
    (π (step w B rs)).h = (π w).h + 1 := by
  let σ : ChainState V :=
    { L := (π w).L, s := (π w).s, h := (π w).h, T_h := (π w).T_h,
      target_participation := (π w).target_participation, progress := (π w).progress,
      h_j := (π w).h_j, J := (π w).J, F := .genesis, h_F := 0, finalize := ∅ }
  have hσ : π w = heightOf σ := rfl
  rw [hb w σ B rs hσ]
  exact transition_progress_of_cover E cfg σ B rs S hS hcover hmature

/-- Target coverage in a child transfers through the derive bridge. -/
theorem derive_target_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (p : FGBlock V) (s : Slot) (x : Nat)
    (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (v p).target_participation ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair = .vote (v p).h (v p).T_h.root false) :
    (v (.node p s x rs)).h = (v p).h + 1 ∧
    (v (.node p s x rs)).J = (v p).T_h ∧
    (v (.node p s x rs)).h_j = (v p).h := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hcover ⊢
  exact derive_target_of_cover E cfg p s x rs S hS hcover

/-- Mature progress coverage in a child transfers through the derive bridge. -/
theorem derive_progress_of_cover_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (p : FGBlock V) (s : Slot) (x : Nat)
    (rs : List (Row V)) (S : Finset V)
    (hS : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (v p).progress ∨
      ∃ a ∈ rs, a.signer = i ∧
        a.height_pair.matchesEntry (v p).h (v p).T_h.root = true)
    (hmature : (v p).T_h.slot + cfg.timeoutDelay ≤ s) :
    (v (.node p s x rs)).h = (v p).h + 1 := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hcover hmature ⊢
  exact derive_progress_of_cover E cfg p s x rs S hS hcover hmature

end AvailableChain.KitFG
end
