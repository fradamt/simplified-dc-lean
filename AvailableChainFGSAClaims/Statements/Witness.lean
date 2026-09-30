module
public import AvailableChainFGSA.Model.Objects

@[expose] public section

/-! F0.5: the common witness of 21 H.22 and 22 §1.
F0.8b adds muOf, high, H0 and tstarOf below these declarations. -/

namespace AvailableChain.FGSA.Run

/-- The common tuple (21 H.22:3001–3003; 22 §1:183–185).
`b` is `sStar`; μ is a run function, not a field (21:3006–3009; 22:188–191).
The H0 constraints on these data are added in F0.8b. -/
structure HealingWitness where
  /-- First action round at or after GST (21 H.22:3046–3047; 22 §1:228–229). -/
  rG : Nat
  /-- Inclusive cut a_(r_G+2) (21 H.22:3047; 22 §1:229). -/
  u₀ : Time
  /-- Maximum honest height at u₀ (21 H.22:3048; 22 §1:230). -/
  M : Nat
  /-- First round with an honest row at height M+1 (21 H.22:3051–3052; 22 §1:233–234). -/
  rStar : Nat
  /-- Slot r*R, also the label b (21 H.22:3052; 22 §1:234). -/
  sStar : Slot
  /-- Actual fresh source of that row (21 H.22:3052–3053; 22 §1:234–235). -/
  CStar : Block
  /-- First honest proposal slot at least s*+2 (21 H.22:3054; 22 §1:236). -/
  u : Slot
  /-- Block of that honest proposal (21 H.22:3054–3055; 22 §1:236–237). -/
  QStar : Block

/-- Healing starts at d_u (21 H.22:3054; 22 §1:236). -/
def tstar (p : Params) (w : HealingWitness) : Time := SA.gateTime p.toParams w.u

end AvailableChain.FGSA.Run
end
