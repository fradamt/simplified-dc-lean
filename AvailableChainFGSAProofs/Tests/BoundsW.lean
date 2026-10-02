module
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (concrete examples and axiom audit commands)

public section

namespace AvailableChain.FGSA.Run

@[expose] def boundsWParams (R : Nat) (hR : 2 ≤ R) : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := R
  δt := 2 * R
  RLarge := hR

example : kappaF (boundsWParams 2 (by decide)) 2 = 2 := by decide
example : kappaF (boundsWParams 3 (by decide)) 6 = 3 := by decide
example : LivenessBoundW (boundsWParams 3 (by decide)) 6 := ⟨by decide⟩

/-- κ=R, and the row deadline equals the carrier time and the next opening. -/
example : ActionDeliveryBoundsW (boundsWParams 3 (by decide)) 6 1 :=
  action_delivery_boundsW _ _ _ (by decide) ⟨by decide⟩
example : (boundsWParams 3 (by decide)).actionTime 1 + 6 =
    carrierTimeW (boundsWParams 3 (by decide)) 6 1 := by decide
example : KernelBeforeNextActionW (boundsWParams 3 (by decide)) 6 1 :=
  kernel_before_next_actionW _ _ _ ⟨by decide⟩

example : betaF (boundsWParams 3 (by decide)) 6 = 12 ∧
    epsF (boundsWParams 3 (by decide)) 6 = 4 ∧
    carrierTimeW (boundsWParams 3 (by decide)) 6 1 = 24 ∧
    kernelDeadlineW (boundsWParams 3 (by decide)) 6 1 = 25 ∧
    W_W (boundsWParams 3 (by decide)) 6 1 = 49 := by decide

/-- The complete third numeric row of blueprint 21:1850–1863. -/
example : E_gF (boundsWParams 3 (by decide)) 6 8 25 = 56 ∧
    E_jF (boundsWParams 3 (by decide)) 6 8 25 = 52 ∧
    B_cF (boundsWParams 3 (by decide)) 6 8 25 = 51 ∧
    D_cF (boundsWParams 3 (by decide)) 25 = 36 ∧
    B_resetF (boundsWParams 3 (by decide)) 6 8 25 = 339 ∧
    BF (boundsWParams 3 (by decide)) 6 8 25 = 351 ∧
    B_H2F (boundsWParams 3 (by decide)) 6 8 = 381 ∧
    B_H1F (boundsWParams 3 (by decide)) 6 8 = 351 ∧
    B_HF (boundsWParams 3 (by decide)) 6 8 = 351 ∧
    B'_resetF (boundsWParams 3 (by decide)) 6 8 = 339 ∧
    B_bestF (boundsWParams 3 (by decide)) 6 8 1 = 351 := by decide

example : B_HF (boundsWParams 2 (by decide)) 2 8 = 295 ∧
    B_HF (boundsWParams 3 (by decide)) 2 8 = 343 := by decide

#print axioms kappaF_ceiling
#print axioms kappaF_eq_two_iff
#print axioms action_delivery_boundsW
#print axioms kernel_before_next_actionW
#print axioms B_HF_bounds
#print axioms B_bestF_le_healing
#print axioms B_HF_numeric_351

end AvailableChain.FGSA.Run
