module
public import AvailableChainFGSAProofs.Proofs.Healing.Reset -- shake: keep (R1–R3 tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (INLINE producer)

set_option linter.privateModule false

public section

/-! Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 T.
DC: SAME discharge the actual source producer and test all reset field support.
R1/R2 application tests are STOPPED: the HG.5 contract has no public eliminator.
The numeric tests cover both allowance choices and integer subtraction. -/

namespace AvailableChain.FGSA.Run.Tests.HealingReset
open AvailableChain.SimplexFG

private theorem reset_emittedName (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    (ha : HonestRowAt p c E rho j x r a) (he : namedEntry a.payload.height_pair = some e) :
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = ((heightView p C).h, (heightView p C).T_h.root) ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
  obtain ⟨C, G, hC, hh, _, hG, hCG, hf⟩ :=
    sourceDiscipline_emittedName p c E rho hs ha he
  refine ⟨C, G, hC, ?_, hG, hCG, hf⟩
  rw [heightView_eq_simplex p]
  exact hh

-- All frozen H0Reset fields are built from the exported first-row contract.
-- This support test does not replace the stopped HG.5-to-first-row derivation.
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF deadline : Time}
    (hset : HealingSet p c E rho G ΔF)
    (firstRow : FirstHeightRowBy p c E rho (resetCutFrontier p c E rho + 1) deadline) :
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar ≤ deadline :=
  healing_reset_fields p c E rho
    (reset_emittedName p c E rho hset.base.valid.toScheduleWellFormed) hset firstRow

private def resetParams (k : Nat) (hk : 2 ≤ k) : Params where
  Δ := 1
  n := 4
  k := k
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := hk
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide

-- The short-lease branch attains the minimum: 339 = 3·12 + 159 + 144.
example : let p := resetParams 2 (by decide)
    B'_resetF p 6 8 = 339 ∧
    (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + B_cF p 6 8 (ρ₁ p 8)) = 159 ∧
    (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + D_cF p (ρ₁ p 8)) = 144 ∧
    B'_resetF p 6 8 = 3 * P p + (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + B_cF p 6 8 (ρ₁ p 8)) +
      (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + D_cF p (ρ₁ p 8)) := by decide

-- k > 2R+1 selects the two-lease allowance.
example : let p := resetParams 8 (by decide)
    ¬ p.k ≤ 2 * p.R + 1 ∧
    B'_resetF p 6 12 = 3 * P p +
      (E_gF p 6 12 (ρΓ p 12) + E_jF p 6 12 (ρΓ p 12) + B_cF p 6 12 (ρΓ p 12)) +
      (E_gF p 6 12 (ρΓ p 12) + E_jF p 6 12 (ρΓ p 12) + D_cF p (ρΓ p 12)) := by decide

-- A negative allowance tests Int subtraction without Nat truncation.
example : let p := resetParams 2 (by decide)
    B_resetF p 6 8 (-100) = -209 ∧
    B_resetF p 6 8 (-100) = 3 * P p + (E_gF p 6 8 (-100) + E_jF p 6 8 (-100) + B_cF p 6 8 (-100)) +
      (E_gF p 6 8 (-100) + E_jF p 6 8 (-100) + D_cF p (-100)) := by decide

-- The strict-cut step reaches the strict reset deadline with the chosen minimum.
example : let p := resetParams 2 (by decide)
    ∃ ρbar, (ρbar = ρΓ p 8 ∨ (ρbar = ρ₁ p 8 ∧ p.k ≤ 2 * p.R + 1)) ∧
      45 + (E_gF p 6 8 ρbar + E_jF p 6 8 ρbar + B_cF p 6 8 ρbar) +
        (E_gF p 6 8 ρbar + E_jF p 6 8 ρbar + D_cF p ρbar) < 10 + B'_resetF p 6 8 :=
  healing_reset_budget_lt _ 8 6 10 45 (by decide)

-- The same arithmetic holds for every integer allowance.
example (p : Params) (G ΔF ρbar : Time) :
    B_resetF p ΔF G ρbar = 3 * P p +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) := healing_reset_budget_sum p G ΔF ρbar

end AvailableChain.FGSA.Run.Tests.HealingReset
end
