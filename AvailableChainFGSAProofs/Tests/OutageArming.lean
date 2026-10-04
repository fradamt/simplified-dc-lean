module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingGate -- shake: keep (slow admission)
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingMain -- shake: keep (axiom lines)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
open Gen.Pure

/-! Plan O-ARM §10 boundary examples. -/

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan O-ARM §2, §10. Class (iii). DC: INTENTIONAL.
A cut at a gate time, b₀ = d(l): the cut label is `l` itself, the batch
receipt deadline e(l + 1) equals the cut, and the pending gate is strictly
later. -/
theorem cut_at_gate (p : Params) (l : Slot) :
    let b₀ := SA.gateTime p.toParams l
    ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat = l ∧
      SA.earlyTime p.toParams (l + 1) = b₀ ∧ b₀ < SA.gateTime p.toParams (l + 1) := by
  intro b₀
  have h6 : 6 * p.Δ ≤ b₀ := by
    change 6 * p.Δ ≤ 4 * p.Δ * (l : Time) + 6 * p.Δ
    have := p.deltaPos
    have : (0 : Time) ≤ 4 * p.Δ * (l : Time) := by positivity
    linarith
  have hle := (arming_le_label p b₀ h6 l).mp le_rfl
  have hlt : ¬ l + 1 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat := fun h =>
    absurd ((arming_le_label p b₀ h6 (l + 1)).mpr h)
      (not_le.mpr ((arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)))
  refine ⟨le_antisymm (Nat.le_of_lt_succ (not_le.mp hlt)) hle, arming_early_next p l,
    (arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)⟩

/-- Plan O-ARM §10. Class (iii). DC: INTENTIONAL.
Δ = 1 and b₀ = d(2) = 14: the cut label is 2. -/
example : (((14 : Int) - 6 * 1) / (4 * 1)).toNat = 2 := by decide

/-- Plan O-ARM §2, §10. Class (iii). DC: INTENTIONAL.
The first possible origin s = 1. The fast lag puts the pending label at
least at 3; the slow window labels are between 2 and `l`. -/
example (p : Params) (T b₀ : Time) (hs : SA.gateTime p.toParams 1 ≤ T)
    (hlag : T + 4 * p.Δ ≤ b₀) : 3 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 :=
  arming_fast_gap p 1 T b₀ hs hlag

example (p : Params) (l a : Nat) (hgap : 1 + p.k ≤ l + 1) (ha : a < p.k - 1) :
    2 ≤ l + 1 - (a + 1) ∧ l + 1 - (a + 1) ≤ l :=
  let h := arming_slow_window_label p 1 l a le_rfl hgap ha
  ⟨h.2.2, h.2.1⟩

/-- Plan O-ARM §10. Class (iii). DC: INTENTIONAL.
A pending gate after the horizon: no actual gate tick exists, so field 9 is
vacuous, and the pre-pending fields alone cover every read up to the horizon. -/
theorem pending_after_horizon {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ b₁ : Time} {B : Block}
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hhor : rho.horizon < SA.gateTime p.toParams (l + 1)) :
    (∀ i y, ¬ IsGateTick p c rho i y (l + 1)) ∧
    ∀ y t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t → t ≤ rho.horizon →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y) := by
  refine ⟨fun i y hi => ?_, fun y t hy hlt ht => ?_⟩
  · have h := (hs.in_horizon _ (List.mem_of_getElem? hi)).2
    exact absurd (lt_of_le_of_lt h hhor) (lt_irrefl _)
  · have htd := lt_of_le_of_lt ht hhor
    have h0 : 0 ≤ t := le_trans (by
      rw [arming_gate_eq]
      have := p.deltaPos
      positivity) hlt
    exact ⟨hc.pending_cover y t hy hlt htd ht, hc.pending_compat y t hy h0 htd ht⟩

/-- Plan O-ARM §6.4, §10. Class (iii). DC: INTENTIONAL.
Slow mode below τ: the slow test alone admits the release level. -/
example (p : Params) {n : Nat} (v : GridCO.State n .root) (r : Slot) (B : Block)
    (_hbelow : SA.prefixSupport p.toParams v r B < SA.releaseThreshold p.toParams)
    (hslow : GridCO.slowEligible p.toParams.engine v r B = true) :
    SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine n .root v r B :=
  arming_admission p v r B (Or.inr hslow)

#print axioms cut_at_gate
#print axioms pending_after_horizon
#print axioms ArmingData_def
#print axioms fast_arming
#print axioms slow_arming
#print axioms pending_gate_lease_or_F

end AvailableChain.FGSA.Run.Tests.OutageArming
