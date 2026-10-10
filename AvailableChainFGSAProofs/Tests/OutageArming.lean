module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Outage.Arming
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingBatch

public section

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
    (_hbelow : SA.Root.prefixSupport p.toParams v r B < SA.releaseThreshold p.toParams)
    (hslow : GridCO.slowEligible p.toParams.engine v r B = true) :
    SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine n .root v r B :=
  by
    simp only [GridCO.admissionLevels]
    change SA.releaseThreshold p.toParams ∈
      (if decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v r B) ||
        GridCO.slowEligible p.toParams.engine v r B then [SA.releaseThreshold p.toParams] else [])
    simp [hslow]

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.cut_at_gate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.pending_after_horizon
#print axioms AvailableChain.FGSA.Run.ArmingData_def
/-- Restart clears saved rows. A prior epoch cannot supply the slow window. -/
theorem saved_rows_erased_at_restart (p : Params) (st : State p.n) (w : Time) (s : Slot) :
    GridCO.savedGenuine (acRestart p st w).base s = none := by
  unfold GridCO.savedGenuine
  rw [acRestart_genuine]
  rfl

/-- Same-time wake precedes the gate's read. The strict-before read is insufficient. -/
theorem gate_reads_after_wake {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : IsGateTick p c rho i x s) :
    storeAt p c E rho i x = (V2.D.Run.stateAfterRestartsAt E rho
      (SA.gateTime p.toParams s) x).st := by
  exact congrArg Node.st (V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hs hi)

/-- Full sleep excludes the old all-honest tick conclusion. -/
theorem asleep_has_no_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) {x : V} {t : Time} (ha : E.awake x t = false) :
    V2.Event.tick x t ∉ rho.events := by
  intro ht
  have hw := hE.tick_awake x t ht
  rw [ha] at hw
  cases hw

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.saved_rows_erased_at_restart
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.gate_reads_after_wake
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.asleep_has_no_tick
#print axioms AvailableChain.FGSA.Run.arming_tick_exists
#print axioms AvailableChain.FGSA.Run.arming_block_early
#print axioms AvailableChain.FGSA.Run.arming_head_ge
#print axioms AvailableChain.FGSA.Run.arming_head_ge_on
#print axioms AvailableChain.FGSA.Run.arming_healthy_batch
#print axioms AvailableChain.FGSA.Run.arming_enabled_of_pass
#print axioms AvailableChain.FGSA.Run.arming_clean_mem
#print axioms AvailableChain.FGSA.Run.arming_clean_of_tick
#print axioms AvailableChain.FGSA.Run.arming_max_label
#print axioms AvailableChain.FGSA.Run.arming_origin_of_clean
#print axioms AvailableChain.FGSA.Run.arming_origin
#print axioms AvailableChain.FGSA.Run.arming_store_succ_on
#print axioms AvailableChain.FGSA.Run.arming_store_succ
#print axioms AvailableChain.FGSA.Run.arming_clock_offGate_fields
#print axioms AvailableChain.FGSA.Run.arming_saved_interval_on
#print axioms AvailableChain.FGSA.Run.arming_saved_interval
#print axioms AvailableChain.FGSA.Run.arming_slow_saved_on
#print axioms AvailableChain.FGSA.Run.arming_slow_eligible_on
#print axioms AvailableChain.FGSA.Run.arming_slow_saved
#print axioms AvailableChain.FGSA.Run.arming_fast_awake
#print axioms AvailableChain.FGSA.Run.arming_fast_restart_free
#print axioms AvailableChain.FGSA.Run.arming_receiver_window
#print axioms AvailableChain.FGSA.Run.arming_receiver_times
#print axioms AvailableChain.FGSA.Run.arming_receiver_start_epoch
#print axioms AvailableChain.FGSA.Run.arming_receiver_epoch
#print axioms AvailableChain.FGSA.Run.arming_receiver_enabled
#print axioms AvailableChain.FGSA.Run.arming_receiver_gate_epoch
#print axioms AvailableChain.FGSA.Run.arming_tick_store_on
#print axioms AvailableChain.FGSA.Run.arming_emitted_head_fields
#print axioms AvailableChain.FGSA.Run.arming_proposal_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_head_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_batch_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_prefix_batch_receipt_on

end AvailableChain.FGSA.Run.Tests.OutageArming
