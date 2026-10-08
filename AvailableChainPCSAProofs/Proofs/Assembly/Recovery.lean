module
public import AvailableChainPCSAProofs.Proofs.Recovery.Export
public import AvailableChainPCSAProofs.Proofs.Clean.Export
public import AvailableChainPCSAProofs.Proofs.Outage.Export

public section

/-! Clean CI consumers for the recovery archive, and the persistence input of
the recovery suffix from C8. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Existing CI result order closes cleanSaved when the anchor gate result is supplied. -/
theorem recovery_cleanSaved_of_ci (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA : Slot) (P : Block) (hci : CleanInvariantAt p c E rho cA)
    (y : V) (hy : y ∈ rho.honest)
    (hP : gateResultAt p c E rho y cA = some (some P)) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P := by
  apply recovery_cleanSaved_of_gate_prefix E rho hs cA P
  intro x hx r C hr hc
  exact (hci.resultsChain x hx y hy r cA C P hr.le (le_refl _) hc hP).1 hr

/-- CI's PC/result field and the anchor stamp supply cleanSaved without an anchor gate. -/
theorem recovery_cleanSaved_of_ci_pc (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hf : StageOneFrame p c E rho)
    (cA : Slot) (P : Block) (hP : P.slot = cA) (hci : CleanInvariantAt p c E rho cA)
    (y : V) (hy : y ∈ rho.honest)
    (hst : PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA P) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P := by
  obtain ⟨pc, hpc, _, ht⟩ := recovery_stampRead E rho hs hnr hf y hy _ cA P hst
  have htime : SA.freezeTime p.toParams cA < SA.voteTime p.toParams (cA + 1) := by
    have hd := p.deltaPos
    change 4 * p.Δ * (cA : Int) + 3 * p.Δ < 4 * p.Δ * ((cA + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  intro x hx i r C hr hc
  have hcompat := hci.pcResults y hy x hx _ pc r C htime hpc hr.le
    (recovery_saved_gate_result E rho hs x i r C hc)
  rw [ht] at hcompat
  have hsym : Block.Compatible C P := by
    rcases Bool.or_eq_true_iff.mp hcompat with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inr h)
    · exact Bool.or_eq_true_iff.mpr (Or.inl h)
  exact recovery_saved_below_of_compatible E rho x i r cA C P hr hP hc hsym

/-- [§5.6.1; C8] The persistence input of the recovery suffix: ARM at `s₁`
with `j₀ = s₁ + 1` gives its conclusion by C8 (`pcsa_armPersistence`).
RECOVERY's `a ≤ ⌊n/4⌋` gives `a < ⌈n/2⌉`. -/
theorem recovery_persistence_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} (h : Recovery₂ p c E rho G ΔF)
    (hfr : StageOneFrame p c E rho) (s₁ : Slot) :
    ∀ B, Arm p c E rho s₁ B (s₁ + 1) → ArmConcl p c E rho s₁ B (s₁ + 1) := by
  have hf : FaultsBelowQA p c rho := by
    rw [FaultsBelowQA_def]
    have hq := (QuarterCap_def p c rho).mp h.quarterCap
    have hn := p.nPos
    change (Gen.V2.Duty.faulty rho).card < (p.n + 1) / 2
    omega
  have hP : ArmPersistenceClaim p := pcsa_armPersistence p
  rw [ArmPersistenceClaim_def] at hP
  intro B harm
  exact hP c m E rho s₁ B (s₁ + 1) h.base hf hfr (Nat.lt_succ_self s₁) harm

/-- Clean results before the anchor are below its honest proposal, including saved results. -/
theorem pcsa_recovery_cleanSaved_from_anchor [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {ΔF : Time} (cA : Slot) (N : NamedProposal p.n)
    (hPos : 0 < cA)
    (hClean : Clean₂ p c E rho (SA.freezeTime p.toParams cA) ΔF)
    (hFault : FaultsBelowQA p c rho) (hFrame : StageOneFrame p c E rho)
    (hN : HonestNamedProposal p c E rho cA N) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C N.erase := by
  have hgate : SA.gateTime p.toParams (cA - 1) ≤ SA.freezeTime p.toParams cA := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hPos)
    simp only [Nat.succ_sub_one]
    have hd := p.deltaPos
    change 4 * p.Δ * (a : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((a + 1 : Nat) : Int) + 3 * p.Δ
    push_cast
    linarith
  have hparent : Block.Preceq N.erase.parent N.erase := by
    cases N.erase with
    | genesis => exact Gen.Pure.block_preceq_refl _
    | node P s r app =>
      change (decide (P = .node P s r app) || Block.preceq P P) = true
      exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl P))
  apply recovery_cleanSaved_of_gate_prefix E rho hClean.base.valid.toScheduleWellFormed cA N.erase
  intro x hx r C hr hc
  exact Gen.Pure.block_preceq_trans
    (pcsa_clean_result_below_proposal_parent p c m E rho _ ΔF hClean hFault hFrame
      cA N hPos hN hgate x hx r C (Nat.le_sub_one_of_lt hr) hc) hparent

/-- The short-break anchor has an honest proposal, common stamp, and persistent ARM. -/
theorem pcsa_recovery_anchor_from_shortBreak [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁) :
    ∃ N : NamedProposal p.n,
      HonestNamedProposal p c E rho cA N ∧
      (∀ y ∈ rho.honest,
        PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA N.erase) ∧
      Arm p c E rho cA N.erase (cA + 1) ∧
      ArmConcl p c E rho cA N.erase (cA + 1) := by
  have htime : SA.proposalTime p.toParams cA ≤ SA.freezeTime p.toParams cA := by
    have hd := p.deltaPos
    change 4 * p.Δ * (cA : Int) ≤ 4 * p.Δ * (cA : Int) + 3 * p.Δ
    linarith
  obtain ⟨N, hN⟩ := recovery_named_proposal_exists E rho h.recovery.base h.frame cA
    h.anchorPos h.anchorProposer (htime.trans h.anchorClean.cut.2)
  have hStamp := pcsa_clean_honestProposal_stamped p c m E rho _ ΔF h.anchorClean
    h.recovery.quarterCap h.frame cA N h.anchorPos hN h.anchorPart (le_refl _)
  have hArm := arm_next_of_common_stamp E rho cA N.erase hStamp
  exact ⟨N, hN, hStamp, hArm,
    recovery_persistence_of_run E rho h.recovery h.frame cA N.erase hArm⟩

end AvailableChain.PCSA.Run
end
