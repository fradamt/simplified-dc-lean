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

end AvailableChain.PCSA.Run
end
