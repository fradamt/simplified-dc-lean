module
public import AvailableChainPCSAClaims.Claims.Recovery
public import AvailableChainPCSAProofs.Proofs.Recovery.Suffix

public section

/-! Conditional short-break recovery export (pcsa34-r4.3b §5.6.1).
The named producers are in RecoverySuffixInputs; no unconditional C11 is claimed. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- C8 supplies initial coverage; restarted CI supplies the healed suffix. -/
theorem recovery_healed_of_inputs (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s₁ : Slot) (ΔF : Time)
    (inputs : RecoverySuffixInputs p c E rho s₁ ΔF) :
    ∃ P, Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho s₁ P ∧
      HealedFrom p c E rho s₁ P := by
  obtain ⟨N, hN, hroot⟩ := inputs.firstSlot
  have hs := inputs.formation N hN hroot
  have ha := arm_next_of_common_stamp E rho s₁ N.erase hs
  have hp := inputs.persistence N.erase ha
  have hi := inputs.ciRestart N hN hroot hp
  refine ⟨N.erase, honestProposal_of_named E rho s₁ N hN.proposal, ?_⟩
  rw [HealedFrom_def]
  refine ⟨?_, ?_, hi.chain, hi.mono, hi.inclusion⟩
  · intro x hx t ht _
    have hfg : SA.freezeTime p.toParams s₁ ≤ SA.gateTime p.toParams s₁ := by
      change 4 * p.Δ * (s₁ : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s₁ : Int) + 6 * p.Δ
      have hd : (0 : Int) < p.Δ := p.deltaPos
      linarith
    exact (hp.2.2 x hx _ t (hfg.trans ht) (inputs.stampRead x hx _ (hs x hx))).2
  · intro x hx t ht _
    exact (hp.2.2 x hx _ t ht (inputs.stampRead x hx _ (hs x hx))).1

/-- The unchanged C11 statement follows when the named recovery producers are supplied. -/
theorem pcsa_fastRecoveredClaim (p : Params)
    (recoveryInputs : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (m : FGMode) (E : Generic.Env V)
      (rho : V2.D.Run V (pcsaWith m p c)) (G ΔF : Time) (cA s₁ : Slot),
      ShortBreakPrem p c E rho G ΔF cA s₁ → RecoverySuffixInputs p c E rho s₁ ΔF) :
    FastRecoveredClaim p := by
  intro V _ _ In c m E rho G ΔF cA s₁ h
  obtain ⟨P, hp, hh⟩ := recovery_healed_of_inputs E rho s₁ ΔF
    (recoveryInputs c m E rho G ΔF cA s₁ h)
  exact ⟨P, hp, recovery_first_gate_bound E rho h.recovery s₁ h.firstMin h.horizon, hh⟩

end AvailableChain.PCSA.Run
end
