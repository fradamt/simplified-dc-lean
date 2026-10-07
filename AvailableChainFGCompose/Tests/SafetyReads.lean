module
public import AvailableChainFGCompose.Statements.SafetyClaims

public section

/-! PROVISIONAL safety contracts. S1 does not freeze these laws. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
variable (f : FGFinalityView (Fin n)) (cfg : FGConfig)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

variable (Good : P.State → Prop) (Q : Block → Prop)

-- Type check safety_run_accountable. No proof is declared.
#check (∀ (_C : FGCoreLaws R) (_L : FGSafetyStoreLaws R S H f Good)
    (_K : FGCertificateLaws Ef H f) (_N : FGSafetyScopeLaws R S E rho Q)
    (_hr : safetyScopedRoots R Q),
    SafetyWholeAccountable R S Ef f E rho)

-- Type check safety_run_agreement. No proof is declared.
#check (∀ (_C : FGCoreLaws R) (_L : FGSafetyStoreLaws R S H f Good)
    (_K : FGCertificateLaws Ef H f) (_N : FGSafetyScopeLaws R S E rho Q)
    (_hr : safetyScopedRoots R Q) (_hb : safetyBound R S Ef E rho),
    SafetyWholeAgreement R S f E rho)

-- Type check safety_event_agreement. No proof is declared.
#check (∀ (_C : FGCoreLaws R) (_L : FGSafetyStoreLaws R S H f Good)
    (_K : FGCertificateLaws Ef H f) (_N : FGSafetyScopeLaws R S E rho Q)
    (_hr : safetyScopedRoots R Q) (_hb : safetyBound R S Ef E rho)
    (i j : Nat) (x y : V),
    FGBlock.compatible (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j y)).fg.F = true)

-- Type check safety_fault_count_bound. No proof is declared.
#check (∀ [Fintype V]
    (_U : FGSafetyUnitLaws Ef) (linked : P.Label → Prop)
    (_hfg : linked S.fgLabel) (_hL : V2.D.Linked linked rho)
    (_hc : ∀ B, safetyRunBlock R S E rho B →
      safetyCarriage S E rho (chainRows B))
    (_he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    (_hf : (Gen.V2.Duty.faulty rho).card ≤ (n - 1) / 3),
    safetyBound R S Ef E rho)

-- Type check safety_finalized_monotone. No proof is declared.
#check (∀ (_C : FGCoreLaws R) (_O : FGSafetyOrderLaws R S)
    (_hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (_hnr : V2.D.NoRestart rho),
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (S.finalizedOut (V2.D.Run.readAt E rho t x))
        (S.finalizedOut (V2.D.Run.readAt E rho t' x)))

-- Type check safety_honest_never_slashed. No proof is declared.
#check (∀ (_C : FGCoreLaws R) (_W : FGSafetyWireLaws S)
    (_L : FGSafetyStoreLaws R S H f Good)
    (_J : FGSafetyClientLaws S Ef cfg)
    (linked : P.Label → Prop) (_hfg : linked S.fgLabel)
    (I : Gen.V2.Duty.SlashingInterface (V := V) P)
    (_hi : safetySlashesRead R S E rho I)
    (_hu : V2.D.UnforgeableSignatures E rho) (_hl : V2.D.Linked linked rho),
    Gen.V2.Duty.HonestNeverSlashed I rho)

end AvailableChain.FGCompose
end
