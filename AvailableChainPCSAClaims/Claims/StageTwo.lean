module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C15 (stage 2, shape only)] The
stage-2 statements that W0 can state without new protocol decisions: the
generic PC companion instance over `pcsa` (no frame premise) and persistence
under ARM with J-STABLE and `a ≤ f` (pcsa34-r4 5.4.1). Not stated: CI item
(vi) (the [FGSA.cleanFrame] transfer is HAND), the Π scope (5.4.3,
PROVED-paper, cited), and B_H^PC (5.6.4, PENDING: its values need a PC-SA
proof). No proof in M1. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 (stage 2) J-STABLE(B)] No honest `F`
conflicts with `B` at any event state, and from `e_s` no block conflicting
with `B` is justified at an honest node (the justified read is the stored
`J`). -/
def JStable (s : Slot) (B : Block) : Prop :=
  (∀ x ∈ rho.honest, ∀ i : Nat,
    Block.Compatible (eraseFG (storeBefore p c E rho i x).fg.F) B) ∧
  (∀ x ∈ rho.honest, ∀ t : Time, SA.earlyTime p.toParams s ≤ t →
    Block.Compatible (eraseFG (storeAt p c E rho x t).fg.J) B)

theorem JStable_def (s : Slot) (B : Block) :
    JStable p c E rho s B =
      ((∀ x ∈ rho.honest, ∀ i : Nat,
        Block.Compatible (eraseFG (storeBefore p c E rho i x).fg.F) B) ∧
      (∀ x ∈ rho.honest, ∀ t : Time, SA.earlyTime p.toParams s ≤ t →
        Block.Compatible (eraseFG (storeAt p c E rho x t).fg.J) B)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 (stage 2), PROVED under ARM; plan
C15] Persistence in stage 2: ARM(s, B, j₀), `a ≤ f` (`FGSafetyBound`),
`a < ⌈n/2⌉`, and J-STABLE(B), with no frame premise. -/
def ArmPersistenceJStableClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (s : Slot) (B : Block) (j₀ : Slot),
    Base₂ p c E rho → FaultsBelowQA p c rho → FGSafetyBound p c rho →
    s < j₀ → Arm p c E rho s B j₀ → JStable p c E rho s B → ArmConcl p c E rho s B j₀

theorem ArmPersistenceJStableClaim_def (p : Params) : ArmPersistenceJStableClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (s : Slot) (B : Block) (j₀ : Slot),
      Base₂ p c E rho → FaultsBelowQA p c rho → FGSafetyBound p c rho →
      s < j₀ → Arm p c E rho s B j₀ → JStable p c E rho s B → ArmConcl p c E rho s B j₀) := by
  rw [ArmPersistenceJStableClaim]

/-- [PC-SA claims, W0; plan C8, C9 (Assembly: PCCompanion instance with
Fam = pcsaFamilies.fresh, delayOf = pcsaDelay); App. B] The generic PC
companion over `pcsa` with the model delay. `PCArmedRegime` and
`PCIncludedRegime` have no frame premise, so this is the stage-2 form (r4.3
5.4.2: "PROVED modulo [FGSA.cleanFrame] (HAND) in stage 2"); the stage-1
forms are `ArmHealthyClaim` and `StrongIncludedClaim`. -/
def PCCompanionClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (ΔF : Time),
    E.Δ = p.Δ →
    Gen.V2.Duty.PCCompanion E (pcsaInterface p c) (pcsaFamilies p c).fresh
      (pcsaDelay p E.Δ ΔF) p.n

theorem PCCompanionClaim_def (p : Params) : PCCompanionClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (ΔF : Time),
      E.Δ = p.Δ →
      Gen.V2.Duty.PCCompanion E (pcsaInterface p c) (pcsaFamilies p c).fresh
        (pcsaDelay p E.Δ ΔF) p.n) := by
  rw [PCCompanionClaim]

end AvailableChain.PCSA.Run

end
