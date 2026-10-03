module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE definitions.
DC: SAME frozen JOINT-IND2 r1 cut guards and successor inputs.
PROVISIONAL: JOINT-IND2 (fgsa-lean) lands the real defs; delete this file at that merge -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- The run-level PostResetRetainedCone body (PostResetRead.lean:21) with the cut guard
`timeIdx rho (voteTime s) ≤ i`. -/
def PostResetRetainedConeP (w : HealingWitness) (i : Nat) : Prop :=
  ∀ s, w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  timeIdx rho (SA.voteTime p.toParams s) ≤ i →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n)),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D

def PostResetConeStep (w : HealingWitness) (i : Nat) : Prop :=
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatibleP p c E rho w i ∧
    PostResetOpeningDomainP p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatibleP p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1)


/-- Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE definitions.
DC: SAME equation export of the frozen cut predicate. -/
theorem PostResetRetainedConeP_def (w : HealingWitness) (i : Nat) :
    PostResetRetainedConeP p c E rho w i = (
  ∀ s, w.sStar + 2 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
  timeIdx rho (SA.voteTime p.toParams s) ≤ i →
  ∀ {ip : Nat} {x : V}, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x →
  ∀ (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n)),
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip →
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) := by rfl

/-- Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE definitions.
DC: SAME equation export of the frozen cut predicate. -/
theorem PostResetConeStep_def (w : HealingWitness) (i : Nat) :
    PostResetConeStep p c E rho w i = (
  PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatibleP p c E rho w i ∧
    PostResetOpeningDomainP p c E rho w i ∧ PostResetRetainedConeP p c E rho w i →
  PostResetResetLeaseCompatibleP p c E rho w (i + 1) →
  PostResetLeaseSafe p c E rho w (i + 1) →
  PostResetFProv p c E rho w (i + 1) →
  PostResetRawTransfer p c E rho w (i + 1) →
  PostResetRetainedConeP p c E rho w (i + 1)) := by rfl

end AvailableChain.FGSA.Run
end
