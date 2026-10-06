module
public import AvailableChainPCSAProofs.Proofs.Recovery.Anchor
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstHonestSlot
public import AvailableChainPCSAProofs.Proofs.Recovery.LockBound

public section

/-! The short-break suffix interfaces (pcsa34-r4.3b §5.6.1).
Formation, persistence, and the restarted chain invariant remain named inputs.
The local root predicate has the shape of the pending corrected F4 field. -/

namespace AvailableChain.PCSA.Run

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))

/-- Corrected F4: the proposer root is on the walk from the common base. -/
def RecoveryRootReachable (s : Slot) : Prop :=
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s)))

/-- The two-read lock bound supplies corrected F4 at the proposer. -/
theorem recovery_root_reachable (s : Slot) (P : Block)
    (rootBounds : ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
      walkBase p nd.st (proposerPC p nd.st) =
        ((proposerPC p nd.st).map PC.target).getD (eraseFG (controls p nd.st).Z) ∧
      Block.Preceq P (walkBase p nd.st (proposerPC p nd.st)) ∧
      ∀ B, LiveLease nd.st B → Block.Preceq B P) :
    RecoveryRootReachable p c E rho s := by
  intro nd hnd
  obtain ⟨he, hb, hl⟩ := rootBounds nd hnd
  dsimp only
  rw [← he]
  exact root_reachable_of_locks_below p nd.st (proposerPC p nd.st) P hb hl _ _ _

/-- The output parts of the restarted CI, with the later inclusion producer. -/
structure RecoveryChainRestart (s₁ : Slot) : Prop where
  chain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    SA.gateTime p.toParams s₁ ≤ t → t ≤ rho.horizon →
    SA.gateTime p.toParams s₁ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho y t')) ∧
    Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
    Block.Compatible (confirmed (storeAt p c E rho x t)) (strong (storeAt p c E rho y t'))
  mono : ∀ x ∈ rho.honest, ∀ t t' : Time, SA.gateTime p.toParams s₁ ≤ t → t ≤ t' →
    t' ≤ rho.horizon →
    Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t')) ∧
    Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t'))
  inclusion : ∀ u B, s₁ + 1 ≤ u →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c (m := m)).toInterface rho u B →
    (∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ rho.horizon →
      Block.Preceq B (confirmed (storeAt p c E rho x t))) ∧
    (∀ x ∈ rho.honest, ∀ t : Time, SA.freezeTime p.toParams u ≤ t → t ≤ rho.horizon →
      Block.Preceq B (strong (storeAt p c E rho x t)))

variable [Fintype V]

/-- Missing producers needed by the conditional C11 export.
`formation` takes the corrected F4 clause as a separate argument until the
statement branch adds it to FormationPrem. `stampRead` is the boundary
between after-ticks stamps and the inclusive output reader. -/
structure RecoverySuffixInputs (s₁ : Slot) (ΔF : Time) : Prop where
  firstSlot : ∃ N : NamedProposal p.n,
    FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
  formation : ∀ N : NamedProposal p.n,
    FormationPrem p c E rho s₁ N ΔF → RecoveryRootReachable p c E rho s₁ →
    ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams s₁) s₁ N.erase
  persistence : ∀ B, Arm p c E rho s₁ B (s₁ + 1) → ArmConcl p c E rho s₁ B (s₁ + 1)
  stampRead : ∀ y ∈ rho.honest, ∀ B,
    PCStampedBefore p c E rho y (SA.freezeTime p.toParams s₁) s₁ B →
    ∃ pc ∈ (storeAt p c E rho y (SA.freezeTime p.toParams s₁)).pcs,
      pc.slot = s₁ ∧ pc.target = B
  ciRestart : ∀ N : NamedProposal p.n,
    FormationPrem p c E rho s₁ N ΔF → RecoveryRootReachable p c E rho s₁ →
    ArmConcl p c E rho s₁ N.erase (s₁ + 1) → RecoveryChainRestart p c E rho s₁

end AvailableChain.PCSA.Run
end
