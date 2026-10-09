module
public import AvailableChainFGSA.Proofs.Spec.Simulation

public section

namespace AvailableChain.FGSA.Spec

/-! WP12b transfer STOP. Exact-parent refusal cannot be transported through the
current erasure on arbitrary delivered ancestors. The auxiliary identity list in
`Block.representation` is not read by the Lean handler. A claim transfer theorem
needs a revised encoding/adapter and a proved step simulation first. This file
records the failed obligation; it does not assume the missing simulation. -/

/-- No reader of the erased child alone recovers the spec's exact-parent test,
even for the fixed two-element accepted tree in the initialized counterexample. -/
theorem spec_no_exact_parent_reader :
    ¬ ∃ held : NamedProposal 2 → Prop, ∀ B : Block 2,
      held B.embed ↔ B.parent ∈ ([.genesis, parentIdentityHeld] : List (Block 2)) := by
  rintro ⟨held, h⟩
  obtain ⟨_, hbad, hgood, heq, _⟩ := spec_parent_identity_erasure
  have hg := (h parentIdentityGoodChild).mpr hgood
  rw [← heq] at hg
  exact hbad ((h parentIdentityChild).mp hg)

/-- The existing delivery adapter also cannot recover that test: both children
produce the same delivered wire, with the same top-level valid authentication. -/
theorem spec_no_exact_parent_delivery_reader :
    ¬ ∃ held : FGSA.Wire 2 → Prop, ∀ B : Block 2,
      held (deliveryWire parentIdentityAssigned ⟨.proposer 2, .proposal B⟩) ↔
        B.parent ∈ ([.genesis, parentIdentityHeld] : List (Block 2)) := by
  rintro ⟨held, h⟩
  obtain ⟨_, hbad, hgood, _, heq⟩ := spec_parent_identity_erasure
  have hg := (h parentIdentityGoodChild).mpr hgood
  rw [← heq] at hg
  exact hbad ((h parentIdentityChild).mp hg)

end AvailableChain.FGSA.Spec
end
