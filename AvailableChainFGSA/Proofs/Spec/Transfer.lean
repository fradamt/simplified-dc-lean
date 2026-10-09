module
public import AvailableChainFGSA.Proofs.Spec.Simulation

public section

namespace AvailableChain.FGSA.Spec

/-! Ruling U repairs ancestor identity through a simulation-only stutter filter.
The old raw-erasure obstructions below remain true. Full transfer is still stopped:
a between-public-ticks restart loses the target clock and changes block acceptance.
Row targets also need a full-block-to-root equality bridge; the pinned text does
not explicitly declare them root names. No claim transfer is assumed here. -/

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

/-- Inserting a refused source payload leaves the entire mapped event list unchanged.
Thus its target state folds and emissions are unchanged at the matched list cut. -/
theorem spec_stutter_event_list {V : Type} (p : Params) (assigned : Slot → Fin p.n)
    (before after : List (V2.Event V (Wire p.n))) (v : V) (t : Time)
    (auth : Auth Label p.n) (B : Block p.n) (hB : ¬ B.Assigned assigned) :
    (before ++ .deliver v ⟨auth, .proposal B⟩ t :: after).filterMap
        (specSimulationEvent p assigned) =
      (before ++ after).filterMap (specSimulationEvent p assigned) := by
  simp [List.filterMap_append, spec_simulation_event_stutter p assigned v t auth B hB]

/-- Concrete failure of the full block-step observation after a between-ticks restart.
This rules out equality at this prescribed post-delivery cut for the event mapping. -/
theorem spec_restart_matched_cut_failure :
    (process specRestartParams specRestartCurrent specRestartWire.embed).proposals.length ≠
      (V2.D.Run.final specRestartEnv specRestartRun 1).st.proposals.length := by
  obtain ⟨_, _, _, _, _, hs, _, ht⟩ := spec_restart_block_trace
  rw [hs, ht]
  decide

/-- Full row-target equality and root-valued height matching differ on the identity
fixture. The Assigned proposal filter does not inspect row targets. This is the
extra row-identity obligation under the full-block reading of spec T and T_f. -/
theorem spec_row_target_identity_trace :
    (2, parentIdentityAbsent) ≠ (2, parentIdentityHeld) ∧
    SimplexFG.NamedHeightPair.matchesEntry 2 parentIdentityHeld.root
      (.vote 2 parentIdentityAbsent.root false) = true ∧
    (some (2, parentIdentityAbsent) : Option (Nat × Block 2)) ≠
      some (2, parentIdentityHeld) ∧
    (⟨2, parentIdentityAbsent.root⟩ : SimplexFG.FinalityPair) =
      ⟨2, parentIdentityHeld.root⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact spec_parent_identity_erasure.1 (Prod.mk.inj h).2
  · rw [spec_parent_identity_root]
    simp [SimplexFG.NamedHeightPair.matchesEntry]
  · intro h
    exact spec_parent_identity_erasure.1 (Prod.mk.inj (Option.some.inj h)).2
  · rw [spec_parent_identity_root]

/-- Root names alone cannot recover equality to the full held target. This includes
proposer-only aliases without a collision between distinct digest inputs. -/
theorem spec_no_full_row_target_reader :
    ¬ ∃ test : BlockId → Prop, ∀ T : Block 2,
      test T.root ↔ T = parentIdentityHeld := by
  rintro ⟨test, h⟩
  have hm := (h parentIdentityHeld).mpr rfl
  rw [← spec_parent_identity_root] at hm
  have he := (h parentIdentityAbsent).mp hm
  exact spec_parent_identity_erasure.1 he

end AvailableChain.FGSA.Spec
end
