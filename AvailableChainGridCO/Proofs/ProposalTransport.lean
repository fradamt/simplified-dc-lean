module
public import AvailableChainGridCO.Proofs.ProposalViewRelay

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem fromHead_toHead {n : Nat} (o : Wire n) (row : HeadWire n)
    (h : toHead? o = some row) : fromHead row = o := by
  cases o with
  | mk auth payload =>
      cases payload with
      | head target => simp only [toHead?, Option.some.injEq] at h; rw [← h]; rfl
      | proposal B raw support => simp [toHead?] at h

private theorem mem_of_head_roundtrip {n : Nat} (xs : List (Wire n)) (o : Wire n)
    (h : o ∈ (xs.filterMap toHead?).map fromHead) : o ∈ xs := by
  obtain ⟨row, hrow, he⟩ := List.mem_map.mp h
  obtain ⟨wire, hw, hc⟩ := List.mem_filterMap.mp hrow
  have hwo : wire = o := (fromHead_toHead wire row hc).symm.trans he
  simpa [hwo] using hw

private theorem freeze_horizon {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot)
    (hsync : SynchronousLabel p E rho (r + 1)) : freezeTime p r ≤ rho.horizon := by
  apply le_trans _ hsync.2.2.1
  dsimp [freezeTime, gateTime, proposalTime]
  nlinarith [p.deltaPos]

private theorem proposal_horizon {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (s : Slot)
    (hsync : SynchronousLabel p E rho s) : proposalTime p s ≤ rho.horizon := by
  have hh := hsync.2.2.1
  dsimp [gateTime] at hh
  linarith [p.deltaPos]

/-- The merged raw view equals the actual honest proposer view as a set.
The frozen subset relays before proposal time; the one authenticated
proposal carries the full source view. This includes faulty HEADs. -/
theorem honest_proposal_raw_set {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (reader : V) (hr : reader ∈ rho.honest) :
    ∀ o, o ∈ proposerView (proposalState p rho (r + 1)) (r + 1) ↔
      o ∈ voterView p (nextHeadState p rho r reader) (r + 1) := by
  have hs := hsync.1.toScheduleWellFormed
  have hslot := (honest_proposal_contains_source_root p E rho hs (r + 1) B hB).1
  have hstored := honest_proposal_stored_at_head p E rho hΔ r
    (.of_synchronous hsync) B hB reader hr
  have hf := nextHeadState_frozenAt_of_schedule p E rho hs hΔ r reader hr
    (freeze_horizon p E rho r hsync)
  intro o
  constructor
  · intro ho
    exact proposal_raw_mem_voterView p _ _ (r + 1) _ B _ hstored.2 rfl hslot o ho
  · intro ho
    simp only [voterView, Nat.add_sub_cancel, hf] at ho
    rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hfrozen | hcarried
    · have hraw : o ∈ votesAt
          (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r :=
        (List.mem_filter.mp hfrozen).1
      exact frozen_raw_at_proposer p E rho hs hΔ r hready
        (proposal_horizon p E rho _ hsync) hB.1 reader hr o hraw
    · obtain ⟨hflat, _⟩ := List.mem_filter.mp hcarried
      obtain ⟨wire, hwire, hraw⟩ := List.mem_flatMap.mp hflat
      rw [nextHeadState_honest_proposal_unique p E rho hsync.1 r B hB reader wire hwire] at hraw
      exact mem_of_head_roundtrip _ o hraw

/-- The merged resolved view also equals the proposer support set.
The proof relays the target paths separately and retains the declared
support metadata; raw receipt alone is not used as resolution. -/
theorem honest_proposal_support_set {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (reader : V) (hr : reader ∈ rho.honest) :
    ∀ o, o ∈ proposerSupportView (proposalState p rho (r + 1)) (r + 1) ↔
      o ∈ voterSupportView p (nextHeadState p rho r reader) (r + 1) := by
  have hs := hsync.1.toScheduleWellFormed
  have hslot := (honest_proposal_contains_source_root p E rho hs (r + 1) B hB).1
  have hstored := honest_proposal_stored_at_head p E rho hΔ r
    (.of_synchronous hsync) B hB reader hr
  have hf := nextHeadState_frozenAt_of_schedule p E rho hs hΔ r reader hr
    (freeze_horizon p E rho r hsync)
  intro o
  constructor
  · intro ho
    have hres := (List.mem_filter.mp ho).2
    cases ht : headTarget? o with
    | none => simp [ht] at hres
    | some target =>
        have hknown : target ∈ (proposalState p rho (r + 1)).blocks := by
          simpa only [ht, Bool.and_eq_true, decide_eq_true_eq, blockKnown] using
            (show blockKnown (proposalState p rho (r + 1)) target = true from
              (Bool.and_eq_true_iff.mp (by simpa only [ht] using hres)).1)
        exact proposal_support_mem_voterSupportView p _ _ (r + 1) _ B _ hstored.2 rfl
          hslot o target ho ht (proposal_blocks_at_head p E rho hΔ r hsync hB.1 reader hr
            target hknown)
  · intro ho
    simp only [voterSupportView, Nat.add_sub_cancel, hf] at ho
    rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hfrozen | hcarried
    · exact frozen_support_at_proposer p E rho hs hΔ r hready
        (proposal_horizon p E rho _ hsync) hB.1 reader hr o hfrozen
    · obtain ⟨hflat, _⟩ := List.mem_filter.mp hcarried
      obtain ⟨wire, hwire, hsupport⟩ := List.mem_flatMap.mp hflat
      rw [nextHeadState_honest_proposal_unique p E rho hsync.1 r B hB reader wire hwire]
        at hsupport
      exact mem_of_head_roundtrip _ o hsupport

/-- The engine discharges every local proposal-view transport obligation:
tree reflection, raw participant count, and all common-block scores. -/
theorem proposalViewTransport_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (reader : V) (hr : reader ∈ rho.honest) :
    ProposalViewTransport p (proposalState p rho (r + 1))
      (nextHeadState p rho r reader) (r + 1) B := by
  apply ProposalViewTransport.of_sets p _ _ (r + 1) B
    (honest_proposal_tree_reflects p E rho hΔ r hsync hready B hB reader hr)
    (honest_proposal_raw_set p E rho hΔ r hsync hready B hB reader hr)
    (honest_proposal_support_set p E rho hΔ r hsync hready B hB reader hr)
  intro o ho target ht
  have hres := (List.mem_filter.mp ho).2
  simp only [ht, Bool.and_eq_true, blockKnown, decide_eq_true_eq] at hres
  exact proposal_blocks_at_head p E rho hΔ r hsync hB.1 reader hr target hres.1

end AvailableChain.GridCO
end
