module
import all AvailableChainFGCompose.Tests.P0d5db
import all tests.POP6bMixedFixture
import all tests.POP6bMixedFacts

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bMixed
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db

private theorem promotion_premises_sat :
    PromotionSlotProposal core env run v5T iface ∧
    PromotionProposalRead core reads env run obs iface decodeProposal v5erase FGBlock.rows
      parentFG parentHeight validFor fold ∧
    PromotionRowSigner reads env run v5T wire ∧
    PromotionSourceParent core env run obs v5T iface 12 ∧
    TRowsReceipt core reads env run v5T (fun _ => []) 1 ∧
    (∀ r h U X, BatchPrem core reads obs v5T env run iface wire v5E decodeProposal v5erase
      FGBlock.rows (fun _ => []) parentFG parentHeight validFor 1 .progress r h U X →
      (obs.height X.parent).h = h → ProgressCoveredByChild v5E obs.height X U h) ∧
    (∀ q Q K, HonestProposal env run iface q Q → v5erase K = Q → K.slot = q) ∧
    (∀ i x A K, K ∈ (core.core (run.stateBefore env i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    PromotionCapReceipt core env run obs v5T iface := by
  have parent (s : Nat) : (chain s).parent = chain (s - 1) := by cases s <;> rfl
  have eraseSlot (X : FGBlock (Fin 1)) : (v5erase X).slot = X.slot := by cases X <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs _ hh
    have h64 : s ≤ 64 := by
      change 4 * (s : Int) ≤ 256 at hh
      exact_mod_cast (show (s : Int) ≤ 64 by omega)
    exact ⟨chain s, (proposal_premises_sat ⟨s, Nat.lt_succ_of_le h64⟩ hs.1).2.1.1,
      chain_slot s⟩
  · intro s X hp _
    obtain ⟨h1, h64, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    have data := proposal_premises_sat ⟨s, Nat.lt_succ_of_le h64⟩ h1
    refine ⟨⟨(chain s).rows, data.2.1, ?_⟩, s - 1, ?_, ?_, rfl, rfl, rfl,
      fun _ => rfl⟩
    · simp
    · change postClock env run (V2.D.proposerOf run iface s) (v5T.proposal s) = _
      rw [data.1]
      exact data.2.2
    · change some (chain ((v5erase (chain s)).parent.slot)) = some (chain s).parent
      rw [v9erase_parent, eraseSlot, parent, chain_slot]
  · refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, ?_⟩
    intro i j r a _
    exact congrArg some (Subsingleton.elim a.signer i)
  · intro u m J c r s X x K _ _ _ _ hafter hp hx hK
    obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
    obtain ⟨_, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    rw [parent]
    change r * 2 + 2 ≤ s at hafter
    exact core_premises_sat.2.2.2.2.1 (2 * r) (s - 1) (by
      simp only [Slot] at *
      omega)
  · intro j y r a ha _ x _
    obtain ⟨hr, _, rfl⟩ := classification_premises_sat.2 j y r a ha
    exact Or.inl (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩)
  · intro q h U X hb _
    obtain ⟨s, hslot⟩ : ∃ s, X.slot = s := ⟨_, rfl⟩
    obtain ⟨rows, hcar, _⟩ := hb.carrier
    have hp := hcar.1
    rw [hslot] at hp
    obtain ⟨_, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    have hafter : q * 2 + 2 ≤ s := hb.after.trans_eq hslot
    obtain ⟨Q, _, hq, hall⟩ := hb.valid
    subst X
    refine ⟨Q, hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hrq, ha, hsign, hn, _⟩ := hall i hi
    obtain ⟨_, _, rfl⟩ := classification_premises_sat.2 j _ r a ha
    refine Or.inr ⟨wireAt r, chain_premises_sat.2.2 r s (by omega), ?_⟩
    exact ⟨Option.some.inj hsign, hn⟩
  · intro q Q K hp he
    obtain ⟨_, _, hQ⟩ := classification_premises_sat.1 q Q hp
    have hk : K = chain q := v5erase_inj (he.trans hQ)
    rw [hk, chain_slot]
  · intro i x A K hK hA
    change K ∈ stored (run.stateBefore env i x) at hK
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hK)
    obtain ⟨a, ha, rfl⟩ := chain_premises_sat.1 A s hA
    simpa only [chain_slot] using ha
  · intro m s Qfg X hp _ _ _ _ hh
    obtain ⟨h1, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    have hs63 : s ≤ 63 := by
      change 4 * (s : Int) + 1 ≤ 256 at hh
      exact_mod_cast (show (s : Int) ≤ 63 by omega)
    have hs : @LT.lt Nat _ (4 * s + 1) 257 := by
      simp only [Slot] at *
      omega
    refine ⟨7, by decide, ?_⟩
    change chain s ∈ stored (run.stateBeforeTime env (v5T.proposal s + v5T.delta) 7)
    have ht : v5T.proposal s + v5T.delta = ((4 * s + 1 : Nat) : Time) := by dsimp [v5T]
    rw [ht, (clock_premises_sat.1 ⟨4 * s + 1, hs⟩).1]
    have hn : @Eq Nat ((4 * s + 1 - 1) / 4) s := by omega
    rw [hn]
    change chain s ∈ ((List.range (min s 64 + 1)).map chain).toFinset
    rw [Nat.min_eq_left (by omega)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨s, List.mem_range.mpr (Nat.lt_succ_self s), rfl⟩)

#print axioms promotion_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end
