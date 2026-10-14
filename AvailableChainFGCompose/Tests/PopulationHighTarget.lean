module
import all AvailableChainFGCompose.Tests.PopulationHighTargetFixture

set_option linter.privateModule false
noncomputable section
public section
namespace AvailableChain.FGCompose.Tests.PopulationHighTarget
open AvailableChain.SimplexFG AvailableChain.KitFG

private theorem mixed_actions_premises_sat :
    FGHonestSeats reads run = {0} ∧ ({0} : Finset (Fin 1)).Nonempty ∧
    electorate.IsQuorum {0} ∧ high core obs point.reset .genesis ∧
    (∀ r, r ≤ 1 → (∀ x ∈ run.honest,
      actionSourceFG core (env Nat) run timing x r = some (some .genesis)) ∧
      (env Nat).t_GST ≤ timing.action r ∧ timing.action r + 2 ≤ run.horizon) ∧
    (∀ x ∈ run.honest, ∀ t, (env Nat).t_GST ≤ t → t ≤ run.horizon →
      (env Nat).awake x t = true) ∧
    (∀ r, reads.enabled (timing.action r) = true) := by
  refine ⟨?_, ⟨0, by simp⟩, by change (1 : Nat) ≤ 1; decide,
    by change (1 : Nat) ≤ 1; decide, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder]
  · intro r hr
    interval_cases r <;> refine ⟨?_, by decide, by decide⟩
    all_goals
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> rfl
  · intro x _ t _ _; rfl
  · intro r
    apply decide_eq_true
    change (4 * (r * 2 : Nat) + 6 : Int) % 8 = 6
    omega

#print axioms mixed_actions_premises_sat

private theorem mixed_targets :
    (∃ j a, j = 6 ∧ a = wire ∧ HonestRowAt reads (env Nat) run timing j 9 0 a ∧
      RowComplete reads run history.signer (fun _ => true) 9 a ∧
      history.heightPair a = .vote 1 genesisRoot false) ∧
    (∃ j q a, j = 6 ∧ q = 0 ∧ a = wire ∧ q ≤ 1 ∧
      HonestRowAt reads (env Nat) run timing j 9 q a ∧
      RowComplete reads run history.signer (fun _ => true) 9 a ∧
      history.heightPair a = .vote 1 genesisRoot false) ∧
    (∃ rows : Fin 1 → protocol.Object, rows 0 = wire ∧
      history.signer (rows 0) = some 0 ∧
      HeldBefore core (env Nat) run Prod.snd 7 (rows 0) 8 ∧
      HeldBefore core (env Nat) run Prod.snd 9 (rows 0) 8) := by
  let p := mixed_premises_sat
  obtain ⟨hH, hne, hQ, hhigh, actions, awake, enabled⟩ := mixed_actions_premises_sat
  have hholder : safetyHolder reads run 0 ∈ run.honest := by decide
  have hsource0 := (actions 0 (by decide)).1 9 (by decide)
  have hsource1 := (actions 1 (by decide)).1 9 (by decide)
  obtain ⟨j, a, ha, hc, hp⟩ := high_target_first_row_holder (D := history) (pt := point)
    (fun _ => genesisRoot) p.entry_source p.records p.finality p.prior
    (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace p.emission
    p.complete p.wires p.timing_laws p.schedule enabled 0 hholder 0 .genesis hsource0 hhigh rfl
    (by intro j q a h hq; omega)
  have he := exact_row j 9 0 a ha
  refine ⟨⟨j, a, he.1, he.2.2.2, ha, hc, hp⟩, ?_⟩
  obtain ⟨j, q, a, hq, ha, hc, hp⟩ := high_target_row_covered_holder
    (D := history) (pt := point) (fun _ => genesisRoot) p.entry_source p.records p.finality
    p.prior (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace
    p.emission p.complete p.wires p.timing_laws p.schedule enabled
    0 hholder 1 .genesis hsource1 hhigh rfl
  have he := exact_row j 9 q a ha
  refine ⟨⟨j, q, a, he.1, he.2.2.1, he.2.2.2, hq, ha, hc, hp⟩, ?_⟩
  obtain ⟨_, rows, hr⟩ := high_target_quorum_covered_holder (D := history) (pt := point)
    (fun _ => genesisRoot) p.entry_source p.records p.finality p.prior
    (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace p.emission
    p.complete p.wires p.timing_laws p.schedule enabled {0}
    (by simpa only [hH] using (Finset.Subset.refl ({0} : Finset (Fin 1))))
    hne hQ Prod.snd 2 (by decide) p.receipt awake
    1 .genesis hhigh (by
      intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hsource1)
    (actions 1 (by decide)).2.1 (actions 1 (by decide)).2.2
  obtain ⟨j, q, _, ha, _, hs, _, receipts⟩ := hr 0 (by simp)
  obtain ⟨_, _, hq, hw⟩ := exact_row j 9 q (rows 0) ha
  subst q
  exact ⟨rows, hw, hs, receipts 7 (by decide), receipts 9 (by decide)⟩

#print axioms mixed_targets

-- Only the signer obstruction is used: every seat belongs to 9, never to 7.
private theorem old_nonholder_target_impossible :
    ¬ ∃ j q a, q ≤ 0 ∧ HonestRowAt reads (env Nat) run timing j 7 q a ∧
      RowComplete reads run history.signer (fun _ => true) 7 a ∧
      history.heightPair a = .vote 1 genesisRoot false := by
  rintro ⟨j, q, a, _, _, hc, _⟩
  obtain ⟨i, _, hi⟩ := hc.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_nonholder_target_impossible
end AvailableChain.FGCompose.Tests.PopulationHighTarget
end
