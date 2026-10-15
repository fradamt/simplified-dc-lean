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

private theorem phase_premises_sat :
    (∀ st, (obs.controls st).contest = false ∧ (obs.controls st).Z = .genesis) ∧
    (∀ u v m J c q, PhaseInterval core env run obs u v m J c →
      u ≤ v5T.proposal q → v5T.gate q ≤ v → m = heightAt (q + 1) ∧ c = false) ∧
    AttemptProposalFloor core env run obs v5T iface 12 ∧
    (∀ u v m J c q Q, (12 : Time) ≤ u → PhaseInterval core env run obs u v m J c →
      FrontierSeedQualification v5T 1 env.t_GST u q → v5T.gate q ≤ v →
      HonestProposal env run iface q Q → ∃ i x Qfg,
      V2.D.Run.idxBefore run u ≤ i ∧ i ≤ timeIdx run v ∧ x ∈ run.honest ∧
      Qfg ∈ (core.core (run.stateBefore env i x)).fg.TF ∧ v5erase Qfg = Q) := by
  have bits (st : Nat) : (obs.controls st).contest = false ∧
      (obs.controls st).Z = .genesis := by
    have hn : ¬ ∃ W ∈ stored st, FGBlock.Preceq .genesis W ∧
        (v5H W).h = heightAt (min st 64) ∧ ¬ FGBlock.Preceq .genesis W := by
      rintro ⟨W, _, _, _, h⟩
      exact h (genesis_preceq W)
    constructor
    · change (decide (heightAt (min st 64) = 1) && decide (∃ W ∈ stored st,
        FGBlock.Preceq .genesis W ∧ (v5H W).h = heightAt (min st 64) ∧
          ¬ FGBlock.Preceq .genesis W)) = false
      rw [decide_eq_false hn, Bool.and_false]
    · change (if (obs.controls st).rootIsJ then FGBlock.genesis else .genesis) = .genesis
      split <;> rfl
  have gate (q : Nat) (hq : v5T.gate q ≤ run.horizon) :
      q ≤ 62 ∧ run.stateBeforeTime env (v5T.gate q) 7 = q + 1 := by
    simp only [Time] at *
    have hz : (q : Int) ≤ 62 := by change 4 * (q : Int) + 6 ≤ 256 at hq; omega
    have hn : q ≤ 62 := by exact_mod_cast hz
    refine ⟨hn, ?_⟩
    have ht : v5T.gate q = ((4 * q + 6 : Nat) : Time) := by dsimp [v5T]
    rw [ht, (clock_premises_sat.1 ⟨4 * q + 6, by omega⟩).1]
    change @Eq Nat ((4 * q + 6 - 1) / 4) (q + 1)
    omega
  have height (u v : Time) (m : Nat) (J : Option (FGBlock (Fin 1))) (c : Bool) (q : Nat)
      (hp : PhaseInterval core env run obs u v m J c) (hu : u ≤ v5T.proposal q)
      (hg : v5T.gate q ≤ v) : m = heightAt (q + 1) ∧ c = false := by
    simp only [Time] at *
    have hread := gate q (hg.trans hp.2.1)
    have hug : u ≤ v5T.gate q := by
      change u ≤ 4 * (q : Int) + 6
      change u ≤ 4 * (q : Int) at hu
      simp only [Time] at *
      omega
    have hf := hp.2.2.2 (V2.D.Run.idxBefore run (v5T.gate q)) 7
      (v9idxBefore_mono run hug)
      ((v9idxBefore_le_timeIdx run _).trans (frontierSearch_timeIdx_mono run hg)) (by decide)
    rw [Gen.V2.Duty.stateBefore_idxBefore env run _ execution_premises_sat.1,
      hread.2] at hf
    have hh := hf.1
    change heightAt (min (q + 1) 64) = m at hh
    rw [Nat.min_eq_left (by omega)] at hh
    exact ⟨hh.symm, hf.2.1.symm.trans (bits (q + 1)).1⟩
  refine ⟨bits, height, ?_, ?_⟩
  · intro u v m J c q Q Qfg _ hp hu hg hQ he
    obtain ⟨h1, h64, hprop⟩ := classification_premises_sat.1 q Q hQ
    have hQfg : Qfg = chain q := v5erase_inj (he.trans hprop)
    subst Qfg
    obtain ⟨hm, rfl⟩ := height u v m J c q hp hu hg
    simp only [Slot, Time] at *
    have parent (s : Nat) : (chain s).parent = chain (s - 1) := by cases s <;> rfl
    rw [parent, (chain_facts_premises_sat ⟨q - 1, by omega⟩).1]
    change m - 1 ≤ heightAt (q - 1)
    dsimp only [heightAt] at hm ⊢
    omega
  · intro u v m J c q Q _ hp seed hg hQ
    obtain ⟨_, _, hprop⟩ := classification_premises_sat.1 q Q hQ
    have hu := frontierSearch_seed_after v5T 1 v5TLaws le_rfl seed
    simp only [Slot, Time] at *
    have hug : u ≤ v5T.gate q := by
      change u ≤ 4 * (q : Int) + 6
      change u ≤ 4 * (q : Int) at hu
      simp only [Time] at *
      omega
    have hread := gate q (hg.trans hp.2.1)
    refine ⟨V2.D.Run.idxBefore run (v5T.gate q), 7, chain q,
      v9idxBefore_mono run hug,
      (v9idxBefore_le_timeIdx run _).trans (frontierSearch_timeIdx_mono run hg), by decide,
      ?_, hprop.symm⟩
    rw [Gen.V2.Duty.stateBefore_idxBefore env run _ execution_premises_sat.1, hread.2]
    change chain q ∈ stored (q + 1)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨q, List.mem_range.mpr (by omega), rfl⟩)

#print axioms phase_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end
