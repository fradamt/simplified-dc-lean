module
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944, 03:293–312; spec 1240–1243; plan I-EXACT, G1
steps 4 and 6. Class (iii). DC: Goldfish/Confirmation:494,508,567; INTENTIONAL:
the batch count is read in the actual proposer pools. Every awake honest
label-(s−1) HEAD is a received, resolved vote above D0, so every prefix L of
D0 has a strict majority and beats each conflicting block. -/
theorem inclusion_proposer_prior [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head (s - 1))) q) (SA.voteTime p.toParams (s - 1)) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  intro L hL
  have hstored (o : GridCO.Wire p.n .root) (ho : o ∈ proposerVotes st s) :
      o ∈ (storeAt p c E rho i x).base.votes ∧ GridCO.headLabel? o = some (s - 1) := by
    have h := List.mem_filter.mp ho
    exact ⟨hvotes ▸ h.1, beq_iff_eq.mp h.2⟩
  have hclean : ∀ q ∈ H, GridCO.equivocates (proposerVotes st s) q = false := by
    intro q hq
    obtain ⟨K, t, he, _, _, _, _, _⟩ := hrec q hq
    refine inclusion_no_equivocation _ q
      (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) ?_
    intro o ho hs
    obtain ⟨hm, hl⟩ := hstored o ho
    exact fgsa_honest_head_eq_of_stored E rho hE i x (s - 1) q K.root t ((hH q).mp hq).1 he
      o hm hl hs
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports st.base.blocks (proposerSupport st s) q D0 = true := by
    intro q hq
    obtain ⟨K, t, _, hv, hK, hlookup, hslot, hDK⟩ := hrec q hq
    have hKb := (List.mem_filter.mp (resolvedHead_mem _ _ hK)).1
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head (s - 1)) q, K.root⟩, ?_, rfl, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨hv, beq_self_eq_true _⟩, ?_⟩
      change (match GridCO.resolvedHead? (actView st) _ with
        | some H => decide (H.slot ≤ s - 1) | none => false) = true
      rw [hK]
      exact decide_eq_true hslot
    · exact (Gen.AC.Root.vote_support_body _ _ _).mpr ⟨K, hlookup, hKb, hslot, hDK⟩
  have hother := inclusion_rest_bound E rho hC hE (s - 1) H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (proposerVotes st s)
    (fun o ho k hk => ⟨i, x, o, (hstored o ho).1, (hstored o ho).2, hk⟩)
  have hc := Gen.AC.Root.batch_counts st.base.blocks (proposerVotes st s) (proposerVotes st s)
    (proposerSupport st s) H H.card (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) (fun _ h => (List.mem_filter.mp h).1) rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, hrival, _⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  have hDB : Block.compatible D0 B = false := by
    cases h : Block.compatible D0 B with
    | false => rfl
    | true =>
      have hLB := block_compatible_of_preceq_compatible hL h
      change Block.compatible L B = true at hLB
      rw [hB] at hLB
      contradiction
  exact lt_of_le_of_lt (hrival B hDB) (lt_of_lt_of_le hbatch.lt (hprefix L hL).1)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2980–3001, 03:293–331; spec 1283–1294; plan I-EXACT,
G1 steps 4 and 6. Class (iii). DC: Goldfish/Confirmation:494,508,567;
INTENTIONAL: the batch count is read in the actual HEAD pools, carried votes
included. Provenance maps each pooled seat to a stored vote. Every prefix L
of D0 gets a strict majority, and no conflicting block gets one. -/
theorem inclusion_reader_scores [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    {ih : Nat} {y : V}
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
        (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 → RetainedTargetScores p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1)))
      (r + 1) L := by
  intro L hL
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))
  have hsub : headSupport p dst (r + 1) ⊆ headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
  have hprov := fgsa_headVotes_provenance E rho hE hN ih y r hih
  have hseat (q : Fin p.n) (hq : q ∈ H) : ∃ K t,
      V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (r + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ r ∧ Block.Preceq D0 K ∧
      ∀ o ∈ headVotes p dst (r + 1), GridCO.headSeat? o = some q →
        o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
    obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrec q hq
    have hpre : ∀ o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r,
        GridCO.headSeat? o = some q →
          o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
      intro o ho hs
      have h := List.mem_filter.mp ho
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K.root t ((hH q).mp hq).1 he
        o h.1 (beq_iff_eq.mp h.2) hs
    refine ⟨K, t, he, hv, hK, hslot, hDK, ?_⟩
    intro o ho hs
    rcases hprov o ho q hs with hm | heq
    · exact hpre o hm hs
    · have hne : GridCO.equivocates
          (GridCO.votesAt (V2.D.Run.stateBefore E rho ih y).st.base r) q = false :=
        inclusion_no_equivocation _ q _ hpre
      rw [hne] at heq
      contradiction
  have hclean : ∀ q ∈ H, GridCO.equivocates (headVotes p dst (r + 1)) q = false := by
    intro q hq
    obtain ⟨K, _, _, _, _, _, _, hu⟩ := hseat q hq
    exact inclusion_no_equivocation _ q _ hu
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (r + 1)) q D0 = true := by
    intro q hq
    obtain ⟨K, _, _, hv, hK, hslot, hDK, _⟩ := hseat q hq
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head r) q, K.root⟩, hv, rfl, ?_⟩
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
        (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)) _ hK rfl,
        hK, hslot, hDK⟩
  have hother := inclusion_rest_bound E rho hC hE r H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.Root.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.Root.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card
    (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) hsub rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, _, hnone⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  apply hnone B
  intro q hq
  obtain ⟨K, _, _, _, hK, _, hDK, hu⟩ := hseat q hq
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨o, ho, hk, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ q B).mp hs
  rw [hu o (hsub ho) hk] at hvote
  have hlookup := resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _))
    (baseVote ⟨.seat (.head r) q, K.root⟩) hK rfl
  rw [Gen.AC.Root.voteSupports_def, hlookup] at hvote
  change (_ && _ && Block.preceq B K) = true at hvote
  have hBK : Block.Preceq B K := (Bool.and_eq_true_iff.mp hvote).2
  have hLB := block_compatible_of_common (block_preceq_trans hL hDK) hBK
  change Block.compatible L B = true at hLB
  rw [hB] at hLB
  contradiction

end AvailableChain.FGSA.Run
end
