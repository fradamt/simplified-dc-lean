module
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem iexact_find_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨⟨b, t⟩, ht, hb⟩ := List.mem_map.mp hm
    dsimp only at hb
    subst b
    have hn := List.find?_eq_none.mp hf (a, t) ht
    simp only [beq_self_eq_true] at hn
    exact (hn trivial).elim
  | some row => rfl

/-- Blueprint 03:293–312; spec 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; a kept first-receipt row keeps its vote stamp
in every later stamp list, whatever the later store clock is. -/
theorem inclusion_stampVote_of_prefix {n : Nat} {st st' : GridCO.State n}
    (h : st.voteStamp <+: st'.voteStamp) {o : GridCO.Wire n}
    (hm : o ∈ st.voteStamp.map Prod.fst) :
    GridCO.stampVote st' o = GridCO.stampVote st o := by
  unfold GridCO.stampVote
  rw [iexact_find_kept h o hm]
  cases he : st.voteStamp.find? (fun row => row.1 == o) with
  | none =>
    obtain ⟨row, hr, ho⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp he row hr
    rw [ho, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- Blueprint 03:293–312; spec 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; a kept first-receipt row keeps its block stamp
in every later stamp list, whatever the later store clock is. -/
theorem inclusion_stampBlock_of_prefix {n : Nat} {st st' : GridCO.State n}
    (h : st.blockStamp <+: st'.blockStamp) {K : Block}
    (hm : K ∈ st.blockStamp.map Prod.fst) :
    GridCO.stampBlock st' K = GridCO.stampBlock st K := by
  unfold GridCO.stampBlock
  rw [iexact_find_kept h K hm]
  cases he : st.blockStamp.find? (fun row => row.1 == K) with
  | none =>
    obtain ⟨row, hr, ho⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp he row hr
    rw [ho, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- Blueprint 03:293–312; spec 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; without restarts a received vote and block stay
stored with their original stamps at every later index. -/
theorem inclusion_stamps_kept (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) {j i : Nat} (hji : j ≤ i) (x : V)
    (o : GridCO.Wire p.n) (K : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hK : K ∈ (storeAt p c E rho j x).base.blocks) :
    o ∈ (storeAt p c E rho i x).base.votes ∧ K ∈ (storeAt p c E rho i x).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho i x).base o =
        GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock (storeAt p c E rho i x).base K =
        GridCO.stampBlock (storeAt p c E rho j x).base K := by
  have hc := fgsa_store_cumulative p c E rho hN hji x
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : K ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hK
  refine ⟨?_, hc.2.1.subset hK, inclusion_stampVote_of_prefix hc.2.2.2.1 hv,
    inclusion_stampBlock_of_prefix hc.2.2.1 hb⟩
  change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
  rw [← fgsa_vote_stamp_keys E rho i x]
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
  exact List.mem_map.mpr ⟨row, hc.2.2.2.1.subset hr, he⟩

omit [DecidableEq V] in
private theorem iexact_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

/-- Blueprint 03:293–312, 21 H.22:3100–3120; spec 1240–1243, 1283–1294;
plan I-EXACT, G1 step 4. Class (iii). DC: INTENTIONAL; the gate-receipt
argument of fgsa_gateReceipt, read at the early tick e_r of any honest
reader instead of at the gate d_r. The emitted HEAD is the scheduled read.
The reader floor bound is an explicit input. Asleep readers are included. -/
theorem inclusion_head_receipt_early
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams r) (SA.earlyTime p.toParams r))
    {j : Nat} {x : V} (hj : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams r)))
    (q : Fin p.n) (hy : rho.seatOf (.base (.head r)) q ∈ rho.honest)
    (hawake : E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
    {k : Nat} (hk : rho.events[k]? =
      some (.tick (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r)))
    (K : Block) (hK : headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.base (.head r)) q)) (SA.voteTime p.toParams r)).st r = K)
    (hF : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) K) :
    V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q) (ofHead p ⟨.seat (.head r) q, K⟩)
      (SA.voteTime p.toParams r) ∧
    baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n) ∈ (storeAt p c E rho j x).base.votes ∧
    GridCO.stampVote (storeAt p c E rho j x).base
      (baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n)) < SA.earlyTime p.toParams r ∧
    K ∈ (storeAt p c E rho j x).base.blocks ∧
    GridCO.stampBlock (storeAt p c E rho j x).base K < SA.earlyTime p.toParams r ∧
    K.slot ≤ r := by
  let y := rho.seatOf (.base (.head r)) q
  have hsch := hE.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? hj)
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have htimes : SA.voteTime p.toParams r + p.Δ = SA.earlyTime p.toParams r := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ = 4 * p.Δ * (r : Int) + 2 * p.Δ
    ring
  rw [Gen.V2.Duty.LabelSyncOn_def] at hSync
  obtain ⟨dl, cut, hD, _, hlt, hbound, _, hcut, _⟩ := hSync
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams r)).cstore r
    rw [hK] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head r) q, K⟩)
      (SA.voteTime p.toParams r) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ r q K).mpr ⟨hawake, rfl, rfl, hK.symm⟩
  have hdeadline : ∀ t, t ≤ SA.voteTime p.toParams r → dl t ≤ SA.earlyTime p.toParams r := by
    intro t ht
    have hb := hbound t
    rw [max_eq_right ht, hDelta, htimes] at hb
    exact hb
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    by_cases hg : K = .genesis
    · rw [hg]
      exact ((cstoreInv_stateBefore E rho j x).baseTree _).mpr
        ⟨.genesis, (cstoreInv_stateBefore E rho j x).fg.gen, rfl⟩
    · have hm := hKsource
      change K ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks at hm
      rw [fgsa_preTick_eq_timeRead E rho hsch hN hk,
        ← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.voteTime p.toParams r) hsch] at hm
      rw [← (metaInv_stateBefore E rho (V2.D.Run.idxBefore rho
        (SA.voteTime p.toParams r)) y).stampKeys] at hm
      obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
      dsimp only at he
      subst b
      rcases fgsa_block_stamp_source E rho _ y K stamp hm with hgen |
        ⟨l, hl, t, o, ho, ha, _⟩
      · exact (hg hgen.1).elim
      · obtain ⟨parent, hdel, _⟩ := ha.1
        have htv := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hdel _).mp hl
        have hdl := hdeadline t htv.le
        exact fgsa_gateReceipt_block_to_tick E rho hE hN hDelta dl cut hD t o K ho
          (Or.inr ⟨y, hy, l, ha⟩) (hlt t) (hdl.trans hcut) hx hj hdl hF
  have hdl := hdeadline (SA.voteTime p.toParams r) le_rfl
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams r)) x).st.slot p ≤
      r + 1 := by
    have hn := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hsch hN
      (iexact_idx_mono rho hdl) x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ x),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ x),
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch,
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch,
      ← fgsa_preTick_eq_timeRead E rho hsch hN hj] at hn
    have hb := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hb
    exact ((Internal.slotOf_mono (p := p) (hn.trans hb)).trans_eq
      (slotOf_offset p r (2 * p.Δ) (by omega) (by omega))).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho hDelta hE hN hC dl cut r q K
    (SA.voteTime p.toParams r) y x hD hy hem hx (hdl.trans hcut) (hlt _) hwindow
  have hid : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams r)) ≤ j := by
    by_contra hn
    exact (not_lt.mpr hdl)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch hj _).mp (Nat.lt_of_not_ge hn))
  have hvoteMem := hr.1
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch] at hvoteMem
  have hkeep := inclusion_stamps_kept E rho hN hid x
    (baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n)) .genesis hvoteMem
    (((cstoreInv_stateBefore E rho _ x).baseTree _).mpr
      ⟨.genesis, (cstoreInv_stateBefore E rho _ x).fg.gen, rfl⟩)
  have hslot : K.slot ≤ r := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p r p.Δ hd.le (by omega)))
  refine ⟨hem, hkeep.1, ?_, hKearly, ?_, hslot⟩
  · rw [hkeep.2.2.1]
    change GridCO.stampVote (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams r))) x).st.base _ < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hr.2.trans_le hdl
  · apply fgsa_gateReceipt_block_stamp_lt E rho hsch hN hj _ K hKearly
    change 0 < 4 * p.Δ * (r : Int) + 2 * p.Δ
    positivity

/-- Blueprint 03:293–312; spec 1240–1243; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; one stored vote per seat excludes a cap. -/
theorem inclusion_no_equivocation {n : Nat} (L : List (GridCO.Wire n)) (k : Fin n)
    (a : GridCO.Wire n) (h : ∀ o ∈ L, GridCO.headSeat? o = some k → o = a) :
    GridCO.equivocates L k = false := by
  cases he : GridCO.equivocates L k with
  | false => rfl
  | true =>
    obtain ⟨u, hu, w, hw, hn, hku, hkw⟩ := (Gen.AC.cap_pair L k).mp he
    exact (hn ((h u hu hku).trans (h w hw hkw).symm)).elim

/-- Blueprint 02:531–541, 03:293–312; spec 1240–1243; plan I-EXACT, G1 step 4.
Class (iii). DC: INTENTIONAL; exactService_participation_of_card without the
fast threshold. The fresh HEAD seat map is a bijection. -/
theorem inclusion_head_seats [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    (hbatch : Gen.Pure.Batch (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r)).card
      (Gen.V2.Duty.faulty rho).card) :
    ∃ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
  classical
  let H := Finset.univ.filter (fun q : Fin p.n =>
    rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
  have hH (q : Fin p.n) : q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun q : Fin p.n => rho.seatOf (.base (.head r)) q) :=
    hC (.base (.head r)) trivial
  have himage : H.image (rho.seatOf (.base (.head r))) =
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r) := by
    ext y
    rw [Gen.V2.Duty.awakeHonest_def, Finset.mem_filter]
    constructor
    · intro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  have hc : H.card = (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams r)).card :=
    (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)
  exact ⟨H, hH, hc ▸ hbatch⟩

/-- Blueprint 02:531–541; spec 1240–1243, 1283–1294; plan I-EXACT, G1 step 4.
Class (iii). DC: Goldfish/Confirmation:494,508; fgsa_late_rest_bound for any
pool whose seats have stored label-r witnesses. Honest stored seats were awake. -/
theorem inclusion_rest_bound [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hE : V2.D.ExecutionValid E rho)
    (r : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head r)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head r)) k) (SA.voteTime p.toParams r) = true → k ∈ H)
    (L : List (GridCO.Wire p.n))
    (hL : ∀ o ∈ L, ∀ k, GridCO.headSeat? o = some k →
      ∃ i x, ∃ o' ∈ (storeAt p c E rho i x).base.votes,
        GridCO.headLabel? o' = some r ∧ GridCO.headSeat? o' = some k) :
    ((GridCO.seats p.n L).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.vote_pool_mem_seats _ k).mp hl
    obtain ⟨i, x, o', ho', hl', hs'⟩ := hL o ho k hs
    exact fgsa_stored_honest_head_awake E rho hE i x r k o' ho' hl' hs' hh
  · intro k _ j _ he
    exact (hC (.base (.head r)) trivial).injective he

/-- Blueprint 21 H.6:932–944, 03:293–312; spec 1240–1243; plan I-EXACT, G1
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
        (ofHead p ⟨.seat (.head (s - 1)) q, K⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K⟩ : HeadWire p.n) ∈ st.base.votes ∧
      K ∈ (actView st).blocks ∧ K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  intro L hL
  have hstored (o : GridCO.Wire p.n) (ho : o ∈ proposerVotes st s) :
      o ∈ (storeAt p c E rho i x).base.votes ∧ GridCO.headLabel? o = some (s - 1) := by
    have h := List.mem_filter.mp ho
    exact ⟨hvotes ▸ h.1, beq_iff_eq.mp h.2⟩
  have hclean : ∀ q ∈ H, GridCO.equivocates (proposerVotes st s) q = false := by
    intro q hq
    obtain ⟨K, t, he, _, _, _, _⟩ := hrec q hq
    refine inclusion_no_equivocation _ q
      (baseVote ⟨.seat (.head (s - 1)) q, K⟩) ?_
    intro o ho hs
    obtain ⟨hm, hl⟩ := hstored o ho
    exact fgsa_honest_head_eq_of_stored E rho hE i x (s - 1) q K t ((hH q).mp hq).1 he
      o hm hl hs
  have hsupp : ∀ q ∈ H,
      Gen.AC.poolSupports st.base.blocks (proposerSupport st s) q D0 = true := by
    intro q hq
    obtain ⟨K, t, _, hv, hK, hslot, hDK⟩ := hrec q hq
    have hKb := ((actView_blocks st K).mp hK).1
    apply (Gen.AC.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head (s - 1)) q, K⟩, ?_, rfl, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨hv, beq_self_eq_true _⟩, ?_⟩
      change (GridCO.blockKnown (actView st) K && decide (K.slot ≤ s - 1)) = true
      simp only [GridCO.blockKnown, hK, hslot, decide_true, Bool.and_self]
    · change (decide (K ∈ st.base.blocks) && decide (K.slot ≤ s - 1) &&
        Block.preceq D0 K) = true
      simp only [hKb, hslot, decide_true, Bool.true_and]
      exact hDK
  have hother := inclusion_rest_bound E rho hC hE (s - 1) H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (proposerVotes st s)
    (fun o ho k hk => ⟨i, x, o, (hstored o ho).1, (hstored o ho).2, hk⟩)
  have hc := Gen.AC.batch_counts st.base.blocks (proposerVotes st s) (proposerVotes st s)
    (proposerSupport st s) H H.card (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) (fun _ h => (List.mem_filter.mp h).1) rfl hclean hsupp hother hbatch
  rw [Gen.AC.BatchBounds_def] at hc
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

/-- Blueprint 21 H.17:2980–3001, 03:293–331; spec 1283–1294; plan I-EXACT,
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
        (ofHead p ⟨.seat (.head r) q, K⟩) t ∧
      baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n) ∈ headSupport p
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
        (ofHead p ⟨.seat (.head r) q, K⟩) t ∧
      baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n) ∈ headSupport p dst (r + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ r ∧ Block.Preceq D0 K ∧
      ∀ o ∈ headVotes p dst (r + 1), GridCO.headSeat? o = some q →
        o = baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n) := by
    obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrec q hq
    have hpre : ∀ o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r,
        GridCO.headSeat? o = some q →
          o = baseVote (⟨.seat (.head r) q, K⟩ : HeadWire p.n) := by
      intro o ho hs
      have h := List.mem_filter.mp ho
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K t ((hH q).mp hq).1 he
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
      Gen.AC.poolSupports dst.base.blocks (headSupport p dst (r + 1)) q D0 = true := by
    intro q hq
    obtain ⟨K, _, _, hv, hK, hslot, hDK, _⟩ := hseat q hq
    apply (Gen.AC.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head r) q, K⟩, hv, rfl, ?_⟩
    change (decide (K ∈ dst.base.blocks) && decide (K.slot ≤ r) &&
      Block.preceq D0 K) = true
    simp only [hK, hslot, decide_true, Bool.true_and]
    exact hDK
  have hother := inclusion_rest_bound E rho hC hE r H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card
    (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) hsub rfl hclean hsupp hother hbatch
  rw [Gen.AC.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, _, hnone⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  apply hnone B
  intro q hq
  obtain ⟨K, _, _, _, _, _, hDK, hu⟩ := hseat q hq
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨o, ho, hk, hvote⟩ := (Gen.AC.vote_pool_support_witness _ _ q B).mp hs
  rw [hu o (hsub ho) hk] at hvote
  change (_ && _ && Block.preceq B K) = true at hvote
  have hBK : Block.Preceq B K := (Bool.and_eq_true_iff.mp hvote).2
  have hLB := block_compatible_of_common (block_preceq_trans hL hDK) hBK
  change Block.compatible L B = true at hLB
  rw [hB] at hLB
  contradiction

end AvailableChain.FGSA.Run
end
