module
public import AvailableChainPCSAProofs.Proofs.Clean.Export

public section

/-! The clean HEAD cone from early receipt through the next vote. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every honest raw voter was awake at the preceding vote, including carried HEADs. -/
theorem pcsa_voter_honest_awake (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hU : V2.D.UnforgeableSignatures E rho)
    (k : Nat) (x : V) (t : Time) (s : Slot) (j : Fin p.n)
    (hj : rho.seatOf (.base (.head s)) j ∈ rho.honest)
    (hm : j ∈ (GridCO.seats p.n
      (headVotes p (clock p (V2.D.Run.stateBefore E rho k x).st t) (s + 1))).toFinset) :
    E.awake (rho.seatOf (.base (.head s)) j) (SA.voteTime p.toParams s) = true := by
  obtain ⟨o, ho, hoj⟩ := (Gen.AC.Root.vote_pool_mem_seats _ j).mp hm
  have hl := pcsa_headVotes_label p _ (s + 1) o ho
  rw [Nat.add_sub_cancel] at hl
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s j hl hoj
  obtain ⟨u, he⟩ := pcsa_voter_input_emission E rho hU k x t s j r hj ho
  exact (pcsa_head_emission_time_awake E rho _ s j r u he).2

/-- Early honest receipt supplies the raw count, frozen support, and retained cone path. -/
theorem pcsa_clean_cone_inputs [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (s : Slot) (B : Block) (he : SA.earlyTime p.toParams s ≤ cut)
    (hheads : ∀ y G, HonestHeadAt p c E rho y s G → Block.Preceq B G)
    (k : Nat) (x : V) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (s + 1)))) :
    let st := clock p (V2.D.Run.stateBefore E rho k x).st (SA.voteTime p.toParams (s + 1))
    let raw := headVotes p st (s + 1)
    let sup := headSupport p st (s + 1)
    ∃ Hon : Finset (Fin p.n),
      (Gen.V2.Duty.faulty rho).card < Hon.card ∧
      (∀ j ∈ Hon, GridCO.equivocates raw j = false) ∧
      (∀ j ∈ Hon, Gen.AC.Root.poolSupports st.base.blocks sup j B = true) ∧
      ((GridCO.seats p.n raw).toFinset \ Hon).card ≤ (Gen.V2.Duty.faulty rho).card ∧
      (∀ C, Block.Preceq C B → C ∈ erasedList st
        (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st (s + 1)))) := by
  classical
  let st := clock p (V2.D.Run.stateBefore E rho k x).st (SA.voteTime p.toParams (s + 1))
  let raw := headVotes p st (s + 1)
  let sup := headSupport p st (s + 1)
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_clean_head_batch_early E rho h s he
  have hef : SA.earlyTime p.toParams s < SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    linarith
  have hvote : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (he.trans h.cut.2)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed hk _).mp hlt
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    push_cast at ht
    have hp := p.deltaPos
    linarith
  have hd : st.base.headDomain = none := by
    change (clock p _ _).base.headDomain = none
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
  refine ⟨Hon, hbatch, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact pcsa_voter_honest_not_capped_unconditional E rho h.base.valid k x _ s j
      ((hHon j).mp hj).1
  · intro j hj
    obtain ⟨hjh, hjw⟩ := (hHon j).mp hj
    obtain ⟨G, hG⟩ := pcsa_honest_head_exists E rho h.base _ hjh s hjw hvote
    obtain ⟨hm, hr⟩ := pcsa_honest_head_clean_support E rho h.base hF h.healthy _ x hx s j G
      rfl hG he k hidx (SA.voteTime p.toParams (s + 1))
    have hearly := List.mem_filter.mp (List.mem_filter.mp hm).1
    have hsup : (⟨.seat s j, .head G.root⟩ : GridCO.Wire p.n .root) ∈ sup := by
      change _ ∈ headSupport p st (s + 1)
      delta headSupport
      apply List.mem_eraseDups.mpr
      apply List.mem_append_left
      apply List.mem_filter.mpr
      rw [Nat.add_sub_cancel]
      refine ⟨hearly.1, ?_⟩
      have ht := hearly.2
      change GridCO.resolvedBefore (actView st) ⟨.seat s j, .head G.root⟩
        (SA.earlyTime p.toParams s) = true at ht
      delta GridCO.resolvedBefore at ht ⊢
      rw [hr] at ht ⊢
      obtain ⟨hh, hb⟩ := Bool.and_eq_true_iff.mp ht
      obtain ⟨hs, hv⟩ := Bool.and_eq_true_iff.mp hh
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨hs, decide_eq_true (lt_trans (of_decide_eq_true hv) hef)⟩,
        decide_eq_true (lt_trans (of_decide_eq_true hb) hef)⟩
    apply (Gen.AC.Root.vote_pool_support_witness st.base.blocks sup j B).mpr
    refine ⟨_, hsup, rfl, ?_⟩
    apply (Gen.AC.Root.vote_support_body st.base.blocks B _).mpr
    refine ⟨G, ?_, ?_, pcsa_honest_head_slot_le E rho h.base hF _ s G hG, hheads _ G hG⟩
    · have hlook := FGSA.Run.resolvedHead_target _ _ hr
      have hdom : GridCO.resolutionTree (actView st) = st.base.blocks := by
        change st.base.headDomain.getD st.base.blocks = st.base.blocks
        rw [hd]
        rfl
      rw [hdom] at hlook
      exact hlook
    · exact (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
  · apply Finset.card_le_card_of_injOn (fun j : Fin p.n => rho.seatOf (.base (.head s)) j)
    · intro j hj
      obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hj
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hh
      exact hn ((hHon j).mpr ⟨hh, pcsa_voter_honest_awake E rho
        h.base.valid.toUnforgeableSignatures k x _ s j hh hm⟩)
    · intro j _ l _ heq
      exact (h.base.cstar (.base (.head s)) trivial).1 heq
  · obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch)
    obtain ⟨hjh, hjw⟩ := (hHon j).mp hj
    obtain ⟨G, hG⟩ := pcsa_honest_head_exists E rho h.base _ hjh s hjw hvote
    obtain ⟨hb, _⟩ := pcsa_honest_head_body_before_early E rho h.base hF h.healthy _ x hx s G
      hG he (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) le_rfl
    have hfreeze : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤
        V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) := by
      rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
        ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ ht
      exact decide_eq_true (lt_trans (of_decide_eq_true ht) hef)
    intro C hCB
    exact pcsa_frozen_read_prefix_mem E rho h.base hF _ k x hx s _ G C hfreeze hidx hb
      (Gen.Pure.block_preceq_trans hCB (hheads _ G hG))

/-- Every next live root is compatible with a common honest HEAD prefix. -/
theorem pcsa_clean_cone_root_compatible [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (hf : FaultsBelowQA p c rho) (s : Slot) (B : Block)
    (he : SA.earlyTime p.toParams s ≤ cut)
    (hheads : ∀ y G, HonestHeadAt p c E rho y s G → Block.Preceq B G)
    (x : V) (hx : x ∈ rho.honest) (R : Block)
    (hR : liveRootAt p c E rho x (s + 1) = some R) : Block.Compatible R B := by
  obtain ⟨Hon, hHon, hbatch⟩ := pcsa_clean_head_batch_early E rho h s he
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch)
  obtain ⟨hjh, hjw⟩ := (hHon j).mp hj
  have hvote : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (he.trans h.cut.2)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hp := p.deltaPos
    linarith
  obtain ⟨G, hG⟩ := pcsa_honest_head_exists E rho h.base _ hjh s hjw hvote
  rcases pcsa_next_root_source E rho h.base hF hf x hx s R hR with hg | ha | hr
  · subst R
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_genesis_preceq B)
      (Gen.Pure.block_preceq_refl B)
  · obtain ⟨y, l, ha, ht⟩ := ha
    have hls := pcsa_early_label_before_vote p l s ht
    rcases lt_or_eq_of_le hls with hlt | rfl
    · exact Gen.Pure.block_compatible_of_common
        (pcsa_clean_ack_to_head_at_early E rho h hF hf l s hlt he y _ R G ha hG)
        (hheads _ G hG)
    · obtain ⟨z, hz⟩ := pcsa_ack_has_honest_head E rho h.base hF hf y _ R ha
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl R)
        (hheads z R hz)
  · obtain ⟨l, X, hlt, hX, hRX⟩ := hr
    exact Gen.Pure.block_compatible_of_common
      (Gen.Pure.block_preceq_trans hRX
        (pcsa_clean_head_above_past_at_early E rho h hF hf s he _ G hG x hx l X hlt hX))
      (hheads _ G hG)

/-- The next honest HEAD covers every common predecessor prefix after the early cut. -/
theorem pcsa_clean_heads_cone_past_cut [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hf : FaultsBelowQA p c rho)
    (hF : StageOneFrame p c E rho) (i : Slot) (B : Block) (hi : 0 < i)
    (he : SA.earlyTime p.toParams (i - 1) ≤ cut)
    (hheads : ∀ y G, HonestHeadAt p c E rho y (i - 1) G → Block.Preceq B G)
    (x : V) (H : Block) (hH : HonestHeadAt p c E rho x i H) : Block.Preceq B H := by
  classical
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  simp only [Nat.succ_sub_one] at he hheads
  by_cases hs : s = 0
  · subst s
    obtain ⟨Hon, hHon, hbatch⟩ := pcsa_clean_head_batch_early E rho h 0 he
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch)
    obtain ⟨hjh, hjw⟩ := (hHon j).mp hj
    have hvote : SA.voteTime p.toParams 0 ≤ rho.horizon := by
      apply le_trans _ (he.trans h.cut.2)
      change 4 * p.Δ * (0 : Int) + p.Δ ≤ 4 * p.Δ * (0 : Int) + 2 * p.Δ
      have hp := p.deltaPos
      linarith
    obtain ⟨G, hG⟩ := pcsa_honest_head_exists E rho h.base _ hjh 0 hjw hvote
    have hBG := hheads _ G hG
    rw [pcsa_honestHead_zero E rho _ G hG] at hBG
    have hB : B = .genesis := of_decide_eq_true hBG
    rw [hB]
    exact Gen.Pure.block_genesis_preceq H
  · have hx := hH.1
    have hhead := hH.2.2
    rw [pcsa_voteHeadAt_def] at hhead
    obtain ⟨nd, hnd, hhead⟩ := Option.map_eq_some_iff.mp hhead
    obtain ⟨k, hk, hstore⟩ := pcsa_postClock_source E rho x _ nd hnd
    have hR : liveRootAt p c E rho x (s + 1) =
        some (liveRoot p nd.st (voterPC p nd.st (s + 1))) := by
      rw [pcsa_liveRootAt_def, hnd]
      rfl
    have hcompat := pcsa_clean_cone_root_compatible E rho h hF hf s B he hheads x hx _ hR
    rw [hstore] at hhead hcompat
    let st := clock p (V2.D.Run.stateBefore E rho k x).st (SA.voteTime p.toParams (s + 1))
    let raw := headVotes p st (s + 1)
    let sup := headSupport p st (s + 1)
    obtain ⟨Hon, hbatch, hcap, hsup, hbound, hpath⟩ :=
      pcsa_clean_cone_inputs E rho h hF s B he hheads k x hx hk
    have hsub : sup ⊆ raw :=
      pcsa_headSupport_subset_at_read E rho h.base.valid.toDeliveryWellFormed k x _ (s + 1)
    have hcounts := Gen.AC.Root.transfer_n2 st.base.blocks raw sup Hon Hon.card
      (Gen.V2.Duty.faulty rho).card B hsub rfl hcap hsup hbound hbatch
    have hcover := pcsa_headInTree_covers_of_transfer p st (voterPC p st (s + 1))
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st (s + 1))))
      raw sup B hcompat (fun C _ hCB => hpath C hCB) hcounts.2.2.2.2.2.1 hcounts.2.2.2.2.2.2
    delta headVote at hhead
    rw [ite_eq_right (Nat.succ_ne_zero s)] at hhead
    rw [← hhead]
    exact hcover

end AvailableChain.PCSA.Run

end
