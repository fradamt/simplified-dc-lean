module
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate
public import AvailableChainFGSAProofs.Proofs.Clean.Transfer
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAProofs.Proofs.Shared.Count

public section

/-! P3 §8.7 F2.5a–b; bp02 §§5.4–5.5. Gate history and independent guard.
Old history supplies the active honest batch; receipt coverage retains its paths.
Ordered, Same, and nonempty are proved first; transfer then supplies Continues. -/

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The store confirmation fact is called directly. The private batch boundary
-- is discharged by gate_batch_of_history at the public OSN consumer.
omit [Fintype V] in
private theorem ordered_of_confirmation
    {i : Nat} (hsch : V2.D.ScheduleWellFormed E rho)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (hbatch : ∀ x s, IsGateTick p c rho i x s →
      ∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s →
      let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
      let v := actView pre
      let a := eraseFG pre.fg.F
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s a ∧
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s B ∧
      (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks)) :
    ∀ s r B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (r, C) ∈ cleanResults p c E rho (i + 1) → s < r → Block.Preceq B C := by
  have hlabels : ∀ {j x y s r}, j ≤ i → IsGateTick p c rho j x s →
      IsGateTick p c rho i y r → s ≤ r := by
    intro j x y s r hji hj hi
    have ht : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams r := by
      rcases hji.eq_or_lt with rfl | hlt
      · exact le_of_eq (V2.Event.tick.inj (Option.some.inj (hj.symm.trans hi))).2
      · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
        have hk := (List.pairwise_iff_getElem.mp hsch.sorted) j i hjl hil hlt
        rw [hje, hie] at hk
        exact V2.D.Engine.time_le_of_key_le _ _ hk
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
      4 * p.Δ * (r : Int) + 6 * p.Δ at ht
    have hd : (0 : Int) < p.Δ := p.deltaPos
    exact_mod_cast (show (s : Int) ≤ (r : Int) by nlinarith)
  intro s r B C hB hC hsr
  rcases cleanResults_mem_succ_iff.mp hC with hCold | ⟨x, ht, hCnew⟩
  · rcases cleanResults_mem_succ_iff.mp hB with hBold | ⟨y, hu, _⟩
    · exact hh.ordered s r B C hBold hCold hsr
    · obtain ⟨j, hj, x, hx, _⟩ := hCold
      exact (Nat.not_lt_of_ge (hlabels (Nat.le_of_lt hj) hx hu) hsr).elim
  · rcases cleanResults_mem_succ_iff.mp hB with hBold | ⟨y, hu, _⟩
    · let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams r)
      have hac : Block.Compatible (eraseFG pre.fg.F) B := by
        change Block.Compatible (eraseFG (clockPre p _ _).fg.F) B
        rw [clockPre_fg]
        rcases (hs.gateInputs x r ht).1 with hg | ⟨t, D, hD, _, haD⟩
        · change Block.Compatible (F_at p c E rho i x) B
          rw [hg]
          exact block_compatible_of_common (block_genesis_preceq B) (block_preceq_refl B)
        · exact block_compatible_of_preceq_compatible haD (cleanHist_results_compatible hh hD hBold)
      obtain ⟨ha, hb, hpath⟩ := hbatch x r ht s B hBold hsr
      obtain ⟨D, hD, hBD⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
        (eraseFG pre.fg.F) B r hac ha hb hpath
      have hraw := Option.some.inj ((clean_gate_raw hsch ht).symm.trans hCnew)
      have he : D = C := Option.some.inj (hD.symm.trans hraw)
      exact he ▸ hBD
    · exact (Nat.not_lt_of_ge (hlabels le_rfl ht hu) hsr).elim



/-- P3 F2.5a:4900–4945; bp02 §5.4. Class B, label-seat count instance.
DC: Goldfish/Confirmation.lean:494; same honest participation count.
The label-seat bijection converts the Clean participation bound to Batch.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_batch (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    {i : Nat} {x : V} {s : Slot} (hi : i < timeIdx rho b₀)
    (ht : IsGateTick p c rho i x s) :
    ∃ H : Finset (Fin p.n),
      (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
  classical
  let A := Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (h.base.cstar (.base (.head s)) trivial)
  let H := A.image e.symm
  refine ⟨H, ?_, ?_⟩
  · intro k
    have he : k ∈ H ↔ e k ∈ A := by
      change k ∈ A.image e.symm ↔ e k ∈ A
      simp only [Finset.mem_image, e.symm_apply_eq]
      exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hk => ⟨e k, hk, rfl⟩⟩
    rw [he]
    change rho.seatOf (.base (.head s)) k ∈
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) ↔ _
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.mem_filter
  have htime : SA.gateTime p.toParams s ≤ b₀ :=
    (V2.D.Engine.index_lt_read_length_iff h.base.valid.toScheduleWellFormed b₀ ht).mp hi
  have hv : 0 ≤ SA.voteTime p.toParams s ∧ SA.voteTime p.toParams s < b₀ := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ b₀ at htime
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ ∧ 4 * p.Δ * (s : Int) + p.Δ < b₀
    have hd : (0 : Int) < p.Δ := p.deltaPos
    have hsn : 0 ≤ (s : Int) := Nat.cast_nonneg s
    constructor <;> nlinarith
  have hcard : H.card = (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card :=
    Finset.card_image_of_injective A e.symm.injective
  exact ⟨hcard ▸ h.partBefore _ hv.1 hv.2⟩

private theorem stamp_find_kept {α : Type} [BEq α] [LawfulBEq α]
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

omit [Fintype V] in
/-- P3 F2.5a:4921–4945; bp02 §5.4 (original early stamps). Class B.
DC: Schedule/AdoptionTransport.lean:157; receipt retention analogue.
INTENTIONAL: clockPre and actView retain the original FG-SA stamps
(spec/fgsa-protocol.tex:2506–2513), including stamps of inactive blocks. -/
theorem clean_gate_stamps (hf : FGFoundation p c E rho) (hn : V2.D.NoRestart rho)
    {j i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hji : j ≤ i) (hi : i ≤ rho.events.length)
    (o : GridCO.Wire p.n) (B : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v B = GridCO.stampBlock (storeAt p c E rho j x).base B := by
  intro v
  have hc := hf.cumul hn j i x hx hji hi
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : B ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change B ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hB
  have hev := stamp_find_kept hc.2.2.2 o hv
  have heb := stamp_find_kept hc.2.2.1 B hb
  refine ⟨?_, ?_, ?_⟩
  · change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
    rw [← fgsa_vote_stamp_keys E rho i x]
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨row, hc.2.2.2.subset hr, he⟩
  · change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).2, hev]
    unfold GridCO.stampVote
    cases he : (storeAt p c E rho j x).base.voteStamp.find? (fun row => row.1 == o) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hv
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
  · change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).1, heb]
    unfold GridCO.stampBlock
    cases he : (storeAt p c E rho j x).base.blockStamp.find? (fun row => row.1 == B) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hb
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl

/-- P3 F2.5a; bp02 §5.4, label zero. Class B, run nonemptiness.
DC: Goldfish/Confirmation.lean:494,567; genesis majority analogue.
INTENTIONAL: the F-anchored optional raw result is exactly genesis
(spec/fgsa-protocol.tex:2506–2513). No successor history is used.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_zero (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) {i : Nat} {x : V}
    (hi : i < timeIdx rho b₀) (ht : IsGateTick p c rho i x 0)
    (hs : CleanState p c E rho i) :
    gateResultAt p c E rho i = some (some .genesis) := by
  have hsch := h.base.valid.toScheduleWellFormed
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil : i ≤ rho.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
  have htime : 6 * p.Δ ≤ b₀ := by
    have hh := (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
    change 4 * p.Δ * (0 : Int) + 6 * p.Δ ≤ b₀ at hh
    simpa only [mul_zero, zero_add] using hh
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have h2 : (2 : Time) * p.Δ ≤ rho.horizon := by linarith [h.cut.2]
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch h.base.delta x hx 2 h2
  change rho.events[j]? = some (.tick x (2 * p.Δ)) at hj
  have hji : j < i := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht (by
    change 2 * p.Δ < 4 * p.Δ * (0 : Int) + 6 * p.Δ
    nlinarith)
  have hjread := fgsa_preTick_eq_timeRead E rho hsch h.base.noRestart hj
  have hjwindow : (V2.D.Run.stateBeforeTime E rho (2 * p.Δ) x).st.slot p ≤ 0 + 1 := by
    rw [← hjread]
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hn
    have hb := Internal.slotOf_mono (p := p) hn
    have hz : p.slotOf (2 * p.Δ) = 0 := by
      have he := slotOf_offset p 0 (2 * p.Δ) (by omega) (by omega)
      simpa only [Nat.cast_zero, mul_zero, zero_add] using he
    exact (hb.trans_eq hz).trans (Nat.zero_le _)
  obtain ⟨H, hH, hbatch⟩ := clean_gate_batch p c E rho b₀ h hi ht
  have hF : eraseFG (storeAt p c E rho i x).fg.F = .genesis := by
    rcases (hs.gateInputs x 0 ht).1 with hg | ⟨r, B, _, hr, _⟩
    · exact hg
    · exact (Nat.not_lt_zero r hr).elim
  have hgen : GridCO.stampBlock
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)))
      .genesis < GridCO.earlyTime p.toParams.engine 0 := by
    have hp := (hf.cumul h.base.noRestart 0 i x hx (Nat.zero_le i) hil).2.2.1
    change [(Block.genesis, (0 : Time))] <+: (storeAt p c E rho i x).base.blockStamp at hp
    obtain ⟨tail, he⟩ := hp
    change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ < _
    rw [(clockPre_stamps p _ _).1, ← he]
    change (0 : Time) < 4 * p.Δ * (0 : Int) + 2 * p.Δ
    nlinarith
  have hreceipts : ∀ k ∈ H, ∃ t,
      rho.seatOf (.base (.head 0)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head 0)) k)
        (ofHead p ⟨.seat (.head 0) k, .genesis⟩) t ∧
      baseVote (⟨.seat (.head 0) k, .genesis⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)))
        (baseVote (⟨.seat (.head 0) k, .genesis⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine 0 := by
    intro k hk
    obtain ⟨hkh, hka⟩ := (hH k).mp hk
    have h1 : (1 : Time) * p.Δ ≤ rho.horizon := by linarith [h.cut.2]
    obtain ⟨l, hl, _⟩ := fgsa_tick_total E rho hsch h.base.delta _ hkh 1 h1
    have hem : V2.D.Run.emits E rho (rho.seatOf (.base (.head 0)) k)
        (ofHead p ⟨.seat (.head 0) k, .genesis⟩) p.Δ := by
      have hl' : rho.events[l]? = some (.tick (rho.seatOf (.base (.head 0)) k) p.Δ) := by
        simpa only [Nat.cast_one, one_mul] using hl
      refine ⟨l, hl', ?_⟩
      rw [(V2.D.Run.step_tick_eq E rho hl').2]
      apply (fgsa_emits_head E rho _ _ _ 0 k .genesis).mpr
      refine ⟨?_, ?_, rfl, ?_⟩
      · change E.awake _ (4 * p.Δ * (0 : Int) + p.Δ) = true at hka
        simpa only [mul_zero, zero_add] using hka
      · change 4 * p.Δ * (0 : Int) + p.Δ = p.Δ
        ring
      · exact (headVote_zero p _).symm
    have hr := fgsa_honest_head_receipt E rho h.base.delta h.base.valid h.base.noRestart
      h.base.cstar (fun t => t + p.Δ) b₀ 0 k .genesis p.Δ _ x
      (by
        simpa only [h.base.delta] using
          Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀ h.healthy
            (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _))
      hkh hem hx (by linarith)
      (lt_add_of_pos_right p.Δ hd) (by
        change (V2.D.Run.stateBeforeTime E rho (p.Δ + p.Δ) x).st.slot p ≤ 1
        rw [show p.Δ + p.Δ = 2 * p.Δ by ring]
        exact hjwindow)
    have hearly : p.Δ + p.Δ = 2 * p.Δ := by ring
    dsimp only at hr
    rw [hearly, ← hjread] at hr
    have hb : Block.genesis ∈ (storeAt p c E rho j x).base.blocks :=
      ((storeBundle_stateBefore E rho j x).cstore.baseTree _).mpr
        ⟨.genesis, (storeBundle_stateBefore E rho j x).cstore.fg.gen, rfl⟩
    have htrans := clean_gate_stamps p c E rho hf h.base.noRestart (s := 0) hx
      (Nat.le_of_lt hji) hil _ .genesis hr.1 hb
    refine ⟨p.Δ, hkh, hem, htrans.1, ?_⟩
    rw [htrans.2.1]
    change _ < 4 * p.Δ * (0 : Int) + 2 * p.Δ
    have hrstamp : GridCO.stampVote (storeAt p c E rho j x).base
        (baseVote (⟨.seat (.head 0) k, .genesis⟩ : HeadWire p.n)) < 2 * p.Δ := hr.2
    simpa only [mul_zero, zero_add] using hrstamp
  have hraw := (fgsa_gate_zero_of_receipts E rho h.base.valid h.base.cstar i x H hbatch
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩) hF hreceipts hgen).2
  exact (clean_gate_raw hsch ht).trans (congrArg some hraw)

omit [Fintype V] in
private theorem gate_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {s : Slot} {K : Block}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
  intro b hb hne
  have hc := (storeBundle_stateBefore E rho k y).cstore
  obtain ⟨Kfg, hKfg, he⟩ := (hc.baseTree K).mp hK
  rw [← he] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg hb
  have hbm := (hc.baseTree b).mpr ⟨Bfg, hBfg, heB⟩
  rw [← (storeBundle_stateBefore E rho k y).«meta».stampKeys] at hbm
  obtain ⟨⟨b', stamp⟩, hstamp, he'⟩ := List.mem_map.mp hbm
  dsimp only at he'
  subst b'
  rcases fgsa_block_stamp_source E rho k y b stamp hstamp with hg | ⟨l, hl, t, o, ho, ha, _⟩
  · exact (hne hg.1).elim
  · refine ⟨l, hl, t, o, ho, ha, ?_, ?_⟩
    · obtain ⟨parent, hd, _⟩ := ha.1
      exact (hsch.in_horizon _ (List.mem_of_getElem? hd)).1
    · obtain ⟨parent, hd, _⟩ := ha.1
      obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
      obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
      have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
      rw [hle, hke] at hkey
      change toLex (t, (2 : Nat)) ≤ toLex (SA.voteTime p.toParams s, 1) at hkey
      rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨_, hphase⟩
      · exact hlt
      · omega

omit [Fintype V] in
private theorem gate_path_coverage (hE : V2.D.ExecutionValid E rho)
    (_hn : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (b₀ : Time) (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (hb₀ : b₀ ≤ rho.horizon) {i k : Nat} {x y : V} {s : Slot} {K : Block}
    (ht : IsGateTick p c rho i x s) (hcut : SA.gateTime p.toParams s ≤ b₀)
    (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) K) :
    ∃ required paths,
      ReceiptCoveragePremises E rho (fun t => t + p.Δ) b₀
        (SA.earlyTime p.toParams s) 0 x K required paths ∧
      paths K (SA.earlyTime p.toParams s) := by
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = SA.earlyTime p.toParams s
  have hsch := hE.toScheduleWellFormed
  have hD : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hd : (0 : Int) < p.Δ := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hh
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (SA.earlyTime p.toParams s)).mp
      (Nat.lt_of_not_ge hh)
    exact (not_lt.mpr hD) hlt
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    refine ⟨(hsch.in_horizon _ (List.mem_of_getElem? hd)).1, ?_⟩
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤ toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hh | ⟨_, hh⟩
    · exact hh
    · omega
  refine ⟨required, paths, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀ hhealthy
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨parent, he, hh⟩ := ha.1
    refine ⟨Or.inr ⟨y, hy, l, ha⟩,
      handles_wellFormed p c _ parent o hh (hE.wire l y parent t he), ?_⟩
    intro r a B hv
    have hh : blockOf? p o = none := by
      change (match (toWire p o).decode with | some (.block _ b _ _ _) => some b | _ => none) = _
      rw [hv]
    rw [hh] at hb
    contradiction
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl K) (hF j (hj.trans hidx))
  · refine ⟨fun _ _ hab => add_le_add hab le_rfl, hD.trans hcut, hb₀, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro o t hr
      have htt := htime o t hr
      refine ⟨Nat.zero_le _, htt.1, lt_add_of_pos_right _ p.deltaPos, ?_⟩
      have hv := htt.2
      change t < 4 * p.Δ * (s : Int) + p.Δ at hv
      change t + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      linarith
    · rintro B d ⟨hBK, hdD⟩
      subst B
      subst d
      refine ⟨block_preceq_refl K, le_rfl, ?_⟩
      intro b hb hne
      obtain ⟨l, hl, t, o, ho, ha, _, ht'⟩ := gate_source_path p c E rho hsch hk hK b hb hne
      have hdecode : ∃ r raw sup rows, (toWire p o).decode = some (.block r b raw sup rows) := by
        change (match (toWire p o).decode with
          | some (.block _ b _ _ _) => some b | _ => none) = _ at ho
        cases he : (toWire p o).decode with
        | none => rw [he] at ho; contradiction
        | some m =>
          cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
          subst b
          exact ⟨_, _, _, _, rfl⟩
      obtain ⟨r, raw, sup, rows, hdec⟩ := hdecode
      refine ⟨o, t, r, raw, sup, rows, ⟨l, hl, ha, b, ho, hb⟩, hdec, ?_⟩
      change t < 4 * p.Δ * (s : Int) + p.Δ at ht'
      change t + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      linarith
    · intro o t r b raw sup rows hr hdec
      obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
      have hb : blockOf? p o = some b := by
        change (match (toWire p o).decode with | some (.block _ b _ _ _) => some b | _ => none) = _
        rw [hdec]
      have heq := Option.some.inj (hb'.symm.trans hb)
      subst b'
      exact ⟨K, SA.earlyTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩

omit [Fintype V] in
/-- P3 F2.5a:4921–4945; bp02 §5.4. Class B, old-history head prefixes.
DC: SafetyRegimes.lean:69–75; successive selection/HEAD order analogue.
INTENTIONAL: retrospective event reads and every intervening F are explicit
(spec/fgsa-protocol.tex:2506–2513). Only old Continues is used. -/
theorem clean_gate_head_prefixes (hsch : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ) (hf : FGFoundation p c E rho)
    {i k : Nat} {x y : V} {s : Slot}
    (ht : IsGateTick p c rho i x (s + 1))
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i) :
    (∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s + 1 →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) ∧
    (∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k (s + 1))) := by
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have htime := (hsch.in_horizon _ (List.mem_of_getElem? ht)).2
  have hprev : ((4 * s + 6 : Nat) : Time) * p.Δ ≤ rho.horizon := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ ≤ rho.horizon at htime
    push_cast at htime ⊢
    nlinarith
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch hDelta x hx (4 * s + 6) hprev
  have he : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  rw [he] at hj
  have hji : j < i := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht (by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    nlinarith)
  have hbefore : ∀ j z, IsGateTick p c rho j z s → k < j := by
    intro j z hz
    exact V2.D.Engine.eventIndex_lt_of_time_lt hsch hk hz (by
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
        4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      nlinarith)
  obtain ⟨D, hD, _⟩ := hh.nonempty j x s hji hj
  have hDK := hh.continues j k x y s D hji (hbefore j x hj) hj hk hD
  have hresults : ∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s + 1 →
      Block.Preceq B (headAtIdx p c E rho k (s + 1)) := by
    intro r B hB hr
    rcases (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr)) with hrs | heq
    · exact block_preceq_trans (hh.ordered r s B D hB ⟨j, hji, x, hj, hD⟩ hrs) hDK
    · subst r
      obtain ⟨l, hl, z, hz, hB⟩ := hB
      exact hh.continues l k z y s B hl (hbefore l z hz) hz hk hB
  refine ⟨hresults, ?_⟩
  have hF : Block.Preceq (F_at p c E rho i x) (headAtIdx p c E rho k (s + 1)) := by
    rcases (hs.gateInputs x (s + 1) ht).1 with hg | ⟨r, B, hB, hr, hFB⟩
    · rw [hg]
      exact block_genesis_preceq _
    · exact block_preceq_trans hFB (hresults r B hB hr)
  intro l hl
  exact block_preceq_trans (eraseFG_preceq (hf.mono hn l i x hx hl).1) hF

omit [Fintype V] in
private theorem gate_block_stamp_lt (hsch : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) {j : Nat} {x : V} {t : Time}
    (hj : rho.events[j]? = some (.tick x t)) (ht : 0 < t)
    (B : Block) (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    GridCO.stampBlock (storeAt p c E rho j x).base B < t := by
  have hbm : B ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst := by
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hB
  change (((V2.D.Run.stateBefore E rho j x).st.base.blockStamp.find? _).map Prod.snd).getD _ < t
  cases he : (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.find? (fun row => row.1 == B) with
  | none =>
    obtain ⟨row, hr, hb⟩ := List.mem_map.mp hbm
    have hno := List.find?_eq_none.mp he row hr
    rw [hb, beq_self_eq_true] at hno
    contradiction
  | some row =>
    change row.2 < t
    have hmem := List.mem_of_find?_eq_some he
    rcases fgsa_block_stamp_source E rho j x row.1 row.2 hmem with hg | ⟨l, hl, _, _, _, _, hs⟩
    · rw [hg.2]
      exact ht
    · rw [hs]
      have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hsch hn
        (Nat.le_of_lt hl) x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l x),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hm
      exact hm.trans_lt (fgsa_preTick_now_lt E rho hsch hj ht)

private theorem gate_active_heads (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) {i : Nat} {x : V} {s : Slot}
    (hi : i < timeIdx rho b₀) (ht : IsGateTick p c rho i x (s + 1))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head (s + 1))) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head (s + 1))) q) (SA.voteTime p.toParams (s + 1)) = true →
      ∃ K t,
        rho.seatOf (.base (.head (s + 1))) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (s + 1))) q)
          (ofHead p ⟨.seat (.head (s + 1)) q, K⟩) t ∧
        baseVote (⟨.seat (.head (s + 1)) q, K⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1)))).blocks ∧
        K.slot ≤ s + 1 ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1))))
          (baseVote (⟨.seat (.head (s + 1)) q, K⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine (s + 1) ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1)))) K < GridCO.earlyTime p.toParams.engine (s + 1) ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (s + 1))).fg.F) K ∧ Block.Preceq B K := by
  intro q hy hawake
  let y := rho.seatOf (.base (.head (s + 1))) q
  have hsch := h.base.valid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
  have hcut : SA.gateTime p.toParams (s + 1) ≤ b₀ :=
    (V2.D.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
  have htimes : SA.voteTime p.toParams (s + 1) + p.Δ = SA.earlyTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams (s + 1) < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hvote : SA.voteTime p.toParams (s + 1) < SA.earlyTime p.toParams (s + 1) := by
    rw [← htimes]
    exact lt_add_of_pos_right _ hd
  have hvt : ((4 * (s + 1) + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  have het : ((4 * (s + 1) + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch h.base.delta y hy (4 * (s + 1) + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans (hcut.trans h.cut.2))))
  rw [hvt] at hk
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch h.base.delta x hx (4 * (s + 1) + 2)
    (het ▸ (hearly.le.trans (hcut.trans h.cut.2)))
  rw [het] at hj
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht hearly
  have hjread := fgsa_preTick_eq_timeRead E rho hsch h.base.noRestart hj
  let K := headAtIdx p c E rho k (s + 1)
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st (s + 1) := by
    have htick : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) = some k := by
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨l, hl⟩ : ∃ l, V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) = some l := by
        rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
        refine ⟨rho.events[k], List.getElem_mem hkl, ?_⟩
        rw [(List.getElem?_eq_some_iff.mp hk).2]
        exact decide_eq_true ⟨rfl, rfl⟩
      exact (fgsa_tick_unique E rho hsch (V2.D.Run.tickIdx?_spec hl) hk) ▸ hl
    have heK := vHead_eq_headAtIdx p c E rho hsch hk
    rw [vHead_def, postClock_def, preTick_def, htick] at heK
    exact (Option.some.inj heK).symm
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams (s + 1))).cstore (s + 1)
    rw [← hKeq] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head (s + 1)) q, K⟩)
      (SA.voteTime p.toParams (s + 1)) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ (s + 1) q K).mpr ⟨hawake, rfl, rfl, hKeq⟩
  have hprefix := clean_gate_head_prefixes p c E rho hsch h.base.noRestart h.base.delta hf
    ht hk hh hs
  obtain ⟨required, paths, hcov, hp⟩ := gate_path_coverage p c E rho h.base.valid
    h.base.noRestart h.base.delta b₀ h.healthy h.cut.2 ht hcut hy hk hKsource hprefix.2
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams (s + 1)) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  have hFearly : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams (s + 1)) x).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix.2 _ hidx
  have hpath := fgsa_active_path_of_coverage E rho h.base.valid h.base.noRestart h.base.delta
    (fun t => t + p.Δ) b₀ (SA.earlyTime p.toParams (s + 1)) 0 x K required paths hx hcov hp hFearly
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← hjread] at hm
    exact hm.1
  have hwindow : (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams (s + 1)) x).st.slot p ≤
      s + 1 + 1 := by
    rw [← hjread]
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hn
    have he := slotOf_offset p (s + 1) (2 * p.Δ) (by omega) (by omega)
    exact ((Internal.slotOf_mono (p := p) hn).trans_eq he).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho h.base.delta h.base.valid h.base.noRestart
    h.base.cstar (fun t => t + p.Δ) b₀ (s + 1) q K (SA.voteTime p.toParams (s + 1)) y x
    (by
      simpa only [h.base.delta] using
        Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀ h.healthy
            (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _))
    hy hem hx (by rw [htimes]; exact hearly.le.trans hcut) (lt_add_of_pos_right _ hd)
    (by rw [htimes]; exact hwindow)
  dsimp only at hr
  rw [htimes, ← hjread] at hr
  have htrans := clean_gate_stamps p c E rho hf h.base.noRestart (s := s + 1) hx
    (Nat.le_of_lt hji) hil _ K hr.1 hKearly
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams (s + 1)))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(hf.cumul h.base.noRestart j i x hx (Nat.le_of_lt hji) hil).2.1.subset hKearly,
      block_compatible_of_common (block_preceq_refl K) (hprefix.2 i le_rfl)⟩
  have hslot : K.slot ≤ s + 1 := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p (s + 1) p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams (s + 1) := by
    change 0 < 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ
    positivity
  refine ⟨K, SA.voteTime p.toParams (s + 1), hy, hem, htrans.1, hKg, hslot, ?_, ?_, ?_, hB k y hk⟩
  · rw [htrans.2.1]
    exact hr.2
  · rw [htrans.2.2]
    exact gate_block_stamp_lt p c E rho hsch h.base.noRestart hj hpos K hKearly
  · rw [clockPre_fg]
    exact hprefix.2 i le_rfl

/-- P3 F2.5a; bp02 §5.4. Class B, same-label history extension.
DC: Goldfish/Confirmation.lean:405, eligible_compatible; same compatibility.
INTENTIONAL: actual optional F-anchored reads (spec/fgsa-protocol.tex:2496–2513).
This covers old/new and new/new pairs without a successor Continues premise.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_same (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    {i : Nat} (hi : i < timeIdx rho b₀) :
    ∀ s B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (s, C) ∈ cleanResults p c E rho (i + 1) → Block.Compatible B C := by
  intro s B C ⟨j, hj, x, hx, hB⟩ ⟨k, hk, y, hy, hC⟩
  have hsch := h.base.valid.toScheduleWellFormed
  have hd : SA.gateTime p.toParams s ≤ b₀ :=
    (V2.D.Engine.index_lt_read_length_iff hsch b₀ hx).mp (show j < timeIdx rho b₀ by omega)
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  exact fgsa_sameLabel p c E rho h.base.valid h.base.noRestart h.base.delta s
    (Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hd h.cut.2)
    x y B C (hsch.honest_only _ (List.mem_of_getElem? hx))
    (hsch.honest_only _ (List.mem_of_getElem? hy))
    ((gateResultAt_eq_gateResult p c E rho hsch hx).symm.trans hB)
    ((gateResultAt_eq_gateResult p c E rho hsch hy).symm.trans hC)

private theorem gate_batch_of_history (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (hf : FGFoundation p c E rho) {i : Nat} {x : V} {s : Slot}
    (hi : i < timeIdx rho b₀) (ht : IsGateTick p c rho i x (s + 1))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (s + 1))
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v (s + 1)) <
      2 * SA.prefixSupport p.toParams v (s + 1) a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v (s + 1)) <
      2 * SA.prefixSupport p.toParams v (s + 1) B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  obtain ⟨H, hH, hb⟩ := clean_gate_batch p c E rho b₀ h hi ht
  apply fgsa_gate_batch_premises E rho h.base.valid h.base.cstar i x (s + 1) B H hb
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩)
  intro k hk
  exact gate_active_heads p c E rho b₀ h hf hi ht hh hs B hB k
    ((hH k).mp hk).1 ((hH k).mp hk).2

/-- P3 F2.5a; bp02 §5.4. Class B, new-gate nonemptiness.
DC: NamedConfirmationWalk.lean:38 and Goldfish/Confirmation.lean:494,567.
INTENTIONAL: the optional F-anchored raw result must pass the anchor test
(spec/fgsa-protocol.tex:2506–2513). Label zero returns genesis exactly.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_nonempty (b₀ : Time) :
    CleanCut₂ p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
    FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
    ∀ i x s, i < timeIdx rho b₀ → IsGateTick p c rho i x s →
      CleanHist p c E rho i → (∀ k, k ≤ i → CleanState p c E rho k) →
      ∃ B, gateResultAt p c E rho i = some (some B) ∧ (s = 0 → B = .genesis) := by
  intro h _ hf _ i x s hi ht hh hall
  cases s with
  | zero => exact ⟨.genesis, clean_gate_zero p c E rho b₀ h hf hi ht (hall i le_rfl), fun _ => rfl⟩
  | succ s =>
    have hb := gate_batch_of_history p c E rho b₀ h hf hi ht hh (hall i le_rfl)
      .genesis (fun _ _ _ => block_genesis_preceq _)
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (s + 1))
    obtain ⟨B, hB, _⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
      (eraseFG pre.fg.F) .genesis (s + 1)
      (block_compatible_of_common (block_preceq_refl _) (block_genesis_preceq _))
      hb.1 hb.2.1 hb.2.2
    refine ⟨B, (clean_gate_raw h.base.valid.toScheduleWellFormed ht).trans (congrArg some hB), ?_⟩
    intro hn
    exact (Nat.succ_ne_zero s hn).elim

/-- P3 F2.5a; bp02 §§5.4–5.5. Class B, add-only history extension.
DC: SafetyRegimes.lean:56–75 and NamedConfirmationWalk.lean:38.
INTENTIONAL: three event-prefix fields for actual F-anchored optional reads
(spec/fgsa-protocol.tex:2496–2525; lead Q2). The result adds no Continues field.
The first conjunct supplies the Ordered premise of clean_transfer_frame.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gate_history_osn (b₀ : Time) :
  CleanCut₂ p c E rho b₀ ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i, i < timeIdx rho b₀ → CleanGateTick p c rho i → CleanHist p c E rho i →
    (∀ k, k ≤ i → CleanState p c E rho k) →
    (∀ s r B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (r, C) ∈ cleanResults p c E rho (i + 1) → s < r → Block.Preceq B C) ∧
    (∀ s B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (s, C) ∈ cleanResults p c E rho (i + 1) → Block.Compatible B C) ∧
    (∀ j x s, j < i + 1 → IsGateTick p c rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) := by
  intro h hq hf hsrc i hi _ hh hall
  refine ⟨?_, clean_gate_same p c E rho b₀ h hi, ?_⟩
  · apply ordered_of_confirmation p c E rho h.base.valid.toScheduleWellFormed hh (hall i le_rfl)
    intro x s ht r B hB hrs
    cases s with
    | zero => exact (Nat.not_lt_zero r hrs).elim
    | succ s =>
      apply gate_batch_of_history p c E rho b₀ h hf hi ht hh (hall i le_rfl) B
      intro k y hk
      exact (clean_gate_head_prefixes p c E rho h.base.valid.toScheduleWellFormed
        h.base.noRestart h.base.delta hf ht hk hh (hall i le_rfl)).1 r B hB hrs
  · intro j x s hj ht
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hji | he
    · exact hh.nonempty j x s hji ht
    · subst j
      exact clean_gate_nonempty p c E rho b₀ h hq hf hsrc i x s hi ht hh hall


/-- P3 §§8.2–8.7 F2.5b; bp02 §§5.4–5.6. Class B, frozen history step.
DC: GSTZeroPreparedWalk.lean:546, SafetyRegimes.lean:53–80, and
JointHistoryGapsIdx.lean:26,141. INTENTIONAL divergence: FG-SA has an
F-anchored optional raw result, leases, and gate-before-action in one tick.
The event-prefix step proves Ordered before retrospective Continues
(bp02:553–613); it uses no closed safety theorem or successor state.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_gateHistStep (b₀ : Time) : CleanGateHistStep (ΔF := ΔF) p c E rho b₀ := by
  rw [CleanGateHistStep_def (ΔF := ΔF), CleanHistStep_def (ΔF := ΔF)]
  intro h hq hf hsrc i hi hgate hh hall
  have hOSN := clean_gate_history_osn p c E rho b₀ h hq hf hsrc i hi hgate hh hall
  refine ⟨hOSN.1, hOSN.2.1, hOSN.2.2, ?_⟩
  intro j k x y s B hj hkj ht hk hB
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hji | he
  · exact hh.continues j k x y s B hji hkj ht hk hB
  · subst j
    apply cleanTransfer p c E rho b₀ h hq hf hsrc i k x y s B hi hkj ht hk hh hall hB
    intro r C hC hrs
    exact hOSN.1 r s C B
      (cleanResults_mono (Nat.le_succ i) hC)
      (cleanResults_mem_succ_iff.mpr (Or.inr ⟨x, ht, hB⟩)) hrs

end AvailableChain.FGSA.Run
end
