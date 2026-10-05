module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepInputs
public import AvailableChainFGSAProofs.Proofs.Shared.Count

public section

/-! WC plan §6.5; DC the honest batch retains its original receipt deadlines. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

/-- WC plan §6.5; DC cumulative stamps retain their first receipt. -/
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


/-- WC plan §6.5; DC gate inputs retain the original stored stamps. -/
private theorem gate_stamps (hcumul : RStoreCumul p c E rho) (hn : V2.D.NoRestart rho)
    {j i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hji : j ≤ i) (hi : i ≤ rho.events.length)
    (o : GridCO.Wire p.n .root) (B : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v B = GridCO.stampBlock (storeAt p c E rho j x).base B := by
  intro v
  have hc := hcumul hn j i x hx hji hi
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
/-- WC plan §6.5; DC a HEAD path has actual earlier receipt origins. -/
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

/-- WC plan §6.5; DC path coverage uses each acceptance time and the inherited GST. -/
private theorem gate_path_coverage (hE : V2.D.ExecutionValid E rho)
    (_hn : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i k : Nat} {x y : V} {s : Slot} {K : Block}
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (ht : IsGateTick p c rho i x s) (hcut : SA.gateTime p.toParams s ≤ rho.horizon)
    (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) K) :
    ∃ required paths,
      ReceiptCoveragePremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
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
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨parent, he, hh⟩ := ha.1
    refine ⟨Or.inr ⟨y, hy, l, ha⟩,
      handles_wellFormed p c _ parent o hh (hE.wire l y parent t he), ?_⟩
    intro r a B hv
    have hh : blockOf? p o = none := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hv]
    rw [hh] at hb
    contradiction
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl K) (hF j (hj.trans hidx))
  · refine ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hD.trans hcut, le_rfl, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro o t hr
      have htt := htime o t hr
      refine ⟨Nat.zero_le _, htt.1,
        (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos), ?_⟩
      have hv := htt.2
      change t < 4 * p.Δ * (s : Int) + p.Δ at hv
      have hm : max t E.t_GST ≤ SA.voteTime p.toParams s := max_le hv.le hGST
      change max t E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      change max t E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hm
      linarith
    · rintro B d ⟨hBK, hdD⟩
      subst B
      subst d
      refine ⟨block_preceq_refl K, le_rfl, ?_⟩
      intro b hb hne
      obtain ⟨l, hl, t, o, ho, ha, _, ht'⟩ := gate_source_path hsch hk hK b hb hne
      have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
        change (match (toWire p o).decode with
          | some (.block _ N) => some N.erase | _ => none) = _ at ho
        cases he : (toWire p o).decode with
        | none => rw [he] at ho; contradiction
        | some m =>
          cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
          exact ⟨_, _, ho, rfl⟩
      obtain ⟨r, N, heN, hdec⟩ := hdecode
      refine ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, ?_⟩
      change t < 4 * p.Δ * (s : Int) + p.Δ at ht'
      have hm : max t E.t_GST ≤ SA.voteTime p.toParams s := max_le ht'.le hGST
      change max t E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      change max t E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hm
      linarith
    · intro o t r N hr hdec
      obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
      have hb : blockOf? p o = some N.erase := by
        change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
        rw [hdec]
      have heq := Option.some.inj (hb'.symm.trans hb)
      subst b'
      exact ⟨K, SA.earlyTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩


/-- WC plan §6.5; DC receipts before a tick have strictly earlier stamps. -/
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

/-- WC plan §6.5; DC an awake honest HEAD and its path arrive before the early tick. -/
private theorem gate_active_heads
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreCumul p c E rho) {i : Nat} {x : V} {s : Slot}
    (ht : IsGateTick p c rho i x s) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k s))
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq B (headAtIdx p c E rho k s)) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  intro q hy hawake
  let y := rho.seatOf (.base (.head s)) q
  have hsch := hvalid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
  have hcut : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have htimes : max (SA.voteTime p.toParams s) E.t_GST + p.Δ =
      SA.earlyTime p.toParams s := by
    rw [max_eq_left hGST]
    change 4 * p.Δ * ((s : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ <
      4 * p.Δ * ((s : Nat) : Int) + 6 * p.Δ
    linarith
  have hvote : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    rw [← htimes]
    exact (le_max_left _ _).trans_lt (lt_add_of_pos_right _ hd)
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + p.Δ
    push_cast
    ring
  have het : ((4 * s + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams s := by
    change ((4 * s + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * s + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans hcut)))
  rw [hvt] at hk
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch hdelta x hx (4 * s + 2)
    (het ▸ (hearly.le.trans hcut))
  rw [het] at hj
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht hearly
  have hjread := fgsa_preTick_eq_timeRead E rho hsch hnr hj
  let K := headAtIdx p c E rho k s
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams s)).st s := by
    change headAtIdx p c E rho k s = _
    unfold headAtIdx
    rw [hk]
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams s)).cstore s
    rw [← hKeq] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr ⟨hawake, rfl, rfl, congrArg
        Block.root hKeq⟩
  have hprefix := hfinal k y hk
  obtain ⟨required, paths, hcov, hp⟩ :=
    gate_path_coverage hvalid hnr hdelta hsync hGST ht hcut hy hk hKsource hprefix
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  have hFearly : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix _ hidx
  have hpath := fgsa_active_path_of_coverage (hroots := hroots)
    E rho hvalid hnr hdelta
    (fun t => max t E.t_GST + p.Δ) rho.horizon (SA.earlyTime p.toParams s) 0 x K
    required paths hx hcov hp hFearly
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← hjread] at hm
    exact hm.1
  have hwindow : (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.slot p ≤
      s + 1 := by
    rw [← hjread]
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hn
    have he := slotOf_offset p s (2 * p.Δ) (by omega) (by omega)
    exact ((Internal.slotOf_mono (p := p) hn).trans_eq he).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho hdelta hvalid hnr
    hcstar (fun t => max t E.t_GST + p.Δ) rho.horizon s q K.root (SA.voteTime p.toParams s) y x
    (by
      simpa only [hdelta] using
        Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
            (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _))
    hy hem hx (by rw [htimes]; exact hearly.le.trans hcut)
    ((le_max_left _ _).trans_lt (lt_add_of_pos_right _ hd))
    (by rw [htimes]; exact hwindow)
  dsimp only at hr
  rw [htimes, ← hjread] at hr
  have htrans := gate_stamps hcumul hnr (s := s) hx
    (Nat.le_of_lt hji) hil _ K hr.1 hKearly
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(hcumul hnr j i x hx (Nat.le_of_lt hji) hil).2.1.subset hKearly,
      block_compatible_of_common (block_preceq_refl K) (hprefix i le_rfl)⟩
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p s p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams s := by
    change 0 < 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    positivity
  refine ⟨K, SA.voteTime p.toParams s, hy, hem, htrans.1, hKg, hslot, ?_, ?_, ?_, hB k y hk⟩
  · rw [htrans.2.1]
    exact hr.2
  · rw [htrans.2.2]
    exact gate_block_stamp_lt hsch hnr hj hpos K hKearly
  · rw [clockPre_fg]
    exact hprefix i le_rfl


/-- WC plan §6.5; DC the actual awake batch gives both anchor and target majorities. -/
theorem wc_gateBatch [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExact p c E rho)
  (_hmeta : RFrame p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i x s, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s → ∀ B,
    (∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq B (headAtIdx p c E rho k s)) →
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  classical
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel B hB
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hcut : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hc : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hhead := wc_gateHeads ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have hF := wc_gateFinalOrigin ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k s) := by
    intro k y hk j hji
    have hh := hhead k y (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk
    apply block_preceq_trans (eraseFG_preceq (hmono hnr j i x hx hji).1)
    rcases hF with hF | ⟨l, z, r, C, hr, hrs, hFC⟩
    · exact block_preceq_trans hF hh.1
    · exact block_preceq_trans hFC (hh.2 l z r C hr hrs)
  let A := Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (hcstar (.base (.head s)) trivial)
  let H := A.image e.symm
  have hH : ∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true := by
    intro k
    have he : k ∈ H ↔ e k ∈ A := by
      change k ∈ A.image e.symm ↔ e k ∈ A
      simp only [Finset.mem_image, e.symm_apply_eq]
      exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hk => ⟨e k, hk, rfl⟩⟩
    rw [he]
    change rho.seatOf (.base (.head s)) k ∈
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) ↔ _
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.mem_filter
  have hv : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans (b := SA.gateTime p.toParams s) _ hcut
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hcard : H.card = A.card := Finset.card_image_of_injective A e.symm.injective
  have hb : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card :=
    ⟨hcard ▸ hpart s (Nat.succ_le_of_lt hslabel) hv⟩
  apply fgsa_gate_batch_premises E rho hvalid hcstar i x s B H hb
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩)
  intro k hk
  exact gate_active_heads hvalid hnr hdelta hcstar hroots hsync hcumul ht hGST hfinal B hB
    k ((hH k).mp hk).1 ((hH k).mp hk).2

end AvailableChain.FGSA.Run
end
