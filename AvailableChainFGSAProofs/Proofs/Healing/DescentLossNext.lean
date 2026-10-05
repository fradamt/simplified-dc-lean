module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLoss
public import AvailableChainFGSAProofs.Proofs.Healing.SupportHeads

public section

/-! H-DESCENT D2 (H.13): the continuation transfer at labels l ≥ sB + 2 in the
moving frame. The H.2 receipt and count of `healing_support_honest_batch_seat`
and `healing_next_transfer_core` with a per-vote relay of each honest HEAD
block (label-local synchrony on [v_i, v_(i+1)]) instead of the PhaseInterval
witness relay, and with the kept path from a domain witness of the HEAD view. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem next_idx_mono : Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

omit [DecidableEq V] in
private theorem next_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ u N, o = ofWire p ⟨.proposer u, .proposal N⟩ ∧ N.erase = b := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i u N
    refine ⟨u, N, ?_, h⟩
    apply toWire_injective (p := p)
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd


omit [DecidableEq V] in
private theorem next_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:673–689, 709–715 (H.2 relay of each honest HEAD); plan
fgsa-s5-m5-d2d4 B `cause` (H.2 re-proved without PhaseInterval).
DC: INTENTIONAL per-block relay with label-local synchrony on [v_s, v_(s+1)],
not TDel. A block stamped before e_s in an honest store reaches each honest
receiver of the v_(s+1) tick before z_s when the receiver's finality is below
it. The window ends at v_(s+1), so the receiver tick bounds the horizon (no
d_s cut). -/
theorem healing_block_receipt_sync (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hDelta : E.Δ = p.Δ) (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.voteTime p.toParams (s + 1)))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (K : Block)
    (hK : K ∈ (storeAt p c E rho ix x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho ix x).base K < SA.earlyTime p.toParams s)
    (hF : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st).fg.F) K)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ Y : FGBlock (Fin p.n), eraseFG Y = K ∧
      Y ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.fg.TF := by
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
    (SA.voteTime p.toParams (s + 1))).st
  have hsch := hE.toScheduleWellFormed
  let D := SA.freezeTime p.toParams s
  have hFpost : st.fg.F = (storeAt p c E rho iy y).fg.F := by
    change (clock p _ _).fg.F = _
    rw [clock_fg]
    rfl
  have hDiy : V2.D.Run.idxBefore rho D ≤ iy := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hiy D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  by_cases hg : K = .genesis
  · subst K
    exact ⟨.genesis, rfl, (storeBundle_stateBeforeTime E rho D y).cstore.fg.gen⟩
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity
  obtain ⟨j, _, t, o, ho, ha, ht⟩ :=
    fgsa_block_accepted_before E rho hsch ix x K _ hg hpub hz hK hstamp
  obtain ⟨u, N, rfl, heN⟩ := next_decode p ho
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hdz : dl t < D := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) <
        4 * p.Δ * (s : Int) + 2 * p.Δ := max_lt ht (by linarith)
    linarith
  have hdcut : dl t ≤ cut := by
    refine (le_of_lt hdz).trans (le_trans ?_ hcut)
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (dl t) ≤ iy :=
    (next_idx_mono p c rho (le_of_lt hdz)).trans hDiy
  have hFd : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho (dl t) y).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hsch]
    refine Gen.Pure.block_preceq_trans (eraseFG_preceq ?_) (hFpost ▸ hF)
    have h := fgsa_monoAlong_preceq_F p c (storeAt p c E rho (V2.D.Run.idxBefore rho (dl t)) y).fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at h
    exact V2.D.Engine.stateBefore_stable _ h.1 h.2.1 h.2.2 E rho hidx y
      (hN.restartFree y _ iy) (KitFG.preceq_refl _)
  obtain ⟨Y, hY, hYK⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hDelta hE hN dl cut u N t y
    hD (Or.inr ⟨x, hx, j, ha⟩) hy hdcut (hlt t)
    (by simpa only [heN] using
      Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFd)
  refine ⟨Y, hYK.trans heN, ?_⟩
  have hc := (fgsa_store_cumulative p c E rho hN (next_idx_mono p c rho (le_of_lt hdz)) y).1
  change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (dl t)) y).st.fg.TF ⊆
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.fg.TF at hc
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hsch,
    Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hc
  exact hc hY

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:673–689, 709–715 (H.2 relay of each honest HEAD); plan
fgsa-s5-m5-d2d4 B `cause`. DC: INTENTIONAL per-block relay (not TDel). The
relayed block of `healing_block_receipt_sync` has its whole FG path in the
post-clock store of the v_(s+1) tick, with strict stamps before z_s. -/
theorem healing_block_path_sync (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hDelta : E.Δ = p.Δ) (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.voteTime p.toParams (s + 1)))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (K : Block)
    (hK : K ∈ (storeAt p c E rho ix x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho ix x).base K < SA.earlyTime p.toParams s)
    (hF : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st).fg.F) K)
    (hroots : NamedRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Kfg : FGBlock (Fin p.n), eraseFG Kfg = K ∧
      ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A Kfg →
        A ∈ st.fg.TF ∧ GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st
  obtain ⟨Y, hYK, hYD⟩ := healing_block_receipt_sync (hroots := hroots)
    p c E rho hE hN hDelta s hSync hx hy hiy
    K hK hstamp hF
  exact ⟨Y, hYK, healing_support_prefreeze_path E rho hE.toScheduleWellFormed hN hiy hYD⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (relay input). DC: SAME stamps.
A stored block has a stamp at most the local clock of its store. -/
theorem healing_block_stamp_le_now (hs : V2.D.ScheduleWellFormed E rho)
    (hN : V2.D.NoRestart rho) {jz : Nat} {z : V}
    {K : Block} (hK : K ∈ (storeAt p c E rho jz z).base.blocks) :
    GridCO.stampBlock (storeAt p c E rho jz z).base K ≤
      (V2.D.Run.stateBefore E rho jz z).st.base.now := by
  have ht0 : 0 ≤ (V2.D.Run.stateBefore E rho jz z).st.base.now := by
    rcases V2.D.Engine.stateBefore_now_source_noRestart (fgsaClock p c) E rho hN jz z with
      h | ⟨j, -, hj⟩
    · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at h
      rw [h]
    · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at hj
      exact (hs.in_horizon _ (List.mem_of_getElem? hj)).1
  have hkeys : K ∈ (storeAt p c E rho jz z).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho jz z).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho jz z).«meta».stampKeys]
    exact hK
  unfold GridCO.stampBlock
  cases hf : (storeAt p c E rho jz z).base.blockStamp.find? (fun row => row.1 == K) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
    have hn := List.find?_eq_none.mp hf row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row =>
    simp only [Option.map_some, Option.getD_some]
    have hrm := List.mem_of_find?_eq_some hf
    have hre : row.1 = K := by simpa only [beq_iff_eq] using List.find?_some hf
    have hm : (K, row.2) ∈ (V2.D.Run.stateBefore E rho jz z).st.base.blockStamp := by
      rw [← hre]
      exact hrm
    rcases fgsa_block_stamp_source E rho jz z K row.2 hm with ⟨-, h0⟩ | ⟨j, hj, -, -, -, -, he⟩
    · rw [h0]
      exact ht0
    · rw [he]
      have h := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hs hN
        (le_of_lt hj) z
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j z),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at h
      exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S1), 673–689 (IF.5 relay); plan fgsa-s5-m5-d2d4 B
`cause` (H.2 receipt re-proved without PhaseInterval). DC: INTENTIONAL moving
frame. An honest label-i HEAD that covers B is, at the receiver's v_(i+1) read,
a clean resolved frozen vote that supports B. The vote arrives by e_i, and the
HEAD block arrives with strict stamps by the per-block relay
(`healing_block_path_sync`), not by a phase witness relay. -/
theorem healing_batch_seat_sync [Fintype V] {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {i : Slot} {B : Block} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B)
    (k : Fin p.n) (hk : rho.seatOf (.base (.head i)) k ∈ rho.honest) :
    Gen.AC.Root.poolSupports (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.blocks
      (FGSA.headSupport p (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))) (i + 1)) k B = true ∧
    GridCO.equivocates (FGSA.headVotes p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1)) k = false := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  let z := rho.seatOf (.base (.head i)) k
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvh : SA.voteTime p.toParams (i + 1) ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hvh
  have hawake := hrec.awake z hk _ hgsti hhori
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk i hhori
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams i)) i
  have hBK : Block.Preceq B K := hcover z hk K hhl
  -- The HEAD block is stored at z before e_i.
  have hzinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho jz z) (SA.voteTime p.toParams i)
  have hKz : K ∈ (storeAt p c E rho jz z).base.blocks := by
    have hm := headVote_stored p _ hzinv i
    rwa [clock_base_blocks] at hm
  have hKstz : GridCO.stampBlock (storeAt p c E rho jz z).base K < SA.earlyTime p.toParams i := by
    have hnow : (V2.D.Run.stateBefore E rho jz z).st.base.now ≤ SA.voteTime p.toParams i := by
      have h := V2.D.Engine.stateBefore_now_le_event_noRestart (fgsaClock p c) E rho hS hN hjz z
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho jz z)] at h
      exact h
    refine lt_of_le_of_lt ((healing_block_stamp_le_now p c E rho hS hN hKz).trans hnow) ?_
    change 4 * p.Δ * (i : Int) + p.Δ < 4 * p.Δ * (i : Int) + 2 * p.Δ
    linarith
  -- The HEAD block reaches y with strict stamps (per-block relay on [v_i, v_(i+1)]).
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgsti (by rw [hDelta]; exact hvi) hvh
  have hFK : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (i + 1))).st).fg.F) K := by
    change Block.Preceq (eraseFG (FGSA.clock p (storeAt p c E rho iy y) _).fg.F) K
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans hFB hBK
  obtain ⟨Kfg, hKe', hpath⟩ := healing_block_path_sync (hroots := hrec.base.idealization)
    p c E rho hE hN hDelta i hSync
    hk hy hiy K hKz hKstz hFK
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hKb : K ∈ dst.base.blocks := by
    rw [← hKe']
    exact (hinv.baseTree _).mpr ⟨Kfg, (hpath Kfg (KitFG.preceq_refl _)).1, rfl⟩
  have hKst : GridCO.stampBlock dst.base K < SA.freezeTime p.toParams i := by
    rw [← hKe']
    exact (hpath Kfg (KitFG.preceq_refl _)).2
  -- The HEAD block has slot at most i.
  have hKslot : K.slot ≤ i := by
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hKz
    have hpos : 0 < SA.voteTime p.toParams i := by
      change 0 < 4 * p.Δ * (i : Int) + p.Δ
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hjz hpos
    have hsl := Internal.slotOf_mono (p := p) (le_of_lt hn)
    have he : p.slotOf (SA.voteTime p.toParams i) = i :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ i)
    exact hb.trans (hsl.trans_eq he)
  -- The vote arrives by e_i and keeps its stamp at the v_(i+1) read.
  have hvd : SA.voteTime p.toParams i + E.Δ ≤ SA.voteTime p.toParams i + E.Δ := le_rfl
  have hdt : SA.voteTime p.toParams i + E.Δ ≤ rho.horizon := by
    rw [hDelta]
    exact hvi.trans hvh
  obtain ⟨dl, cut, hD, _, hlt, hdl, _, hdcut, _⟩ :=
    Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ hrec.sync
      (fgsaDelay_nonrow E.Δ _) hgsti hvd hdt
  have hdle : dl (SA.voteTime p.toParams i) ≤ SA.voteTime p.toParams i + p.Δ := by
    have h := hdl (SA.voteTime p.toParams i)
    rwa [max_self, hDelta] at h
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams i)) y).st.slot p ≤
      i + 1 := by
    have h := healing_support_read_window E rho hS hN hiy _ (hdle.trans hvi)
    have he : p.slotOf (SA.voteTime p.toParams (i + 1)) = i + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho iy y) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ (i + 1))
    exact h.trans_eq he
  have hcut : dl (SA.voteTime p.toParams i) ≤ cut := by
    refine hdle.trans (le_trans ?_ hdcut)
    rw [hDelta]
  obtain ⟨hom, hos⟩ := fgsa_honest_head_receipt E rho hDelta hE hN hrec.base.cstar dl cut i k K.root
    (SA.voteTime p.toParams i) z y hD hk hem hy hcut (hlt _) hwindow
  let o := baseVote (⟨.seat (.head i) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams i)) ≤ iy :=
    healing_support_idxBefore_le p c E rho hS hiy (hdle.trans hvi)
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (dl (SA.voteTime p.toParams i))) y).base.votes := by
    change o ∈ (V2.D.Run.stateBefore E rho _ y).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, hods⟩ := healing_support_vote_kept E rho hN hidx y
    (SA.voteTime p.toParams (i + 1)) o hom'
  have hfz : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hstampv : GridCO.stampVote dst.base o < SA.freezeTime p.toParams i := by
    change GridCO.stampVote (FGSA.clock p _ _).base o < _
    rw [hods]
    change GridCO.stampVote (V2.D.Run.stateBefore E rho _ y).st.base o < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact lt_of_lt_of_le hos (hdle.trans hfz)
  have hFK' : Block.Compatible K (eraseFG dst.fg.F) := by
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hol : GridCO.headLabel? o = some i := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p dst hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho iy y)))
    o ((actView_blocks dst K).mpr ⟨hKb, hFK'⟩) hoK
  -- The vote is in the frozen support arm and supports B.
  have hsupp : o ∈ FGSA.headSupport p dst (i + 1) := by
    change o ∈ List.eraseDups (_ ++ _)
    rw [List.mem_eraseDups, List.mem_append]
    left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hod, ?_⟩, ?_⟩
    · simpa only [Nat.add_sub_cancel, hol] using beq_self_eq_true (some i)
    · unfold GridCO.resolvedBefore
      rw [hresolve]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel,
        hol, Option.getD_some]
      exact ⟨⟨hKslot, hstampv⟩, hKst⟩
  have hvs : Gen.AC.Root.voteSupports dst.base.blocks B o = true := by
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p _ hinv) o hKb hoK,
        hKb, by simpa only [hol, Option.getD_some] using hKslot, hBK⟩
  refine ⟨(Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr ⟨o, hsupp, hok, hvs⟩, ?_⟩
  -- Every stored label-i vote of the honest seat is its emitted HEAD.
  have hall : ∀ w ∈ GridCO.votesAt (storeAt p c E rho iy y).base i,
      GridCO.headSeat? w = some k → w = o := by
    intro w hw hwk
    obtain ⟨hwm, hwl⟩ := List.mem_filter.mp hw
    exact fgsa_honest_head_eq_of_stored E rho hE iy y i k K.root _ hk hem w hwm
      (by simpa only [beq_iff_eq] using hwl) hwk
  have hnoeq : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = false := by
    cases he : GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k with
    | false => rfl
    | true =>
      obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
      exact absurd ((hall a ha hka).trans (hall b hb hkb).symm) hne
  cases he : GridCO.equivocates (FGSA.headVotes p dst (i + 1)) k with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, ha, b, hb, hne, hka, hkb⟩ := (cap_pair _ k).mp he
    have hprov := fgsa_headVotes_provenance E rho hE hN iy y i hiy
    have hone : ∀ w ∈ FGSA.headVotes p dst (i + 1), GridCO.headSeat? w = some k → w = o := by
      intro w hw hwk
      rcases hprov w hw k hwk with hm | heq
      · exact hall w hm hwk
      · change GridCO.equivocates (GridCO.votesAt (storeAt p c E rho iy y).base i) k = true at heq
        rw [hnoeq] at heq
        contradiction
    exact hne ((hone a ha hka).trans (hone b hb hkb).symm)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2 S1), 748–783 (H.3); plan fgsa-s5-m5-d2d4 B `cause`
(continuation scores, H.2 re-proved without PhaseInterval). DC: INTENTIONAL
moving frame. If every honest label-i HEAD covers B, and B is in the domain of
an ancestor-closed part X of the frozen HEAD view of an honest node y at
v_(i+1), and the live leases of that read are compatible with B, then the HEAD
of y at label i + 1 covers B. The honest batch of label i gives the majority
and rival bounds (`batch_head_covers`); the domain gives the kept path. -/
theorem healing_next_transfer_domain [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    {i : Slot} {B : FGBlock (Fin p.n)} (hgsti : E.t_GST ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
      Block.Preceq (eraseFG B) K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X)
    (hlease : ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 (eraseFG B)) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (i + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans
      (hS.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.storeControlsView (heightView p) dst.fg =
      KitFG.storeControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  obtain ⟨-, hFB, hZB, W, hWX, hBW, hloW⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho iy y) X B).mp hD
  have hvW : W ∈ voterBlocks p dst (i + 1) := hXv hWX
  have hWdst : W ∈ dst.fg.TF := (Finset.mem_filter.mp hvW).1
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) (eraseFG B) :=
    eraseFG_preceq hFB
  -- The kept path through the frozen domain.
  let Xv := voterBlocks p dst (i + 1)
  have hkeep : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C (eraseFG B) →
      C ∈ erasedList dst (domainR p dst Xv) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hWdst
      (Gen.Pure.block_preceq_trans hCB (eraseFG_preceq hBW))
    have hFA : FGBlock.Preceq dst.fg.F A := next_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := next_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hXv (hXc W hWX A hAW), hFA, hZA, W, hvW, hAW, hRd ▸ hloW⟩
  -- The live root is compatible with B.
  have hanchor : Block.Compatible (liveRoot p dst) (eraseFG B) := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he, hRd]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq hZB)
        (Gen.Pure.block_preceq_refl _)
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hlease row hr
      · contradiction
  -- The honest batch of label i.
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head i)) k ∈ rho.honest)
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head i)) k) :=
    hrec.base.cstar (.base (.head i)) trivial
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head i)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := healing_batch_seat_sync p c E rho hrec hgsti
    hcover hy hiy hFB0 k ((hHmem k).mp hk)
  have hHon : Hon.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective Hon hbij.1]
    congr 1
    ext z
    simp only [Hon, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, hz, rfl⟩
  have hawk : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams i) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun z hz => hrec.awake z hz _ hgsti hhori)
  have hb : Gen.Pure.Batch Hon.card (Gen.V2.Duty.faulty rho).card := by
    have h := (hrec.batch hgsti hhori).lt
    rw [hawk] at h
    exact ⟨hHon ▸ h⟩
  have hother : ((GridCO.seats p.n (FGSA.headVotes p dst (i + 1))).toFinset \ Hon).card ≤
      (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head i)))
    · intro k hk
      obtain ⟨_, hn⟩ := Finset.mem_sdiff.mp hk
      rw [Finset.mem_coe, Gen.V2.Duty.faulty_def]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      exact hn ((hHmem k).mpr hh)
    · intro k _ j _ he
      exact hbij.1 he
  have hcov := batch_head_covers p dst Xv (FGSA.headVotes p dst (i + 1))
    (FGSA.headSupport p dst (i + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card (eraseFG B)
    (fgsa_headSupport_subset_headVotes E rho hE iy y i) rfl
    (fun k hk => (hseat k hk).2) (fun k hk => (hseat k hk).1) hother hb hanchor hkeep
  rw [domainR_eq_storeFrame] at hcov
  rw [healing_headAtIdx_tick p c E rho hiy]
  change Block.Preceq _ (headVote p dst (i + 1))
  rw [headVote_eq, ite_eq_right (Nat.succ_ne_zero i)]
  exact hcov

end AvailableChain.FGSA.Run
end
