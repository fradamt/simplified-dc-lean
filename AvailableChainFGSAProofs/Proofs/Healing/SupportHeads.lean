module
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.HeadCover
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Healing.FramePaths
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTransfer
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTicks

public section

/-! H-SUPPORT H.2 HEAD step (plan §4 step 7; S1 HEAD clause at labels after s+1).
Each step uses the honest HEAD batch of the previous label and a fresh witness W of an
honest HEAD of that label. The lease premise stays explicit at each step. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem heads_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–689; plan H-SUPPORT §4 step 7.
DC: SAME a state read before a tick at T has a slot at most the slot of T. -/
theorem healing_support_read_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {T : Time} (hi : rho.events[i]? = some (.tick x T))
    (d : Time) (hd : d ≤ T) :
    (V2.D.Run.stateBeforeTime E rho d x).st.slot p ≤ p.slotOf T := by
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (heads_idx_mono rho hd) x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) x),
    fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho T) x)] at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hS,
    Gen.V2.Duty.stateBefore_idxBefore E rho _ hS,
    ← fgsa_preTick_eq_timeRead E rho hS hN hi] at hm
  have hb := stateBefore_now_le_event_retained (fgsaClock p c)
    (fgsa_hrestore_now_retained p c)
    E rho hS hi x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x)] at hb
  exact Internal.slotOf_mono (p := p) (hm.trans hb)

private theorem heads_stamp_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp hf row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–689; plan H-SUPPORT §4 step 7.
DC: SAME a stored vote keeps its membership and its stamp at every later post-clock read. -/
theorem healing_support_vote_kept (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) {a b : Nat} (hab : a ≤ b) (y : V) (t : Time)
    (o : GridCO.Wire p.n .root) (ho : o ∈ (storeAt p c E rho a y).base.votes) :
    o ∈ (FGSA.clock p (storeAt p c E rho b y) t).base.votes ∧
      GridCO.stampVote (FGSA.clock p (storeAt p c E rho b y) t).base o =
        GridCO.stampVote (storeAt p c E rho a y).base o := by
  have hc := fgsa_store_cumulative p c E rho hN hab y
  have hk : o ∈ (storeAt p c E rho a y).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho a y).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho a y]
    exact ho
  have hkb : o ∈ (storeAt p c E rho b y).base.voteStamp.map Prod.fst := by
    obtain ⟨tail, he⟩ := hc.2.2.2.1
    rw [← he, List.map_append]
    exact List.mem_append_left _ hk
  constructor
  · rw [(clock_vn (storeAt p c E rho b y) t).1]
    change o ∈ (V2.D.Run.stateBefore E rho b y).st.base.votes
    rw [← fgsa_vote_stamp_keys E rho b y]
    exact hkb
  · change (((FGSA.clock p (storeAt p c E rho b y) t).base.voteStamp.find? _).map
      Prod.snd).getD _ = (((storeAt p c E rho a y).base.voteStamp.find? _).map Prod.snd).getD _
    rw [(clock_cumulative p _ _).2.2.2.1, heads_stamp_kept hc.2.2.2.1 o hk]
    cases hf : (storeAt p c E rho a y).base.voteStamp.find? (fun row => row.1 == o) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hk
      have hn := List.find?_eq_none.mp hf row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => rfl

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S1), 673–689 (IF.5 relay); plan H-SUPPORT §4 step 7.
DC: INTENTIONAL an honest label-i HEAD that covers B is, at the receiver's q_i read, a
clean resolved frozen vote that supports B: the vote arrives by e_i, and the HEAD
block arrives with strict stamps through the HEAD witness W (F1 + F2). -/
theorem healing_support_honest_batch_seat [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
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
  have hvv : SA.voteTime p.toParams i ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hv
  have hgsti : E.t_GST ≤ SA.voteTime p.toParams i := hgst.trans hhead
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon := hvv.trans hphase.2.1
  have hawake := hrec.awake z hk _ hgsti hhori
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk i hhori
  obtain ⟨hem, hhl⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams i)) i
  have hBK : Block.Preceq B K := hcover z hk K hhl
  -- The witness of z's HEAD reaches y before e_i, so the HEAD block has strict stamps.
  obtain ⟨Kfg, hKfull, hKe, W, _, hKW, _, hrelay⟩ :=
    healing_head_witness_relay (hroots := hrec.base.idealization)
      p c E rho mono crossing hE hN hDelta hrec.sync u v m J contested
      hgst hphase hk hjz hhead (hvi.trans hv)
  have hfz : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams i := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hWf : W ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams i) y).st.fg.TF := by
    have h := hrelay y hy W (KitFG.preceq_refl W)
    change W ∈ (V2.D.Run.stateBeforeTime E rho _ y).st.fg.TF at h
    have hc := (fgsa_store_cumulative p c E rho hN (heads_idx_mono rho hfz) y).1
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho _) y).st.fg.TF ⊆
      (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho _) y).st.fg.TF at hc
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS,
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hc
    exact hc h
  have hpath := healing_support_prefreeze_path E rho hS hN hiy hWf Kfg hKW
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hKe' : eraseFG Kfg = K := hKe
  have hKb : K ∈ dst.base.blocks := by
    rw [← hKe']
    exact (hinv.baseTree _).mpr ⟨Kfg, hpath.1, rfl⟩
  have hKst : GridCO.stampBlock dst.base K < SA.freezeTime p.toParams i := by
    rw [← hKe']
    exact hpath.2
  -- The HEAD block has slot at most i.
  have hKslot : K.slot ≤ i := by
    have hzinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho jz z) (SA.voteTime p.toParams i)
    have hKT := ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).1
    have hm := (hzinv.baseTree (eraseFG Kfg)).mpr ⟨Kfg, hKT, rfl⟩
    rw [clock_base_blocks, hKe'] at hm
    have hb := (fgsa_stateBefore_bounds E rho hS jz z).1 K hm
    have hpos : 0 < SA.voteTime p.toParams i := by
      change 0 < 4 * p.Δ * (i : Int) + p.Δ
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hjz hpos
    have hsl := Internal.slotOf_mono (p := p) (le_of_lt hn)
    have he : p.slotOf (SA.voteTime p.toParams i) = i :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho jz z) _).2.symm.trans
        (fgsa_vote_slot (c := c) _ i)
    exact hb.trans (hsl.trans_eq he)
  -- The vote arrives by e_i and keeps its stamp at the q_i read.
  have hvd : SA.voteTime p.toParams i + E.Δ ≤ SA.voteTime p.toParams i + E.Δ := le_rfl
  have hdt : SA.voteTime p.toParams i + E.Δ ≤ rho.horizon := by
    rw [hDelta]
    exact (hvi.trans hv).trans hphase.2.1
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
  have hstampv : GridCO.stampVote dst.base o < SA.freezeTime p.toParams i := by
    change GridCO.stampVote (FGSA.clock p _ _).base o < _
    rw [hods]
    change GridCO.stampVote (V2.D.Run.stateBefore E rho _ y).st.base o < _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact lt_of_lt_of_le hos (hdle.trans hfz)
  have hFK : Block.Compatible K (eraseFG dst.fg.F) := by
    rw [clock_fg]
    exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
      (Gen.Pure.block_preceq_trans hFB hBK)
  have hol : GridCO.headLabel? o = some i := rfl
  have hok : GridCO.headSeat? o = some k := rfl
  have hoK : GridCO.headTarget? o = some K.root := rfl
  have hresolve := actView_resolve_target p dst hinv
    (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho iy y)))
    o ((actView_blocks dst K).mpr ⟨hKb, hFK⟩) hoK
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
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst hinv) o hKb hoK,
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
ROOT-DIGEST W2b. Blueprint 21:748–783 (H.3), 1148–1252 (F1 + F2); plan H-SUPPORT §4 steps 3 and
7.
DC: INTENTIONAL an honest label-i HEAD that covers B gives a witness W ⪰ B. W reaches
the receiver before e_i, and at its q_i read Z and F are below W, with lo ≤ h(W). The
F-root case uses RXing; the top-J case uses the common J. -/
theorem healing_support_head_frame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Slot} (hhead : u ≤ SA.voteTime p.toParams i)
    {jz : Nat} {z : V} (hz : z ∈ rho.honest)
    (hjz : rho.events[jz]? = some (.tick z (SA.voteTime p.toParams i)))
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hv : SA.voteTime p.toParams (i + 1) ≤ v) {B : Block}
    (hBK : Block.Preceq B (headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
      (SA.voteTime p.toParams i)) i))
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ W, W ∈ (storeAt p c E rho
        (V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ)) y).fg.TF ∧
      Block.Preceq B (eraseFG W) ∧ FGBlock.Preceq (R_at p c E rho iy y).Z W ∧
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F W ∧
      (R_at p c E rho iy y).lo ≤ (heightView p W).h := by
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvsv : SA.voteTime p.toParams i ≤ SA.voteTime p.toParams (i + 1) :=
    (le_add_of_nonneg_right hd.le).trans hvi
  obtain ⟨Kfg, hKfull, hKe, W, _, hKW, hloW, hrelay⟩ :=
    healing_head_witness_relay (hroots := hroots)
      p c E rho mono crossing hE hN hDelta hsync u v m J contested
      hgst hphase hz hjz hhead (hvi.trans hv)
  have hBW : Block.Preceq B (eraseFG W) := by
    refine Gen.Pure.block_preceq_trans hBK ?_
    have hKe' : eraseFG Kfg = headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
      (SA.voteTime p.toParams i)) i := hKe
    rw [← hKe']
    exact eraseFG_preceq hKW
  have hZK : FGBlock.Preceq (FGSA.controls p ((fgsa p c).clock (rho.stateBefore E jz z)
      (SA.voteTime p.toParams i)).st).Z Kfg :=
    ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).2.2.1
  have hRz : FGSA.controls p ((fgsa p c).clock (rho.stateBefore E jz z)
      (SA.voteTime p.toParams i)).st = R_at p c E rho jz z := by
    change KitFG.treeStoreControlsView (heightView p) (FGSA.clock p _ _).fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho jz _).fg
    rw [clock_fg]
    rfl
  rw [hRz] at hZK hloW
  have hfz := healing_settled_frame_strict p c E rho crossing u v m J contested hphase jz z
    (healing_support_idxBefore_le p c E rho hS hjz hhead)
    (healing_phase_lt_timeIdx p c E rho hS hjz (hvsv.trans hv)).le hz
  have hfy := healing_settled_frame_strict p c E rho crossing u v m J contested hphase iy y
    (healing_support_idxBefore_le p c E rho hS hiy (hhead.trans hvsv))
    (healing_phase_lt_timeIdx p c E rho hS hiy hv).le hy
  have hWd : W ∈ (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ)) y).fg.TF := by
    have h := hrelay y hy W (KitFG.preceq_refl W)
    change W ∈ (V2.D.Run.stateBefore E rho _ y).st.fg.TF
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact h
  have hWy : W ∈ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hiy hvi) y).1 hWd
  have hloy : (R_at p c E rho iy y).lo ≤ (heightView p W).h := by
    have e1 : (R_at p c E rho iy y).lo = (R_at p c E rho jz z).lo :=
      hfy.2.2.1.trans hfz.2.2.1.symm
    rw [e1]
    exact hloW
  refine ⟨W, hWd, hBW, ?_⟩
  cases J with
  | some J0 =>
    obtain ⟨_, _, hZy, _, _, hFJ⟩ := hfy.2.2.2.1
    obtain ⟨_, _, hZz, _, _, _⟩ := hfz.2.2.2.1
    have hZW : FGBlock.Preceq J0 W := by
      rw [← hZz]
      exact KitFG.preceq_trans hZK hKW
    refine ⟨?_, KitFG.preceq_trans hFJ hZW, hloy⟩
    change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho iy y)).Z W
    rw [hZy]
    exact hZW
  | none =>
    obtain ⟨_, hZy, ⟨Kc, hKc, hKcF, hKclt⟩, _⟩ := hfy.2.2.2.1
    have hFW := crossing iy iy y y Kc W hy le_rfl hKc hKcF ⟨hy, hWy⟩
      (lt_of_lt_of_le hKclt hloy)
    refine ⟨?_, hFW, hloy⟩
    change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho iy y)).Z W
    rw [hZy]
    exact hFW

private theorem heads_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–715 (H.2 S1), 748–783 (H.3); plan H-SUPPORT §4 step 7.
DC: INTENTIONAL one H.2 HEAD step. If every honest label-i HEAD covers B, then every
honest HEAD at label i+1 inside the phase covers B. The honest batch of label i gives
majority and rival bounds (`batch_head_covers`); a fresh witness W of an honest label-i
HEAD gives the kept path and the frame; `hlease` is the lease premise at this read. -/
theorem healing_next_transfer_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams i)
    (hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hv : SA.voteTime p.toParams (i + 1) ≤ v)
    (hlease : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B) :
    Block.Preceq B (headVote p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))) (i + 1)) := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1))
  have hvi : SA.voteTime p.toParams i + p.Δ ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hvv : SA.voteTime p.toParams i ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvi).trans hv
  have hgsti : E.t_GST ≤ SA.voteTime p.toParams i := hgst.trans hhead
  have hhori : SA.voteTime p.toParams i ≤ rho.horizon := hvv.trans hphase.2.1
  -- The witness of the receiver's own label-i HEAD.
  obtain ⟨jy, hjy⟩ := healing_support_vote_tick E rho hS hDelta hy i hhori
  have hhl : headAtLabel p c E rho y i = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jy y).st (SA.voteTime p.toParams i)) i) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjy]
    rfl
  obtain ⟨W, hWd, hBW, hZW, hFW, hloy⟩ := healing_support_head_frame (hroots :=
    hrec.base.idealization) E rho mono crossing hE hN
    hDelta hrec.sync hgst hphase hhead hy hjy hy hiy hv (hcover y hy _ hhl)
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.treeStoreControlsView (heightView p) dst.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  have hWdst : W ∈ dst.fg.TF := by
    rw [hdfg]
    exact (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS hiy hvi) y).1 hWd
  have hFW' : Block.Preceq (eraseFG dst.fg.F) (eraseFG W) := by
    rw [hdfg]
    exact eraseFG_preceq hFW
  by_cases hBF : Block.Preceq B (eraseFG dst.fg.F)
  · exact preceq_headVote_of_preceq_F p dst hinv hBF (Nat.succ_pos i)
  have hFB : Block.Preceq (eraseFG dst.fg.F) B := by
    rcases Gen.Pure.block_preceq_total_of_common hFW' hBW with h | h
    · exact h
    · exact absurd h hBF
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B := hdfg ▸ hFB
  -- The kept path through the frozen q_i domain.
  have hread : postClock E rho y (SA.voteTime p.toParams (i + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (i + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiy]
    rfl
  have hdpos : 0 < SA.voteTime p.toParams i + p.Δ := by
    change 0 < 4 * p.Δ * (i : Int) + p.Δ + p.Δ
    positivity
  have hdfreeze : SA.voteTime p.toParams i + p.Δ ≤ SA.freezeTime p.toParams (i + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    change 4 * p.Δ * (i : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (i : Int) + 3 * p.Δ
    linarith
  have hfrozen := healing_frozen_path p c E rho hS hN hdpos hvi hdfreeze hWd hread
  let X := voterBlocks p dst (i + 1)
  have hkeep : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (domainR p dst X) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ :=
      eraseFG_ancestor_preceq hinv.fg.closed hWdst (Gen.Pure.block_preceq_trans hCB hBW)
    have hFA : FGBlock.Preceq dst.fg.F A := heads_lift
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := heads_lift
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hfrozen A hFA hAW, hFA, hZA, W,
        hfrozen W (hdfg ▸ hFW) (KitFG.preceq_refl W), hAW, hRd ▸ hloy⟩
  -- The live root is compatible with B.
  have hrows := hlease hFB0
  have hanchor : Block.Compatible (liveRoot p dst) B := by
    have hselect := Gen.Pure.foldl_select_mem (fun (best b : Block) =>
      best.depth < b.depth || (best.depth == b.depth && best.root < b.root))
      (dst.base.obligations.filterMap (fun row =>
        if dst.base.now < row.2.2 && decide (∃ X ∈ FGSA.fullTree p dst, eraseFG X = row.1)
        then some row.1 else none)) (eraseFG (FGSA.controls p dst).Z)
    change FGSA.liveRoot p dst = _ ∨ FGSA.liveRoot p dst ∈ _ at hselect
    rcases hselect with he | hm
    · rw [he]
      exact Gen.Pure.block_compatible_of_common (eraseFG_preceq (hRd ▸ hZW)) hBW
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · rw [← Option.some.inj hrow]
        exact hrows row hr
      · contradiction
  -- The honest batch of label i.
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head i)) k ∈ rho.honest)
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head i)) k) :=
    hrec.base.cstar (.base (.head i)) trivial
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head i)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hseat (k : Fin p.n) (hk : k ∈ Hon) := healing_support_honest_batch_seat E rho hrec
    mono crossing hgst hphase hhead hcover hy hiy hv hFB0 k ((hHmem k).mp hk)
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
  have hcov := batch_head_covers p dst X (FGSA.headVotes p dst (i + 1))
    (FGSA.headSupport p dst (i + 1)) Hon Hon.card (Gen.V2.Duty.faulty rho).card B
    (fgsa_headSupport_subset_headVotes E rho hE iy y i) rfl
    (fun k hk => (hseat k hk).2) (fun k hk => (hseat k hk).1) hother hb hanchor hkeep
  rw [fgsa_domainR_eq_filtered] at hcov
  rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero i)]
  exact hcov

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2 S1); plan H-SUPPORT §4 step 7, G8.
DC: INTENTIONAL the bounded H.2 HEAD induction. From a common honest HEAD prefix B at
label s+1, every honest HEAD at a label i ≥ s+1 with q_i ≤ v covers B. Each step uses
the honest batch of the previous label (no gate lookahead, G8). `hlease` is the lease
premise at each honest read after s+1. -/
theorem healing_heads_transfer [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hbase : SA.voteTime p.toParams (s + 1) ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z (s + 1) = some K → Block.Preceq B K)
    (hlease : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams (i + 1) ≤ v →
      ∀ iy y, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
      Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B) :
    ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact hbase
  | succ i hi ih =>
    intro hv z hz K hK
    have hvi : SA.voteTime p.toParams i ≤ SA.voteTime p.toParams (i + 1) := by
      change 4 * p.Δ * (i : Int) + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith
    have hsi : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams i := by
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (i : Int) + p.Δ
      have h : (s : Int) ≤ i := by exact_mod_cast (Nat.le_succ s).trans hi
      nlinarith
    unfold headAtLabel at hK
    rw [postClock_def, preTick_def] at hK
    cases hiz' : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams (i + 1)) with
    | none => rw [hiz'] at hK; cases hK
    | some iz =>
    rw [hiz'] at hK
    have hiz := V2.D.Run.tickIdx?_spec hiz'
    have hKeq := Option.some.inj hK
    subst hKeq
    exact healing_next_transfer_core E rho hrec mono crossing hgst hphase (hhead.trans hsi)
      (ih (hvi.trans hv)) hz hiz hv (hlease i hi hv iz z hz hiz)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–715 (H.1 + H.2 S1, fast arm); plan H-SUPPORT §4 steps 1–7.
DC: INTENTIONAL the S1 HEAD clause for a fast PhaseBody arm, under the per-label lease
premise `hlease` after s+1 (the s+1 lease bound is proved, G5). -/
theorem healing_fast_heads_transfer [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hlease : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams (i + 1) ≤ v →
      ∀ iy y, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
      Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B) :
    ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K :=
  healing_heads_transfer E rho hrec mono crossing hgst hphase hhead
    (fun hv _ hz _ hK => healing_first_transfer_fast E rho hrec mono crossing hgst hphase
      hhead hgate hx hnd hB hz hv hK) hlease

end AvailableChain.FGSA.Run
end
