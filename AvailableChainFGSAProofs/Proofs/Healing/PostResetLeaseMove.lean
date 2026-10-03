module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossCause
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint -- shake: keep (J4A2-2 step types)

public section

/-! Blueprint 21 H.15:2916–2923, H.2:709–746; plan J4A2-2 G2.
B1/B13/B17/B18. DC: INTENTIONAL reader time after freeze, including
proposal ticks. The prior high field and emitted-source no-loss supply
the domain guards. No THigh input or successor service field is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem leaseMove_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  preceq_of_eraseFG_preceq (KitFG.viewRootInj_all {A, B})
    ⟨A, by simp, KitFG.preceq_refl A⟩ ⟨B, by simp, KitFG.preceq_refl B⟩ h

omit [DecidableEq V] in
private theorem leaseMove_decode {o : Obj p} {b : Block}
    (h : blockOf? p o = some b) :
    ∃ u raw sup rows, o = ofWire p ⟨.proposer u, .proposal b raw sup rows⟩ := by
  have hd : ∃ u raw sup rows, (toWire p o).decode = some (.block u b raw sup rows) := by
    change (match (toWire p o).decode with
      | some (.block _ b _ _ _) => some b | _ => none) = _ at h
    cases hd : (toWire p o).decode with
    | none => rw [hd] at h; contradiction
    | some m =>
      cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
      subst b
      exact ⟨_, _, _, _, rfl⟩
  obtain ⟨u, raw, sup, rows, hd⟩ := hd
  refine ⟨u, raw, sup, rows, ?_⟩
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem leaseMove_block_receipt (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hDelta : E.Δ = p.Δ) (s : Slot) {t : Time} (hafter : SA.freezeTime p.toParams s < t)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      t)
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t))
    (K : Block)
    (hK : K ∈ (storeAt p c E rho ix x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho ix x).base K < SA.earlyTime p.toParams s)
    (hF : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      t).st).fg.F) K) :
    ∃ Y : FGBlock (Fin p.n), eraseFG Y = K ∧
      Y ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.fg.TF := by
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
    t).st
  have hsch := hE.toScheduleWellFormed
  let D := SA.freezeTime p.toParams s
  have hFpost : st.fg.F = (storeAt p c E rho iy y).fg.F := by
    change (clock p _ _).fg.F = _
    rw [clock_fg]
    rfl
  have hDiy : V2.D.Run.idxBefore rho D ≤ iy :=
    healing_support_idxBefore_le p c E rho hsch hiy hafter.le
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
  obtain ⟨j, _, tr, o, ho, ha, ht⟩ :=
    fgsa_block_accepted_before E rho hsch ix x K _ hg hpub hz hK hstamp
  obtain ⟨u, raw, sup, rows, rfl⟩ := leaseMove_decode p ho
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hdz : dl tr < D := by
    have hb := hb tr
    rw [hDelta] at hb
    change tr < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    change dl tr ≤ max tr (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl tr < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    have hh : max tr (4 * p.Δ * (s : Int) + p.Δ) <
        4 * p.Δ * (s : Int) + 2 * p.Δ := max_lt ht (by linarith)
    linarith
  have hdcut : dl tr ≤ cut :=
    (le_of_lt hdz).trans (hafter.le.trans hcut)
  have hidx : V2.D.Run.idxBefore rho (dl tr) ≤ iy :=
    (healing_phase_idxBefore_mono p c rho (le_of_lt hdz)).trans hDiy
  have hFd : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho (dl tr) y).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl tr) hsch]
    refine Gen.Pure.block_preceq_trans (eraseFG_preceq ?_) (hFpost ▸ hF)
    have h := fgsa_monoAlong_preceq_F p c
      (storeAt p c E rho (V2.D.Run.idxBefore rho (dl tr)) y).fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at h
    exact V2.D.Engine.stateBefore_stable _ h.1 h.2.1 h.2.2 E rho hidx y
      (hN.restartFree y _ iy) (KitFG.preceq_refl _)
  obtain ⟨Y, hY, hYK⟩ := fgsa_proposal_receipt E rho hDelta hE hN dl cut u K raw sup rows tr y
    hD (Or.inr ⟨x, hx, j, ha⟩) hy hdcut (hlt tr)
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFd)
  refine ⟨Y, hYK, ?_⟩
  have hc := (fgsa_store_cumulative p c E rho hN
    (healing_phase_idxBefore_mono p c rho (le_of_lt hdz)) y).1
  change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (dl tr)) y).st.fg.TF ⊆
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.fg.TF at hc
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho (dl tr) hsch,
    Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hc
  exact hc hY


private theorem leaseMove_source_receipt [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot} (hK : SourceBefore p c E rho i K s)
    {u : Slot} (hsu : s ≤ u) (hgst : E.t_GST ≤ SA.voteTime p.toParams u)
    {k : Nat} {x : V} {t : Time}
    (hafter : SA.freezeTime p.toParams u < t) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x t))
    (hF : FGBlock.Preceq (storeAt p c E rho k x).fg.F K) :
    K ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams u)) x).fg.TF := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  obtain ⟨j, y, r, a, -, ha, hKs, rfl⟩ := hK
  obtain ⟨-, -, -, -, -, st, hst, hτ⟩ :=
    healing_source_decode p c E rho emittedNonempty emittedName ha hKs
  rw [gateIn_def, preTick_def] at hst
  cases hix' : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams (r * p.R)) with
  | none => rw [hix'] at hst; cases hst
  | some ix =>
  rw [hix'] at hst
  have hst' := Option.some.inj hst
  subst hst'
  obtain ⟨-, o, -, ho, -, hsup⟩ :=
    healing_support_honest_seat rho hrec.base.cstar hrec.fault _ _ _ hτ
  obtain ⟨K', hK', hKm', hKst', -, -, -⟩ := healing_support_clean_target E rho o ho
  have hKK' : Block.Preceq (eraseFG K) K' := by
    rw [Gen.AC.voteSupports_def, hK'] at hsup
    exact (Bool.and_eq_true_iff.mp hsup).2
  have hvh : t ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hk)).2
  have hvu : SA.voteTime p.toParams u + E.Δ ≤ t := by
    rw [hDelta]
    refine le_trans ?_ hafter.le
    change 4 * p.Δ * (u : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (u : Int) + 3 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvu hvh
  have hstamp : GridCO.stampBlock (storeAt p c E rho ix y).base K' <
      SA.earlyTime p.toParams u := by
    refine lt_of_lt_of_le hKst' ?_
    have hsu' : ((r * p.R : Nat) : Int) ≤ (u : Int) := by exact_mod_cast hsu
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 2 * p.Δ ≤ 4 * p.Δ * (u : Int) + 2 * p.Δ
    nlinarith
  have hF' : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho k x)
      t).st).fg.F) K' := by
    change Block.Preceq (eraseFG (FGSA.clock p (storeAt p c E rho k x) _).fg.F) K'
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hF) hKK'
  obtain ⟨Y, hYK, hY⟩ := leaseMove_block_receipt p c E rho hE hN hDelta u hafter hSync ha.1 hx hk
    K' hKm' hstamp hF'
  have hinv := (storeBundle_stateBeforeTime E rho (SA.freezeTime p.toParams u) x).cstore
  obtain ⟨A, hA, hAe⟩ := eraseFG_ancestor_mem hinv.fg.closed hY (hYK ▸ hKK')
  change K ∈ (V2.D.Run.stateBefore E rho _ x).st.fg.TF
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
  exact (eraseFG_injective hAe) ▸ hA


omit [DecidableEq V] in
/-- Blueprint 21 H.15:2916–2923; plan J4A2-2 G1 cut guard;
B1/B17/B18. DC: SAME inclusive HEAD cut before a reader after freeze.
The event at iy is later than the label-l HEAD time. Thus the complete
HEAD batch is before iy, including equal-time HEAD events. -/
theorem postReset_moving_head_cut (hs : V2.D.ScheduleWellFormed E rho)
    {iy : Nat} {y : V} {l : Slot} {t : Time}
    (hiy : rho.events[iy]? = some (.tick y t))
    (hafter : SA.freezeTime p.toParams l < t) :
    timeIdx rho (SA.voteTime p.toParams l) ≤ iy := by
  by_contra hn
  have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hiy).mp (Nat.lt_of_not_ge hn)
  have hvl : SA.voteTime p.toParams l ≤ SA.freezeTime p.toParams l := by
    change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  exact (not_lt_of_ge (ht.trans hvl)) hafter

variable [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec mono emittedNonempty emittedName writes xing origin h0r

omit mono emittedNonempty emittedName writes xing origin h0r in
private theorem leaseMove_source_label {iy : Nat} {y : V} {l : Slot} {t : Time}
    (hiy : rho.events[iy]? = some (.tick y t))
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    {K : FGBlock (Fin p.n)} {r : Slot} (hK : SourceBefore p c E rho iy K r) :
    r + 1 ≤ l := by
  have ht := (healing_source_gate p c E rho
    hrec.base.valid.toScheduleWellFormed hK hiy).trans hupper
  change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((l + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hrs : (r : Int) < l := by
    by_contra hn
    have hlr : (l : Int) ≤ r := le_of_not_gt hn
    nlinarith [p.deltaPos]
  exact_mod_cast hrs

/-- Blueprint 21 H.15:2916–2923, H.2:709–746; plan J4A2-2 G2;
B1/B13/B17/B18. DC: INTENTIONAL domain at a moving reader after freeze.
The label-l batch covers the target. The view contains the frozen store
and is a subset of the reader's tree. Root and finality coverage are the
other descent arms. Only the prior high field at i is read, with iy ≤ i.
No emitted-source witness for B, THigh input, or H4 input is used. -/
theorem postReset_moving_domain
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {l : Slot} {B : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams l)
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hbatch : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z l = some H →
      Block.Preceq (eraseFG B) H)
    {iy : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y t)) (hyi : iy ≤ i)
    (hafter : SA.freezeTime p.toParams l < t)
    (hupper : t ≤ SA.voteTime p.toParams (l + 1))
    {X : Finset (FGBlock (Fin p.n))}
    (hX : X ⊆ (storeAt p c E rho iy y).fg.TF)
    (hfrozen : (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams l)) y).fg.TF ⊆ X)
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y X := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hvl : SA.voteTime p.toParams l ≤ SA.freezeTime p.toParams l := by
    change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (l : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  obtain ⟨jy, hjy⟩ := healing_support_vote_tick E rho hs hrec.base.delta hy l
    (hvl.trans (hafter.le.trans hhor))
  have hhead : headAtLabel p c E rho y l = some (headAtIdx p c E rho jy l) := by
    delta headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hjy]
    rw [healing_headAtIdx_tick p c E rho hjy]
    rfl
  have hBH := hbatch y hy _ hhead
  have hHstore : headAtIdx p c E rho jy l ∈ (storeAt p c E rho jy y).base.blocks := by
    rw [healing_headAtIdx_tick p c E rho hjy]
    have hm := headVote_stored p _ (cstoreInv_clock p (storeAt p c E rho jy y)
      (cstoreInv_stateBefore E rho jy y) (SA.voteTime p.toParams l)) l
    rwa [clock_base_blocks] at hm
  obtain ⟨W, hW, heW⟩ := (cstoreInv_stateBefore E rho jy y).baseTree _ |>.mp hHstore
  have hBstore : B ∈ (storeAt p c E rho jy y).fg.TF := by
    obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho jy y).fg.closed
      hW (heW ▸ hBH)
    exact (eraseFG_injective heA) ▸ hA
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := leaseMove_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have noLoss := (healing_high_source_compat p c E rho hrec mono emittedNonempty
    emittedName writes xing origin).1
  have hBK : ∀ K r, SourceBefore p c E rho iy K r → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K) := by
    intro K r hK hhK
    have hrs := leaseMove_source_label p c E rho hrec hiy hupper hK
    have hKn : HighSrcN p c E rho K r := by
      rw [HighSrcN_def]
      rw [high_def] at hhK
      exact ⟨healing_srcN_of_source p c E rho hK,
        (Nat.succ_le_succ h0r.mu_le).trans hhK⟩
    have hKH : Block.Preceq (eraseFG K) (headAtIdx p c E rho jy l) := by
      by_contra hn
      apply noLoss jy K r
      rw [Lost_def]
      exact ⟨hKn, y, l, hy, hrs, hjy, hn⟩
    exact Gen.Pure.block_compatible_of_common hBH hKH
  have hFB : FGBlock.Preceq (storeAt p c E rho iy y).fg.F B := by
    by_cases hFg : (storeAt p c E rho iy y).fg.F = .genesis
    · rw [hFg]; exact KitFG.genesis_preceq B
    obtain ⟨D, hD, hDF, K, r, hK, hhK, hKF, -⟩ :=
      healing_finality_source p c E rho hs origin hy hFg
    by_cases hl : (finalityView p D).h_F < (heightView p B).h
    · exact xing iy (iy + jy) y y D B hy (Nat.le_add_right iy jy) hD hDF
        ⟨hy, (fgsa_store_cumulative p c E rho hN (Nat.le_add_left jy iy) y).1 hBstore⟩ hl
    · have hhighK : high p w K := by
        rw [high_def, hhK]
        rw [high_def] at hhB
        exact hhB.trans (Nat.le_of_not_lt hl)
      have hcompat := hBK K r hK hhighK
      change (Block.preceq (eraseFG B) (eraseFG K) ||
        Block.preceq (eraseFG K) (eraseFG B)) = true at hcompat
      have hFK : FGBlock.Preceq (storeAt p c E rho iy y).fg.F K := by
        have hp := (fgCertificateLaws p).height.entry_preceq K
        rwa [hKF] at hp
      rcases Bool.or_eq_true_iff.mp hcompat with h | h
      · exact (KitFG.preceq_total_of_common hFK (leaseMove_lift p h)).resolve_right hnF
      · exact KitFG.preceq_trans hFK (leaseMove_lift p h)
  have hvu : SA.voteTime p.toParams l + E.Δ ≤ t := by
    rw [hrec.base.delta]
    refine le_trans ?_ hafter.le
    change 4 * p.Δ * (l : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (l : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvu hhor
  have hHstamp : GridCO.stampBlock (storeAt p c E rho jy y).base
      (headAtIdx p c E rho jy l) < SA.earlyTime p.toParams l := by
    have hnow := V2.D.Engine.stateBefore_now_le_event_noRestart (fgsaClock p c) E rho hs hN hjy y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho jy y)] at hnow
    refine lt_of_le_of_lt ((healing_block_stamp_le_now p c E rho hs hN hHstore).trans hnow) ?_
    change 4 * p.Δ * (l : Int) + p.Δ < 4 * p.Δ * (l : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have hFH : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      t).st).fg.F) (headAtIdx p c E rho jy l) := by
    change Block.Preceq (eraseFG (FGSA.clock p (storeAt p c E rho iy y) t).fg.F) _
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hFB) hBH
  obtain ⟨Y, heY, hY⟩ := leaseMove_block_receipt p c E rho hrec.base.valid hN
    hrec.base.delta l hafter hSync hy hy hiy _ hHstore hHstamp hFH
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hY
  have hBX : B ∈ X := by
    obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem (cstoreInv_stateBefore E rho _ y).fg.closed
      hY (heY ▸ hBH)
    exact hfrozen ((eraseFG_injective heA) ▸ hA)
  have hcover : ∀ K r, SourceBefore p c E rho iy K r →
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F K → FGBlock.Preceq B K →
      (heightView p B).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho iy y).fg.F := by
    intro K r hK hFK _hBK _hhK
    exact Or.inl (hfrozen (leaseMove_source_receipt p c E rho hrec emittedNonempty
      emittedName hK (Nat.le_of_succ_le (leaseMove_source_label p c E rho hrec hiy hupper hK))
      hgst hafter hy hiy hFK))
  have hhigh := hinv.high_compatible
  rw [PostResetHighCompatible_def] at hhigh
  have hsrc : ∀ K r, SourceBefore p c E rho iy K r → SourceBefore p c E rho i K r := by
    intro K r hK
    obtain ⟨a, z, q, row, haj, hrow, hsrc, he⟩ := hK
    exact ⟨a, z, q, row, haj.trans_le hyi, hrow, hsrc, he⟩
  rcases healing_descent p c E rho xing origin hy hX hBX hcover with
    hk | ⟨K, r, hK, hn, hhK⟩ | ⟨K, K', r, r', hK, hK', heh, hlt, hr⟩
  · exact (hk.resolve_left hnZ).resolve_right hnF
  · exact False.elim (hn (hBK K r hK (by
      rw [high_def] at hhB ⊢
      exact hhB.trans hhK)))
  · have hhK : high p w K := by
      rw [high_def] at hhB ⊢
      exact hhB.trans (Nat.le_of_lt hlt)
    have hhK' : high p w K' := by rw [high_def] at hhK ⊢; rwa [← heh]
    exact False.elim (healing_entry_pair_incompatible p heh hr
      (hhigh K K' r r' (hsrc K r hK) (hsrc K' r' hK') hhK hhK'))

end AvailableChain.FGSA.Run
end
