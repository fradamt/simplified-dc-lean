module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease -- shake: keep (J4-A required input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep -- shake: keep (J4-A required input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J4-A required input)
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLoss
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTransfer

public section

/-! Blueprint 21 H.15:2885–2923, H.1:663–708; plan J4-A;
B1/B13/B17/B18. First transfer for an arbitrary written prefix.
DC: SAME majority transport; INTENTIONAL moving domain and slow window.
The gate result supplies the majority. No emitted source of B is needed. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem written_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  preceq_of_eraseFG_preceq (KitFG.viewRootInj_all {A, B})
    ⟨A, by simp, KitFG.preceq_refl A⟩ ⟨B, by simp, KitFG.preceq_refl B⟩ h

/-- Blueprint 21 H.15:2894–2900; plan J4-A A1 synchrony;
B1/B13/B17/B18. DC: SAME causal frontier cut. A stored prefix above C*
cannot be held at u₀. Its gate is after u₀, so its HEAD label is after GST.
This uses the actual stored prefix, without an emitted-source premise. -/
theorem postReset_written_sync [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) {i : Nat} {y : V} {s : Slot} {B : Block}
    (hy : y ∈ rho.honest) (ht : IsGateTick p c rho i y s)
    (hCB : Block.Preceq w.CStar B)
    (hB : B ∈ (actView (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams s))).blocks) :
    E.t_GST < SA.voteTime p.toParams s := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hb := (actView_blocks _ _).mp hB |>.1
  rw [(clockPre_fields p _ _).2.1] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := (cstoreInv_stateBefore E rho i y).baseTree B |>.mp hb
  obtain ⟨_, _, _, Cfg, _, _, _, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg Bfg := written_lift p (by rwa [heC, heB])
  have hhB : w.M + 1 ≤ (heightView p Bfg).h :=
    hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have hcut : w.u₀ < SA.gateTime p.toParams s := by
    by_contra hn
    have hi : i ≤ timeIdx rho w.u₀ :=
      ((V2.D.Engine.index_lt_read_length_iff hs w.u₀ ht).mpr (le_of_not_gt hn)).le
    have hBcut := (fgsa_store_cumulative p c E rho hrec.base.noRestart hi y).1 hBfg
    have hheight := healing_phase_height_le p c E rho hBcut
    have hfront : (storeAt p c E rho (timeIdx rho w.u₀) y).fg.h_max ≤ w.M := by
      rw [h0r.frontier]
      unfold honestFrontier
      rw [V2.D.Engine.readAt_eq_stateBefore hs w.u₀]
      exact Finset.le_sup (f := fun z => (storeAt p c E rho (timeIdx rho w.u₀) z).fg.h_max) hy
    exact (Nat.not_succ_le_self w.M) (hhB.trans (hheight.trans hfront))
  have hP : 8 * p.Δ ≤ P p := by
    have hR : (2 : Int) ≤ p.R := by exact_mod_cast p.RLarge
    change 8 * p.Δ ≤ 4 * (p.R : Int) * p.Δ
    nlinarith [p.deltaPos]
  have hlow := h0r.cut_lower
  change w.u₀ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hcut
  change E.t_GST < 4 * p.Δ * (s : Int) + p.Δ
  linarith [p.deltaPos]

/-- Blueprint 21 H.15:2902–2914, H.1:673–699; plan J4-A A1;
B1/B13/B17/B18. DC: SAME count and relay with a kept domain path.
The fast arm uses release. The slow arm uses the last-write window.
Assembly supplies fgsa_rMono and fgsa_leaseOrigins_lastWrite. The domain
and label synchrony are explicit read guards for the H.15 producer. -/
theorem healing_first_transfer_written [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
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
    {ix : Nat} {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    {B : FGBlock (Fin p.n)} (hBC : Block.Preceq (eraseFG B) C)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (harm : SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) ∨
      (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
        GridCO.slowEligible p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
          (eraseFG B) = true))
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (s + 1)) := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hhor : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hS.in_horizon _ (List.mem_of_getElem? hix)).2
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
  have hres' : gateResult p c E rho x s = some (some C) :=
    (gateResultAt_eq_gateResult p c E rho hS hix).symm.trans hres
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  have hmaj := healing_slow_majority E rho hS hix hres' hBC
  let dst := FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (s + 1))
  -- The domain witness of B at the receiver read.
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho iy y) _
  have hdfg : dst.fg = (storeAt p c E rho iy y).fg := clock_fg p _ _
  have hRd : FGSA.controls p dst = R_at p c E rho iy y := by
    change KitFG.storeControlsView (heightView p) dst.fg =
      KitFG.storeControlsView (heightView p) (storeAt p c E rho iy y).fg
    rw [hdfg]
  obtain ⟨hBX, hFB, hZB, W, hWX, hBW, hloW⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho iy y) X B).mp hD
  have hvW : W ∈ voterBlocks p dst (s + 1) := hXv hWX
  have hWdst : W ∈ dst.fg.TF := (Finset.mem_filter.mp hvW).1
  have hFB0 : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) (eraseFG B) :=
    eraseFG_preceq hFB
  have hFB' : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := hdfg ▸ hFB0
  -- The kept path: every block between the live root and B is in the frozen domain.
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C (eraseFG B) →
      C ∈ erasedList dst (storeFrame p.E p.cfg dst.fg (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAW⟩ := eraseFG_ancestor_preceq hinv.fg.closed hWdst
      (Gen.Pure.block_preceq_trans hCB (eraseFG_preceq hBW))
    have hFA : FGBlock.Preceq dst.fg.F A := written_lift p
      (Gen.Pure.block_preceq_trans (F_preceq_liveRoot p dst hinv) (heA ▸ hr'.2))
    have hZA : FGBlock.Preceq (FGSA.controls p dst).Z A := written_lift p
      (Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) (heA ▸ hr'.2))
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [← domainR_eq_storeFrame, domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p dst) _ A).mpr
      ⟨hXv (hXc W hWX A hAW), hFA, hZA, W, hvW, hAW, hRd ▸ hloW⟩
  -- Both admission arms remove conflicting leases at this HEAD read.
  have hrows : ∀ row ∈ dst.base.obligations, Block.Compatible row.1 (eraseFG B) := by
    rcases harm with hτ | ⟨hgw, hel⟩
    · exact healing_support_release_compat E rho hE hN hDelta s hSync hx hy hix hiy hτ hFB0
    · have hst : gateIn p c E rho x s =
          some (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)) := by
        rw [gateIn_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hix]
        rfl
      exact healing_slow_lease E rho hrec mono writes hgst hhor hx hgw hst hres' hBC hel
        le_rfl (hS.in_horizon _ (List.mem_of_getElem? hiy)).2
        (fun w hw1 hw2 => absurd (hw1.trans hw2) (Nat.not_succ_le_self s)) hy hiy hFB0
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
        exact hrows row hr
      · contradiction
  -- Majority and rival dominance at the receiver (forward and reverse relay).
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.voteSupports src.blocks (eraseFG B) o = true →
      (o ∈ FGSA.headSupport p dst (s + 1) ∧
        Gen.AC.voteSupports dst.base.blocks (eraseFG B) o = true) ∨
        GridCO.equivocates (FGSA.headVotes p dst (s + 1)) seat = true := by
    intro o' ho' seat hs' hsup'
    obtain ⟨K', hK', hKm', hKst', _, _, _⟩ := healing_support_clean_target E rho o' ho'
    have hBK' : Block.Preceq (eraseFG B) K' := by
      rw [Gen.AC.voteSupports_def, hK'] at hsup'
      exact (Bool.and_eq_true_iff.mp hsup').2
    obtain ⟨Kfg', hKe', hpath'⟩ := healing_support_target_path E rho hE hN hDelta s hSync
      hx hy hiy K' hKm' hKst' (Gen.Pure.block_preceq_trans hFB' hBK')
    exact fgsa_cleanSupport_forward_relay E rho hE hN hDelta s hSync hx hy hix hiy o' ho'
      seat hs' Kfg' (hKe' ▸ hK') (eraseFG B) (hKe' ▸ hBK') hpath' hFB'
  have htr := Gen.AC.transfer src.blocks dst.base.blocks
    (GridCO.cleanSupport p.toParams.engine src s) (GridCO.lateVotes p.toParams.engine src s)
    (FGSA.headVotes p dst (s + 1)) (FGSA.headSupport p dst (s + 1)) (eraseFG B)
    (fun _ ho' => fgsa_early_subset_late p src s (List.mem_filter.mp ho').1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay E rho hE hN hDelta s hSync hx hy hix hiy)
    (fgsa_headSupport_subset_headVotes E rho hE iy y s) hmaj
  rw [Gen.AC.TransferBounds_def] at htr
  rw [healing_headAtIdx_tick p c E rho hiy]
  exact fgsa_headVote_covers_of_transfer p dst s (eraseFG B) hanchor hpath
    htr.2.2.2.2.2.1 htr.2.2.2.2.2.2

end AvailableChain.FGSA.Run
end
