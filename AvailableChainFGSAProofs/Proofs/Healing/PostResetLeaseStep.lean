module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease -- shake: keep (J4-A required input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep -- shake: keep (J4-A required input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J4-A required input)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTransfer

public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossCause
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossNext
public import AvailableChainFGSAProofs.Proofs.Healing.SupportGate

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


section WrittenDomain
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
    (gateResultSupporter : ∀ {G ΔF : Time}, Recovery₂ p c E rho G ΔF →
      ∀ {s : Slot}, E.t_GST ≤ SA.voteTime p.toParams s →
      ∀ {ix : Nat} {x : V} {C : Block}, x ∈ rho.honest →
      IsGateTick p c rho ix x s → gateResultAt p c E rho ix = some (some C) →
      ∃ k z, z ∈ rho.honest ∧
        rho.events[k]? = some (.tick z (SA.voteTime p.toParams s)) ∧
        Block.Preceq C (headAtIdx p c E rho k s) ∧ k < ix)

include hrec mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter

omit mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter in
private theorem written_source_label {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    {K : FGBlock (Fin p.n)} {r : Slot} (hK : SourceBefore p c E rho iy K r) :
    r + 1 ≤ s := by
  have ht := healing_source_gate p c E rho hrec.base.valid.toScheduleWellFormed hK hiy
  change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
  push_cast at ht
  have hrs : (r : Int) < s := by
    by_contra hn
    have hsr : (s : Int) ≤ r := le_of_not_gt hn
    nlinarith [p.deltaPos]
  exact_mod_cast hrs

/-- Blueprint 21 H.15:2908–2914; plan J4-A2 route steps 1–7;
B1/B13/B17/B18. DC: SAME common honest HEAD from emitted-source no-loss.
The written prefix needs no emitted row. The shared supporter producer is
J5-A healing_gate_result_supporter, with its exact statement. Synchrony
comes from postReset_written_sync. The inherited engine has m = p.k. -/
theorem postReset_written_source_compatible
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hmem : eraseFG B ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks)
    (hBC : Block.Preceq (eraseFG B) C)
    {iy : Nat} {y : V}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    ∀ K r, SourceBefore p c E rho iy K r → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K) := by
  have noLoss := (healing_high_source_compat p c E rho hrec mono emittedNonempty
    emittedName writes xing origin).1
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  obtain ⟨jh, z, hz, hjh, hCH, -⟩ := gateResultSupporter hrec hgst.le hx hix hres
  intro K r hK hhK
  have hrs := written_source_label p c E rho hrec hiy hK
  have hKn : HighSrcN p c E rho K r := by
    rw [HighSrcN_def]
    rw [high_def] at hhK
    exact ⟨healing_srcN_of_source p c E rho hK,
      (Nat.succ_le_succ h0r.mu_le).trans hhK⟩
  have hKH : Block.Preceq (eraseFG K) (headAtIdx p c E rho jh s) := by
    by_contra hn
    apply noLoss jh K r
    rw [Lost_def]
    exact ⟨hKn, z, s, hz, hrs, hjh, hn⟩
  exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_trans hBC hCH) hKH

omit hrec mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter in
omit [Fintype V] in
private theorem written_stored {ix : Nat} {x : V} {s : Slot} {B : FGBlock (Fin p.n)}
    (hmem : eraseFG B ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks) : B ∈ (storeAt p c E rho ix x).fg.TF := by
  have hb := (actView_blocks _ _).mp hmem |>.1
  rw [(clockPre_fields p _ _).2.1] at hb
  obtain ⟨A, hA, he⟩ := (cstoreInv_stateBefore E rho ix x).baseTree (eraseFG B) |>.mp hb
  exact (eraseFG_injective he) ▸ hA

omit hrec mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter in
omit [Fintype V] in
private theorem written_source_mono {j i : Nat} {K : FGBlock (Fin p.n)} {r : Slot}
    (h : SourceBefore p c E rho j K r) (hji : j ≤ i) : SourceBefore p c E rho i K r := by
  obtain ⟨a, z, q, row, haj, hrow, hsrc, he⟩ := h
  exact ⟨a, z, q, row, haj.trans_le hji, hrow, hsrc, he⟩

/-- Blueprint 21 H.15:2904–2914; plan J4-A2, frozen domain;
B1/B13/B17/B18. DC: INTENTIONAL moving-frame descent at the first HEAD.
The root and finality coverage cases are excluded by the branch guards.
The proof supplies receipt and restricted view coverage, then excludes
both descent causes. It applies before and after q_(s*), without a phase
or a reset-copy availability premise. Only high_compatible at i is read.
The inherited engine has m = p.k; the label-s supporter is synchronous. -/
theorem postReset_written_domain
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hmem : eraseFG B ∈ (actView (clockPre p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s))).blocks)
    (hBC : Block.Preceq (eraseFG B) C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hyi : iy ≤ i)
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hBK := postReset_written_source_compatible p c E rho hrec mono emittedNonempty
    emittedName writes xing origin h0r gateResultSupporter hx hix hres hCB hmem hBC hiy
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := written_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have hBstore := written_stored p c E rho hmem
  have hFB : FGBlock.Preceq (storeAt p c E rho iy y).fg.F B := by
    by_cases hFg : (storeAt p c E rho iy y).fg.F = .genesis
    · rw [hFg]; exact KitFG.genesis_preceq B
    obtain ⟨D, hD, hDF, K, r, hK, hhK, hKF, -⟩ :=
      healing_finality_source p c E rho hs origin hy hFg
    by_cases hl : (finalityView p D).h_F < (heightView p B).h
    · exact xing iy (iy + ix) y x D B hy (Nat.le_add_right iy ix) hD hDF
        ⟨hx, (fgsa_store_cumulative p c E rho hN (Nat.le_add_left ix iy) x).1 hBstore⟩ hl
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
      · exact (KitFG.preceq_total_of_common hFK (written_lift p h)).resolve_right hnF
      · exact KitFG.preceq_trans hFK (written_lift p h)
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have hres' := (gateResultAt_eq_gateResult p c E rho hs hix).symm.trans hres
  have hmaj := healing_slow_majority E rho hs hix hres' hBC
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hix)).2
  obtain ⟨-, o, -, ho, -, hsup⟩ := healing_slow_honest_seat E rho hrec hgst.le hhor hx hix hmaj
  obtain ⟨K, hKt, hKm, hstamp, -, -, -⟩ := healing_support_clean_target E rho o ho
  have hBKt : Block.Preceq (eraseFG B) K := by
    rw [Gen.AC.voteSupports_def, hKt] at hsup
    exact (Bool.and_eq_true_iff.mp hsup).2
  have hvh := (hs.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hvu : SA.voteTime p.toParams s + E.Δ ≤ SA.voteTime p.toParams (s + 1) := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst.le hvu hvh
  have hFK : Block.Preceq (eraseFG (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).fg.F) K := by
    rw [clock_fg]
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hFB) hBKt
  obtain ⟨Y, heY, hY⟩ := healing_block_receipt_sync p c E rho hrec.base.valid hN
    hrec.base.delta s hSync hx hy hiy K hKm hstamp hFK
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hY
  let X := (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF
  have hBX : B ∈ X := by
    obtain ⟨A, hA, heA⟩ := (cstoreInv_stateBefore E rho _ y).fg.closed |>
      fun hc => eraseFG_ancestor_mem hc hY (heY ▸ hBKt)
    exact (eraseFG_injective heA) ▸ hA
  have hcut : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ iy :=
    healing_support_idxBefore_le p c E rho hs hiy (by
      change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos])
  have hX : X ⊆ (storeAt p c E rho iy y).fg.TF :=
    (fgsa_store_cumulative p c E rho hN hcut y).1
  have hcover : ∀ K r, SourceBefore p c E rho iy K r →
      FGBlock.Preceq (storeAt p c E rho iy y).fg.F K → FGBlock.Preceq B K →
      (heightView p B).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho iy y).fg.F := by
    intro K r hK hFK _hBK _hhK
    exact Or.inl (healing_source_receipt p c E rho hrec emittedNonempty emittedName hK
      (Nat.le_of_succ_le (written_source_label p c E rho hrec hiy hK)) hgst.le hy hiy hFK)
  have hhigh := hinv.high_compatible
  rw [PostResetHighCompatible_def] at hhigh
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
      (hhigh K K' r r' (written_source_mono p c E rho hK hyi)
        (written_source_mono p c E rho hK' hyi) hhK hhK'))


variable (slowWindowSync : ∀ {G ΔF : Time}, Recovery₂ p c E rho G ΔF →
  ∀ {w : HealingWitness}, H0Reset p c E rho w →
  ∀ {i : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)},
  x ∈ rho.honest →
  GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some C) →
  Block.Preceq w.CStar (eraseFG B) → Block.Preceq (eraseFG B) C →
  E.t_GST < SA.voteTime p.toParams s)

include slowWindowSync

omit mono emittedNonempty emittedName writes xing origin gateResultSupporter in
private theorem written_slow_boundary
    {ix : Nat} {x : V} {s : Slot} {B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hCB : Block.Preceq w.CStar (eraseFG B))
    (hel : GridCO.slowEligible p.toParams.engine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
      (eraseFG B) = true) : E.t_GST < SA.voteTime p.toParams (s + 1 - p.k) := by
  unfold GridCO.slowEligible at hel
  obtain ⟨hkw, hall⟩ := Bool.and_eq_true_iff.mp hel
  have hm : p.toParams.engine.m = p.k := rfl
  rw [hm] at hkw hall
  have hk : p.k ≤ s + 1 := of_decide_eq_true hkw
  have key0 : ∀ a k : Nat, 2 ≤ k → k ≤ a + 1 → a + 1 - k + 1 ≤ a := by
    intro a k h1 h2
    omega
  have hw := key0 s p.k p.kLarge hk
  have key1 : ∀ a b k : Nat, a + 1 - k ≤ b → b + 1 ≤ a → a - b - 1 < k - 1 := by
    intro a b k h1 h2
    omega
  have hj := key1 s (s + 1 - p.k) p.k le_rfl hw
  have h := List.all_eq_true.mp hall _ (List.mem_range.mpr hj)
  have key2 : ∀ a b : Nat, b + 1 ≤ a → a - (a - b - 1 + 1) = b := by
    intro a b h
    omega
  have he := key2 s (s + 1 - p.k) hw
  rw [he] at h
  have hsave : GridCO.savedGenuine
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)))
      (s + 1 - p.k) = GridCO.savedGenuine (storeAt p c E rho ix x).base (s + 1 - p.k) :=
    savedGenuine_congr (clockPre_genuine p _ _) _
  rw [hsave] at h
  cases hsg : GridCO.savedGenuine (storeAt p c E rho ix x).base (s + 1 - p.k) with
  | none => rw [hsg] at h; cases h
  | some r =>
    cases r with
    | none => rw [hsg] at h; cases h
    | some C =>
      rw [hsg] at h
      exact slowWindowSync hrec h0r hx hsg hCB h

omit mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter slowWindowSync in
private theorem written_frozen_geometry
    {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    let X := (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF
    X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1) ∧
    ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X := by
  intro X
  have hs := hrec.base.valid.toScheduleWellFormed
  have hread : postClock E rho y (SA.voteTime p.toParams (s + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
        (SA.voteTime p.toParams (s + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hiy]
    rfl
  have hdpos : 0 < SA.freezeTime p.toParams s := by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity
  have hdvote : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  refine ⟨fun W hW => healing_frozen_path p c E rho hs hrec.base.noRestart hdpos hdvote
    (by rw [Nat.add_sub_cancel]) hW hread W (KitFG.preceq_refl W), ?_⟩
  intro W hW A hAW
  obtain ⟨A', hA', heA'⟩ := eraseFG_ancestor_mem
    (cstoreInv_stateBefore E rho _ y).fg.closed hW (eraseFG_preceq hAW)
  exact (eraseFG_injective heA') ▸ hA'

/-- Blueprint 21 H.15:2902–2914, H.1:663–708; plan J4-A3;
B1/B13/B17/B18. DC: SAME first common HEAD for an actual written prefix.
A2 supplies the frozen domain; root and finality coverage are direct.
The actual key supplies the fast or slow arm. J5-A's exact named
postReset_slow_window_sync supplies synchrony at the first saved label.
The first HEAD precedes its write by time, hence by event index. -/
theorem postReset_written_first_head
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (s + 1)) := by
  by_cases hZ : FGBlock.Preceq B (R_at p c E rho iy y).Z
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inl hZ)
  by_cases hF : FGBlock.Preceq B (storeAt p c E rho iy y).fg.F
  · exact healing_head_covers_root p c E rho hiy (l := s + 1) (Nat.succ_ne_zero s) (Or.inr hF)
  have hyx : iy < ix := healing_idx_lt_of_time_lt p c E rho
    hrec.base.valid.toScheduleWellFormed hiy hix (by
      change SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      linarith [p.deltaPos])
  obtain ⟨hmem, -, hBC, -, hcase⟩ := healing_support_key_cases p hkey
  have hD := postReset_written_domain p c E rho hrec mono emittedNonempty emittedName
    writes xing origin h0r gateResultSupporter hinv hx hix hres hCB hmem hBC hy hiy
    (hyx.le.trans hxi) hZ hF
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have harm : SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
      (eraseFG B) ∨
    (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
      GridCO.slowEligible p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) = true) := hcase.imp_right (fun hel =>
    ⟨(written_slow_boundary p c E rho hrec h0r slowWindowSync hx hCB hel).le, hel⟩)
  obtain ⟨hXv, hXc⟩ := written_frozen_geometry p c E rho hrec hiy
  exact healing_first_transfer_written p c E rho hrec mono writes hx hix hres hBC
    hgst.le harm hy hiy hXv hXc hD

/-- Blueprint 21 H.15 S1:2902–2914; plan J4-A3; B1/B13/B17/B18.
DC: SAME complete first-HEAD clause, expressed through headAtLabel.
No bounded induction range or first-proposal input is used. -/
theorem postReset_written_first_head_label
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s) (hxi : ix ≤ i)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    {y : V} {H : Block} (hy : y ∈ rho.honest)
    (hhead : headAtLabel p c E rho y (s + 1) = some H) : Block.Preceq (eraseFG B) H := by
  delta headAtLabel at hhead
  rw [postClock_def, preTick_def] at hhead
  cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [ht] at hhead; cases hhead
  | some iy =>
    rw [ht] at hhead
    have hiy := V2.D.Run.tickIdx?_spec ht
    have hH : H = headAtIdx p c E rho iy (s + 1) := by
      rw [healing_headAtIdx_tick p c E rho hiy]
      exact (Option.some.inj hhead).symm
    rw [hH]
    exact postReset_written_first_head p c E rho hrec mono emittedNonempty emittedName
      writes xing origin h0r gateResultSupporter slowWindowSync hinv hx hix hxi hres hCB hkey hy hiy


/-- Blueprint 21 H.15 S1:2887–2914; plan J4-A5, new-write HEAD clause;
B1/B13/B17/B18. DC: SAME event-index cut. For every i : Nat, the only
label at or above s + 1 whose actual HEAD cut can be complete at i + 1
is s + 1. Later actual ticks contradict the cut. No induction or bound
by the run length is needed. This is the new-write case, not a successor
producer for old writes. -/
theorem postReset_written_heads_at_write_cut
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
    (hres : gateResultAt p c E rho i = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B))
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s C) :
    ∀ y j H, y ∈ rho.honest → s + 1 ≤ j →
      timeIdx rho (SA.voteTime p.toParams j) ≤ i + 1 →
      headAtLabel p c E rho y j = some H → Block.Preceq (eraseFG B) H := by
  intro y j H hy hsj hcut hhead
  rcases Nat.eq_or_lt_of_le hsj with rfl | hj
  · exact postReset_written_first_head_label p c E rho hrec mono emittedNonempty emittedName
      writes xing origin h0r gateResultSupporter slowWindowSync hinv hx hi le_rfl
      hres hCB hkey hy hhead
  · delta headAtLabel at hhead
    rw [postClock_def, preTick_def] at hhead
    cases ht : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams j) with
    | none => rw [ht] at hhead; cases hhead
    | some iy =>
      have hiy := V2.D.Run.tickIdx?_spec ht
      have hiycut : iy < timeIdx rho (SA.voteTime p.toParams j) :=
        (V2.D.Engine.index_lt_read_length_iff hrec.base.valid.toScheduleWellFormed _ hiy).mpr le_rfl
      have hil : i < iy := healing_idx_lt_of_time_lt p c E rho
        hrec.base.valid.toScheduleWellFormed hi hiy (by
          change SA.gateTime p.toParams s < SA.voteTime p.toParams j
          have hjs : (s : Int) + 2 ≤ j := by exact_mod_cast (show s + 2 ≤ j from hj)
          change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (j : Int) + p.Δ
          nlinarith [p.deltaPos])
      omega


omit mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter slowWindowSync in
private theorem written_head_label {a : Nat} {z : V} {j : Slot}
    (ha : rho.events[a]? = some (.tick z (SA.voteTime p.toParams j))) :
    headAtLabel p c E rho z j = some (headAtIdx p c E rho a j) := by
  delta headAtLabel
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event p c E rho hrec.base.valid.toScheduleWellFormed ha]
  rw [healing_headAtIdx_tick p c E rho ha]
  rfl

omit slowWindowSync in
/-- Blueprint 21 H.15:2916–2923, H.2:720–733; plan J4-A4, later result boundary;
B1/B13/B17/B18. DC: SAME finality coverage or a covering-batch confirmation.
The old write's S1 field at i covers the complete label-j batch before
this gate. Earlier sources use no-loss; a same-label emitted source uses
its genuine result's own honest supporter. No field at i + 1 is read. -/
theorem postReset_written_later_result
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {k : Nat} (hki : k < i) {x : V} {s : Slot} {C : Block}
    {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hk : IsGateTick p c rho k x s)
    (hpass : gatePassedAt p c E rho k)
    (hres : gateResultAt p c E rho k = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s C)
    {y : V} {j : Slot} {D : Block} (hy : y ∈ rho.honest) (hsj : s + 1 ≤ j)
    (hi : IsGateTick p c rho i y j)
    (hresult : gateResultAt p c E rho i = some (some D)) :
    Block.Preceq (eraseFG B) D ∨ Block.Preceq (eraseFG B) (F_at p c E rho i y) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hmem, hgen, hBC, -, -⟩ := healing_support_key_cases p hkey
  have hadm : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s (eraseFG B) := by
    have hkey' := hkey
    rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hkey'
    obtain ⟨b, -, hbg⟩ := List.mem_flatMap.mp hkey'
    obtain ⟨g', hga, he⟩ := List.mem_map.mp hbg
    obtain ⟨heb, heg⟩ := Prod.mk.inj he
    simpa only [heb, heg] using hga
  have hsafe := hinv.lease_safe
  rw [PostResetLeaseSafe_def] at hsafe
  have hheads := (hsafe k hki x s (eraseFG B) g C hx hk hpass hres hCB hne
    hmem hgen hBC hadm).2.1
  have hcut : timeIdx rho (SA.voteTime p.toParams j) ≤ i := by
    by_contra hn
    have ht := (V2.D.Engine.index_lt_read_length_iff hs _ hi).mp (Nat.lt_of_not_ge hn)
    change SA.gateTime p.toParams j ≤ SA.voteTime p.toParams j at ht
    change 4 * p.Δ * (j : Int) + 6 * p.Δ ≤ 4 * p.Δ * (j : Int) + p.Δ at ht
    linarith [p.deltaPos]
  have hcov : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z j = some H →
      Block.Preceq (eraseFG B) H := fun z hz H hh => hheads z j H hz hsj hcut hh
  have hgsts := postReset_written_sync p c E rho hrec h0r hx hk hCB hmem
  have hgst : E.t_GST ≤ SA.voteTime p.toParams j := by
    refine hgsts.le.trans ?_
    have hsj' : (s : Int) ≤ j := by exact_mod_cast (Nat.le_of_succ_le hsj)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (j : Int) + p.Δ
    nlinarith [p.deltaPos]
  have noLoss := (healing_high_source_compat p c E rho hrec mono emittedNonempty
    emittedName writes xing origin).1
  obtain ⟨a, z, hz, ha, -, -⟩ := gateResultSupporter hrec hgst hy hi hresult
  have hBH := hcov z hz _ (written_head_label p c E rho hrec ha)
  have hBK : ∀ K r, SourceBefore p c E rho i K r → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K) := by
    intro K r hK hhK
    have hrj := (healing_source_read p c E rho hs hK hi).2.2 rfl
    rcases Nat.eq_or_lt_of_le hrj with he | hr
    · obtain ⟨b, zK, q, row, -, hrow, hsrc, hlabel⟩ := hK
      have hq : q * p.R = j := hlabel.symm.trans he
      obtain ⟨-, CK, -, hG, hKCK, st, hst, -⟩ :=
        healing_source_decode p c E rho emittedNonempty emittedName hrow hsrc
      rw [hq] at hG hst
      rw [gateIn_def, preTick_def] at hst
      cases hidx : V2.D.Run.tickIdx? rho zK (SA.gateTime p.toParams j) with
      | none => rw [hidx] at hst; cases hst
      | some ik =>
        have hik := V2.D.Run.tickIdx?_spec hidx
        have hraw := (gateResultAt_eq_gateResult p c E rho hs hik).trans hG
        obtain ⟨aK, zH, hzH, haK, hCKH, -⟩ := gateResultSupporter hrec hgst hrow.1 hik hraw
        exact Gen.Pure.block_compatible_of_common
          (hcov zH hzH _ (written_head_label p c E rho hrec haK))
          (Gen.Pure.block_preceq_trans hKCK hCKH)
    · have hKn : HighSrcN p c E rho K r := by
        rw [HighSrcN_def]
        rw [high_def] at hhK
        exact ⟨healing_srcN_of_source p c E rho hK,
          (Nat.succ_le_succ h0r.mu_le).trans hhK⟩
      have hKH : Block.Preceq (eraseFG K) (headAtIdx p c E rho a j) := by
        by_contra hn
        apply noLoss a K r
        rw [Lost_def]
        exact ⟨hKn, z, j, hz, hr, ha, hn⟩
      exact Gen.Pure.block_compatible_of_common hBH hKH
  by_cases hBF : FGBlock.Preceq B (storeAt p c E rho i y).fg.F
  · right
    exact eraseFG_preceq hBF
  have hBstore := written_stored p c E rho hmem
  obtain ⟨-, -, -, Cfg, -, -, -, heC, hhC⟩ := h0r.fresh
  have hCBfg : FGBlock.Preceq Cfg B := written_lift p (by rwa [heC])
  have hhB : high p w B := by
    rw [high_def]
    exact hhC ▸ (fgCertificateLaws p).height.h_mono hCBfg
  have hFB : FGBlock.Preceq (storeAt p c E rho i y).fg.F B := by
    by_cases hFg : (storeAt p c E rho i y).fg.F = .genesis
    · rw [hFg]; exact KitFG.genesis_preceq B
    obtain ⟨DF, hDF, heF, K, r, hK, hhK, hKF, -⟩ :=
      healing_finality_source p c E rho hs origin hy hFg
    by_cases hl : (finalityView p DF).h_F < (heightView p B).h
    · exact xing i (i + k) y x DF B hy (Nat.le_add_right i k) hDF heF
        ⟨hx, (fgsa_store_cumulative p c E rho hrec.base.noRestart
          (Nat.le_add_left k i) x).1 hBstore⟩ hl
    · have hhighK : high p w K := by
        rw [high_def, hhK]
        rw [high_def] at hhB
        exact hhB.trans (Nat.le_of_not_lt hl)
      have hcompat := hBK K r hK hhighK
      change (Block.preceq (eraseFG B) (eraseFG K) ||
        Block.preceq (eraseFG K) (eraseFG B)) = true at hcompat
      have hFK : FGBlock.Preceq (storeAt p c E rho i y).fg.F K := by
        have hp := (fgCertificateLaws p).height.entry_preceq K
        rwa [hKF] at hp
      rcases Bool.or_eq_true_iff.mp hcompat with h | h
      · exact (KitFG.preceq_total_of_common hFK (written_lift p h)).resolve_right hBF
      · exact KitFG.preceq_trans hFK (written_lift p h)
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hi)).2
  obtain ⟨D', hconf, hBD⟩ := healing_support_gate_cover E rho hrec hgst hhor hcov hi (by
    rw [clockPre_fg]
    exact eraseFG_preceq hFB)
  have hst : gateIn p c E rho y j =
      some (clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams j)) := by
    rw [gateIn_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hi]
    rfl
  have hG := (gateResultAt_eq_gateResult p c E rho hs hi).symm.trans hresult
  rw [gateResult_def] at hG
  rw [hst] at hG
  simp only [Option.map_some, Option.some.injEq] at hG
  have heD : D' = D := Option.some.inj (hconf.symm.trans hG)
  exact Or.inl (heD ▸ hBD)


omit hrec mono emittedNonempty emittedName writes xing origin h0r
  gateResultSupporter slowWindowSync in
omit [Fintype V] in
private theorem written_key_of_guards {k : Nat} {x : V} {s : Slot} {B C : Block} {g : Nat}
    (hmem : B ∈ (actView (clockPre p (storeAt p c E rho k x)
      (SA.gateTime p.toParams s))).blocks) (hgen : B ≠ .genesis) (hBC : Block.Preceq B C)
    (hg : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s B) :
    (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s C := by
  rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy]
  apply List.mem_flatMap.mpr
  refine ⟨B, List.mem_filter.mpr ⟨hmem, ?_⟩, List.mem_map.mpr ⟨g, hg, rfl⟩⟩
  simp only [Bool.and_eq_true, bne_iff_ne]
  exact ⟨hgen, hBC⟩

omit slowWindowSync in
/-- Blueprint 21 H.15:2887–2892, 2916–2923; plan J4-A4, result clause at i + 1;
B1/B13/B17/B18. DC: SAME event-prefix result extension for every i : Nat.
Old writes use the prior result clause or the new gate boundary lemma.
A new write cannot have a later-label gate before this cut. This is the
full later-result clause; HEAD, proposal and output successors are separate. -/
theorem postReset_leaseSafe_results_succ {i : Nat} (hinv : PostResetInv p c E rho w i) :
    ∀ k, k < i + 1 → ∀ x s B g C, x ∈ rho.honest → IsGateTick p c rho k x s →
    gatePassedAt p c E rho k → gateResultAt p c E rho k = some (some C) →
    Block.Preceq w.CStar B → B ≠ w.CStar →
    let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s)
    B ∈ (actView pre).blocks → B ≠ .genesis → Block.Preceq B C →
    g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n (actView pre) s B →
    ∀ l, l < i + 1 → ∀ y j D, y ∈ rho.honest → s + 1 ≤ j →
      IsGateTick p c rho l y j → gateResultAt p c E rho l = some (some D) →
      Block.Preceq B D ∨ Block.Preceq B (F_at p c E rho l y) := by
  intro k hk x s B g C hx ht hp hr hCB hne pre hmem hgen hBC hg l hl y j D hy hsj hgate hresult
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | rfl
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hl) with hli | rfl
    · have hsafe := hinv.lease_safe
      rw [PostResetLeaseSafe_def] at hsafe
      exact (hsafe k hki x s B g C hx ht hp hr hCB hne hmem hgen hBC hg).1
        l hli y j D hy hsj hgate hresult
    · have hkey := written_key_of_guards p c E rho hmem hgen hBC hg
      have hb := (actView_blocks _ _).mp hmem |>.1
      rw [(clockPre_fields p _ _).2.1] at hb
      obtain ⟨Bfg, -, he⟩ := (cstoreInv_stateBefore E rho k x).baseTree B |>.mp hb
      have hresult' := postReset_written_later_result p c E rho hrec mono emittedNonempty
        emittedName writes xing origin h0r gateResultSupporter hinv hki hx ht hp hr
        (B := Bfg) (by rwa [he]) (by rwa [he]) (by rwa [he]) hy hsj hgate hresult
      simpa only [he] using hresult'
  · have hkl : k < l := healing_idx_lt_of_time_lt p c E rho
      hrec.base.valid.toScheduleWellFormed ht hgate (by
        change SA.gateTime p.toParams s < SA.gateTime p.toParams j
        have hsj' : (s : Int) + 1 ≤ j := by exact_mod_cast hsj
        change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (j : Int) + 6 * p.Δ
        nlinarith [p.deltaPos])
    omega

end WrittenDomain

end AvailableChain.FGSA.Run
end
