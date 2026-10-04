module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportTransfer
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate

public section

/-! HG.1 gate service (blueprint 21:1551–1574; plan §3.1 steps 6–7).
The cap replaces fixed-phase geometry after d_q. The release proof keeps each node's
own gate and vote indices. INLINE writes: `fgsa_leaseOrigins_lastWrite` at Assembly. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Blueprint 21:965–970, 1551–1574.
DC: INTENTIONAL exact HEAD receipts release conflicting leases before the gate.
This local lemma does not use a phase. Its receipt input is built by the capped proof. -/
theorem frontier_gate_guard_of_receipts [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho)
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
    {s : Slot} (hgsts : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgh : SA.gateTime p.toParams s ≤ rho.horizon) {Q : Block}
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some Q)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s Q)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q) :
    ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) Q := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgsts hvd hgh
  have hτ := repair_gate_fast_count E rho hrec hgsts hgh hhead ht hgeom
  have hqd : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hx (s + 1) (hqd.le.trans hgh)
  have hqi : iq < i := repair_idx_lt E rho hS hiq ht hqd
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  intro lease hl
  rw [← hv] at hl
  have hl' : lease ∈ (storeAt p c E rho i x).base.obligations :=
    (clockPre_obligations_sublist p _ _).subset hl
  obtain ⟨j, hji, w, C, htj, _, _, _, _, hdl, _, _⟩ := writes i x lease hl'
  have hws : w < s := by
    have hlt := fgsa_tick_time_strict E rho hS htj ht hji
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hlt
    have h : (w : Int) < s := by nlinarith
    exact_mod_cast h
  have hjq : j < iq := by
    apply repair_idx_lt E rho hS htj hiq
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    have h : (w : Int) + 1 ≤ (s : Int) := by exact_mod_cast hws
    push_cast
    nlinarith
  have hkeep := healing_lease_persist E rho hS htj (Nat.lt_succ_of_lt hjq) hqi lease hdl hl'
  have hpost : storeAt p c E rho (iq + 1) x =
      FGSA.clock p (storeAt p c E rho iq x) (SA.voteTime p.toParams (s + 1)) := by
    change (V2.D.Run.stateBefore E rho (iq + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho hiq]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho _ x _
  rw [hpost] at hkeep
  have hFiq : Block.Preceq (eraseFG (storeAt p c E rho iq x).fg.F) Q :=
    block_preceq_trans (eraseFG_preceq (mono hN iq i x hx hqi.le).1) hFQ
  exact healing_support_release_compat (hroots := hrec.base.idealization)
    E rho hE hN hDelta s hSync hx hx ht hiq hτ hFiq lease hkeep

/-- ROOT-DIGEST W2b. Blueprint 21:1520–1534, 1551–1574; plan §3.1 steps 6–7.
DC: INTENTIONAL gate geometry of a later exact-HEAD slot under the frontier cap.
The honest HEAD is a height-m witness. It reaches the gate, where F and Z are below it.
The release argument checks all live leases, including writes at the pending q gate. -/
theorem frontier_gate_geometry [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q B : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    (hqs : q < s) (hgate : SA.gateTime p.toParams s ≤ v) (hBs : B.slot = s)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some B)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s) :
    ExactServiceGateGeometry E rho i x s B := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hd := p.deltaPos
  have hqsI : (q : Int) < (s : Int) := by exact_mod_cast hqs
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hgst.trans (hu.trans ?_)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hvd : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvs : SA.voteTime p.toParams s ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvd).trans hgate
  have hgh : SA.gateTime p.toParams s ≤ rho.horizon := hgate.trans hvh
  have hcovQ := frontier_Q_heads E rho hrec mono crossing writes hgst hErase hHeight
    hService hu hPhase hqv hvh hcap s (Nat.succ_le_of_lt hqs) hvs
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hrec.base.delta hx s (hvs.trans hvh)
  have hhl : headAtLabel p c E rho x s = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz x).st (SA.voteTime p.toParams s)) s) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
    rfl
  have hKB : headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz x).st
      (SA.voteTime p.toParams s)) s = B := Option.some.inj (hhl.symm.trans (hhead x hx))
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) ≤ timeIdx rho v := by
    change (rho.events.filter (fun e => decide (e.time < _))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ v))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).le.trans (hvd.trans hgate)))
  obtain ⟨Kfg, _, hKe, hKm, hrelay⟩ := frontier_head_relay (hroots := hrec.base.idealization)
    E rho crossing hE hN hrec.base.delta
    hrec.sync hHeight hcap hx hjz hgsts (hErase ▸ hcovQ x hx _ hhl)
    (hvd.trans hgh) hcut
  have hKi : Kfg ∈ (storeAt p c E rho i x).fg.TF :=
    (fgsa_store_cumulative p c E rho hN
      (healing_support_idxBefore_le p c E rho hS ht hvd) x).1 (hrelay x hx)
  have hKeB : eraseFG Kfg = B := hKe.trans hKB
  have hiv : i ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS ht hgate).le
  obtain ⟨_, hFK, hZK, hloK⟩ := frontier_self_witness E rho crossing hKm hx
    (hcap i x hiv hx) hKi (block_preceq_refl _)
  have hFB : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) B :=
    hKeB ▸ eraseFG_preceq hFK
  have hK (a : Fin p.n) (ha : rho.seatOf (.base (.head s)) a ∈ rho.honest) (C : Block)
      (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) a)
        (ofHead p ⟨.seat (.head s) a, C⟩) (SA.voteTime p.toParams s)) : C = B := by
    have h := healing_support_emitted_head E rho hS s a C _ he
    exact Option.some.inj (h.symm.trans (hhead _ ha))
  have hreceipt : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B := by
    refine ⟨?_, ?_⟩
    · intro a ha _ C he
      rw [hK a ha C he, clockPre_fg]
      exact hFB
    · intro a ha _ C he
      rw [hK a ha C he]
      exact block_preceq_refl B
  refine { toGateReceiptGeometry := hreceipt
           guard := frontier_gate_guard_of_receipts E rho hrec mono writes hgsts hgh
             hhead hx ht hreceipt hFB
           old_output := ?_
           opening_domain := ?_ }
  · intro hBo
    rcases repair_output_bound E rho hE hN mono hx ht i le_rfl with h | ⟨hm, hsl⟩
    · exact block_preceq_antisymm (block_preceq_trans h hFB) hBo
    · by_contra hne
      have hlt := repair_stored_slot_lt E rho hE i x hm hBo (Ne.symm hne)
      rw [hBs] at hlt
      exact lt_irrefl _ (lt_of_lt_of_le hlt hsl)
  · intro r _
    refine ⟨Kfg, hKeB, ?_⟩
    have hc : frameR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st =
        R_at p c E rho i x := repair_controls_clock _ _
    have hfg : ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st.fg =
        (storeAt p c E rho i x).fg := clock_fg p _ _
    rw [domainR_def, treeT_def, hc, hfg]
    exact (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hKi, hFK, hZK, Kfg, hKi, KitFG.preceq_refl _, hloK⟩

end AvailableChain.FGSA.Run
end
