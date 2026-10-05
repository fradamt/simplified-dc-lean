module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchCompose
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchRise
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchBudget
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3.
First rise, then the first height-M+1 row, with one row selected before both allowances. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, budget arithmetic.
DC: SAME each remaining phase sum fits its frozen total, with a nonnegative tail. -/
theorem frontierSearch_task_bounds [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) (kind : PhaseKind) :
    frontierSearch_remaining p G ΔF ρbar (2 * P p + Γ p G - 9 * p.Δ) kind ≤
        frontierSearchRiseBudget p G ΔF ρbar ∧
    frontierSearch_remaining p G ΔF ρbar (P p - 4 * p.Δ) kind ≤
        frontierSearchRowBudget p G ΔF ρbar ∧
    0 ≤ 2 * P p + Γ p G - 9 * p.Δ ∧ 0 ≤ P p - 4 * p.Δ ∧
    0 ≤ frontierSearchRiseBudget p G ΔF ρbar ∧ 0 ≤ frontierSearchRowBudget p G ΔF ρbar := by
  have hP := frontierSearch_period_bound p
  have hΓ : 4 * p.Δ ≤ Γ p G := hrec.gapPos.trans (fgsa_gamma_bounds p G).1
  have hρ := frontierSearch_allowance_nonneg E rho hrec hmode
  have hg : 0 ≤ E_gF p ΔF G ρbar := by
    rw [E_gF_eq p ΔF G ρbar hbound]
    change 0 ≤ ρbar + 2 * P p + Γ p G - p.Δ
    linarith [p.deltaPos]
  have hj : 0 ≤ E_jF p ΔF G ρbar := by
    change 0 ≤ max _ _
    apply le_trans _ (le_max_right _ _)
    linarith [p.deltaPos]
  have hcR := frontierSearch_contest_rise_cost p G ΔF ρbar hbound
  have hcW := frontierSearch_contest_row_cost p ρbar
  refine ⟨?_, ?_, by linarith [p.deltaPos], by linarith [p.deltaPos], ?_, ?_⟩
  · rw [frontierSearchRiseBudget_eq]
    rw [← hcR]
    cases kind <;> simp [frontierSearch_remaining_eq] <;> linarith only [hg, hj]
  · rw [frontierSearchRowBudget_eq]
    rw [← hcW]
    cases kind <;> simp [frontierSearch_remaining_eq] <;> linarith only [hg, hj]
  · rw [frontierSearchRiseBudget_eq]
    rw [← hcR]
    linarith [p.deltaPos]
  · rw [frontierSearchRowBudget_eq]
    rw [← hcW]
    linarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, first task.
DC: SAME HG.3 reaches a saved seed or advances phase; HG.4 finishes the rise. -/
theorem frontierSearch_rise_task [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (frontier : TFrontier p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hdelay : E.t_GST + 2 * P p ≤ ev.time)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1))
    (hhor : ev.time + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m (ev.time + frontierSearchRiseBudget p G ΔF ρbar) := by
  obtain ⟨hb, _, ht, _, _, _⟩ := frontierSearch_task_bounds E rho hrec hbound hmode kind
  have hbudget : ev.time + frontierSearch_remaining p G ΔF ρbar
      (2 * P p + Γ p G - 9 * p.Δ) kind ≤ ev.time + frontierSearchRiseBudget p G ΔF ρbar := by
    linarith only [hb]
  rcases frontierSearch_phase_tail E rho hrec mono crossing origin repair common hδ hbound
      perm rowsReceipt progressCoverage hfold faultQ honestQuorum
      (2 * P p + Γ p G - 9 * p.Δ) ht hmode hstart hdelay
      ((hbudget).trans hhor) with hr | ⟨t, _, htail, hserved⟩
  · exact frontierSearch_rise_mono p c E rho (hbudget) hr
  · have hf := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.1
    exact frontierSearch_rise_mono p c E rho (htail.trans (hbudget))
      (healing_frontierTail_rise_of_seed E rho hrec hδ hbound crossing frontier
        rowsReceipt progressCoverage hfold faultQ honestQuorum hf.le hserved
        ((htail.trans (hbudget)).trans hhor))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, row provenance.
DC: SAME a rise past m supplies an earlier real height-m row through RCap. -/
theorem frontierSearch_row_of_rise (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (cap : RCap p c E rho)
    {i m : Nat} {D : Time} (hm : 1 ≤ m) (hrise : FrontierRiseBy p c E rho i m D) :
    FirstHeightRowBy p c E rho m D := by
  obtain ⟨j, ev, _, hj, ht, hh, _⟩ := (frontierRiseBy_iff p c E rho i m D).mp hrise
  obtain ⟨x, W, hW, hWh⟩ := (healing_phaseWitness p c E rho (i := j + 1)
        (m := frontierAtIdx p c E rho (j + 1)) (by omega) rfl).frontier
  obtain ⟨l, z, r, a, e, hlj, ha, hn, _⟩ := cap (m - 1) (j + 1) x W hW
    (by simp only [Height] at *; omega)
  have hn' : namedEntry a.payload.height_pair = some (m, e) := by
    simpa only [Nat.sub_add_cancel hm] using hn
  have hcut : l < timeIdx rho ev.time := by
    have hjcut := healing_phase_lt_timeIdx p c E rho hs hj le_rfl
    exact (Nat.le_of_lt_succ hlj).trans_lt hjcut
  exact frontierSearch_first_row p c E rho ⟨l, z, a, e, ha, hn'⟩
    ((frontierSearch_event_time_le p c E rho hs ha.2.1 hcut).trans ht)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1722–1800; S5 F3, second task.
DC: SAME HG.3 plus the HG.4 row tail keeps exact height m and the frozen row budget. -/
theorem frontierSearch_row_task [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (cap : RCap p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hdelay : E.t_GST + 2 * P p ≤ ev.time)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1))
    (hhor : ev.time + frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon) :
    FirstHeightRowBy p c E rho m (ev.time + frontierSearchRowBudget p G ΔF ρbar) := by
  obtain ⟨_, hb, _, ht, _, _⟩ := frontierSearch_task_bounds E rho hrec hbound hmode kind
  have hbudget : ev.time + frontierSearch_remaining p G ΔF ρbar
      (P p - 4 * p.Δ) kind ≤ ev.time + frontierSearchRowBudget p G ΔF ρbar := by
    linarith only [hb]
  rcases frontierSearch_phase_tail E rho hrec mono crossing origin repair common hδ hbound
      perm rowsReceipt progressCoverage hfold faultQ honestQuorum
      (P p - 4 * p.Δ) ht hmode hstart hdelay
      ((hbudget).trans hhor) with hr | ⟨t, _, htail, hserved⟩
  · have hm := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.2.1
    exact frontierSearch_row_of_rise E rho hrec.base.valid.toScheduleWellFormed cap hm
      (frontierSearch_rise_mono p c E rho (hbudget) hr)
  · obtain ⟨r, hr, hfirst, htime⟩ :=
      (firstHeightRowBy_iff p c E rho m _).mp
        (healing_frontierTail_row E rho hrec mono crossing cap writes rowCoverage hserved
          ((htail.trans (hbudget)).trans hhor))
    exact (firstHeightRowBy_iff p c E rho m _).mpr
      ⟨r, hr, hfirst, htime.trans (htail.trans (hbudget))⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1744–1800; S5 F3, inclusive cut.
DC: SAME Recovery₂ gives an honest node and a cut event under the task's horizon. -/
theorem frontierSearch_cut_start [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {rG M : Nat} {u₀ : Time} (hgst : E.t_GST ≤ p.actionTime rG)
    (hfirst : ∀ r, E.t_GST ≤ p.actionTime r → rG ≤ r)
    (hu₀ : u₀ = p.actionTime (rG + 2)) (hdelay : E.t_GST + 2 * P p ≤ u₀)
    (hM : M = honestFrontier p c E rho u₀) (hhor : u₀ ≤ rho.horizon) :
    ∃ i ev kind, FrontierSearchStart p c E rho i ev M kind ∧
      ev.time = u₀ ∧ timeIdx rho u₀ = i + 1 := by
  classical
  have hne : rho.honest.Nonempty := by
    have hn : Fintype.card V = p.n :=
      (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hf := hrec.fault
    rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
    have := p.nPos
    omega
  obtain ⟨x, hx⟩ := hne
  have hs := hrec.base.valid.toScheduleWellFormed
  have hgrid : u₀ = ((4 * ((rG + 2) * p.R) + 6 : Nat) : Time) * p.Δ := by
    rw [hu₀]
    change 4 * p.Δ * (((rG + 2) * p.R : Nat) : Time) + 6 * p.Δ = _
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx
    (4 * ((rG + 2) * p.R) + 6) (hgrid ▸ hhor)
  rw [← hgrid] at hj
  have hcut : ∃ (i : Nat) (ev : V2.Event V (Obj p)), rho.events[i]? = some ev ∧
      ev.time = u₀ ∧ timeIdx rho u₀ = i + 1 :=
    (reset_inclusive_start_iff p c E rho hs u₀).mpr
      ⟨.tick x u₀, List.mem_of_getElem? hj, rfl⟩
  obtain ⟨i, ev, hi, ht, hidx⟩ := hcut
  have hfront : frontierAtIdx p c E rho (i + 1) = M := by
    rw [← hidx]
    exact (hM.trans (reset_inclusive_frontier p c E rho hs u₀)).symm
  have hm : 1 ≤ M := by
    have hg := (storeBundle_stateBefore E rho (i + 1) x).cstore.fg.gen
    have hh := ((fgCertificateLaws p).height.one_le_h .genesis).trans
      ((healing_phase_height_le p c E rho hg).trans (healing_phase_local_le_frontier p c E rho hx))
    exact hh.trans_eq hfront
  have kinds : ∃ kind, AttemptPhaseAt p c E rho (i + 1) M kind := by
    by_cases hc : ContestEvidence p c E rho (i + 1) M
    · exact ⟨.contest, hc⟩
    · by_cases ht : TopEvidence p c E rho (i + 1) M
      · exact ⟨.topJ, ht, hc⟩
      · exact ⟨.gap, ht, hc⟩
  obtain ⟨kind, hkind⟩ := kinds
  refine ⟨i, ev, kind, (frontierSearchStart_iff p c E rho i ev M kind).mpr
    ⟨hi, ?_, Or.inr ⟨rG, hgst, hfirst, ht.trans hu₀, ?_⟩, hfront, hm, hkind⟩, ht, hidx⟩
  · rw [ht]
    have hP := frontierSearch_period_bound p
    linarith [p.deltaPos]
  · rw [ht]
    exact hidx

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1744–1800; S5 F3.
DC: SAME event order also permits equal timestamps. -/
theorem frontierSearch_event_time_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {ev ev' : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) (hj : rho.events[j]? = some ev') (hij : i ≤ j) :
    ev.time ≤ ev'.time := by
  by_cases he : i = j
  · subst j
    have hev : ev = ev' := Option.some.inj (hi.symm.trans hj)
    exact hev ▸ le_rfl
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl (by omega)
    rw [hie, hje] at hk
    exact V2.D.Engine.time_le_of_key_le _ _ hk

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1744–1800; S5 F3.
DC: SAME classify a frontier by its accepted evidence. -/
theorem frontierSearch_phase_exists (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i m : Nat) : ∃ kind, AttemptPhaseAt p c E rho i m kind := by
  classical
  by_cases hc : ContestEvidence p c E rho i m
  · exact ⟨.contest, hc⟩
  · by_cases ht : TopEvidence p c E rho i m
    · exact ⟨.topJ, ht, hc⟩
    · exact ⟨.gap, ht, hc⟩

end AvailableChain.FGSA.Run
end
