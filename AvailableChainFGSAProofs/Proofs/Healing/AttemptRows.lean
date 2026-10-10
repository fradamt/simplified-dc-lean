module
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptBudget
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptStop
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntry
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionTerminal
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneRepair

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem attempt_period_bounds (p : Params) : 8 * p.Δ ≤ P p := by
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
  nlinarith [p.deltaPos]

private theorem attempt_honest_nonempty [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn := card_eq_n_of_linked hrec.base.linked
  have hc : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hle := Finset.card_le_univ rho.honest
    rw [hn] at hle
    omega
  have hf := hrec.fault
  have hp := p.nPos
  exact Finset.card_pos.mp (by omega)

omit [DecidableEq V] in
private theorem attempt_time_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {ev : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) {D : Time} (hD : i < timeIdx rho D) : ev.time ≤ D := by
  have he : rho.events.filter (fun e => decide (e.time < D + 1)) =
      rho.events.filter (fun e => decide (e.time ≤ D)) :=
    List.filter_congr (fun e _ => by simp only [Int.lt_add_one_iff])
  have hiD : i < V2.D.Run.idxBefore rho (D + 1) := by
    rw [V2.D.Run.idxBefore_def, he]
    exact hD
  exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi (D + 1)).mp hiD)

private theorem attempt_quiet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : AttemptKey} {ev : V2.Event V (Obj p)}
    {budget : Time} (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget) :
    ∀ j, k.start < j → j < timeIdx rho (ev.time + budget) →
      ¬ EffectiveEvent p c E rho j := by
  intro j hj hcut
  have hjlen : j < rho.events.length := hcut.trans_le (List.length_filter_le _ _)
  have hev := List.getElem?_eq_getElem hjlen
  exact healing_attempt_no_event E rho hstart hstop hj hev
    (attempt_time_le E rho hs hev hcut)

private theorem attempt_row_of_covered [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget : Time} {r : Nat} {Q : Block}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (htask : k.task = .firstRow) (hr : p.actionTime r ≤ ev.time + budget)
    (hcovered : OpeningCovered p c E rho r Q)
    (hentry : OpeningEntry p c E rho r k.frontier) : AttemptEndsBy p c E rho k budget := by
  obtain ⟨x, hx⟩ := attempt_honest_nonempty E rho hrec
  obtain ⟨K, nd, j, rSent, a, _hnd, hK, _hmem, _hQ, hrr, ha, hn⟩ := hcovered x hx
  obtain ⟨e, he⟩ := hentry
  have hn' : namedEntry a.payload.height_pair = some (k.frontier, e) := by
    obtain ⟨hh, ht⟩ := he x K hx hK
    rwa [hh, ht] at hn
  have hj : k.start < j := by
    by_contra h
    obtain ⟨_, _, _, _, _, _, _, _, hnone⟩ := hvalid
    exact hnone htask j x rSent a k.frontier e (Nat.le_of_not_gt h) ha hn' rfl
  have hsend : p.actionTime rSent ≤ p.actionTime r := by
    rw [actionTime_periodW, actionTime_periodW]
    have hrr' : (rSent : Time) ≤ r := by exact_mod_cast hrr
    have hP := attempt_period_bounds p
    nlinarith [p.deltaPos]
  exact healing_attempt_ends_of_row E rho hstart hj ha.2.1 (hsend.trans hr) htask ha hn'

section Rows
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (heldServices : ∀ i (ev : V2.Event V (Obj p)) x W,
      rho.events[i]? = some ev → x ∈ rho.honest → E.t_GST ≤ ev.time →
      W ∈ (storeAt p c E rho (i + 1) x).fg.TF →
      (heightView p W).h = frontierAtIdx p c E rho (i + 1) →
      ev.time + p.Δ ≤ rho.horizon → WitnessReceiptScope E rho W (ev.time + p.Δ))
    (crossing : RXing p c E rho)
    (qc : RQCOrigin p c E rho)
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


include hrec mono heldServices crossing qc writes rowCoverage

omit mono heldServices qc writes rowCoverage in
private theorem attempt_proposal_heights
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hp : PhaseInterval p c E rho u D m J contested)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams q ≤ D)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (heq : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q) :
    (if contested then m else m - 1) ≤ (heightView p Qfg).h ∧
      (heightView p Qfg).h ≤ m := by
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _hem, hst, _hslot, _hb, _hrows⟩ :=
    healing_promotion_proposal_read p c E rho hS hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
    (SA.proposalTime p.toParams q)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hui := healing_support_idxBefore_le p c E rho hS hj hu
  have hjD := (healing_phase_lt_timeIdx p c E rho hS hj (hqg.trans hgate)).le
  obtain ⟨hH, hc, _hr⟩ := hp.2.2.2 j x hui hjD hx
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, _hB, heB, hlo⟩ := healing_proposer_floor p c E rho hS q Q st hQ hst hne
  have he : B = Qfg.parent := eraseFG_injective (heB.trans
    (by rw [← eraseFG_parent, heq]))
  have hH' : st.fg.h_max = m := by rw [hfg]; exact hH
  have hc' : (FGSA.controls p st).contest = contested := by
    change (KitFG.treeStoreControlsView (heightView p) st.fg).contest = contested
    rw [hfg]
    exact hc
  change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _ at hlo
  rw [hH', hc', he] at hlo
  have hparent : FGBlock.Preceq Qfg.parent Qfg := by
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
  refine ⟨hlo.trans ((fgCertificateLaws p).height.h_mono hparent), ?_⟩
  obtain ⟨i, K, hi, hK, heK⟩ := healing_rise_one_gate_copy p c E rho hS hexact
    (hgate.trans hp.2.1) hx
  have hKe : K = Qfg := eraseFG_injective (heK.trans heq.symm)
  subst K
  have hui' := healing_support_idxBefore_le p c E rho hS hi (hu.trans hqg)
  have hiD := (healing_phase_lt_timeIdx p c E rho hS hi hgate).le
  have hcap := (hp.2.2.2 i x hui' hiD hx).1
  exact hcap ▸ healing_phase_height_le p c E rho hK

private theorem attempt_repair_opening
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget)
    (hhor : ev.time + budget ≤ rho.horizon)
    (hbudget : ev.time + 3 * p.Δ + ρΓ p G + (P p - 4 * p.Δ) ≤ ev.time + budget) :
    ∃ (β q : Nat) (Q : Block) (Qfg : FGBlock (Fin p.n)) (r : Nat)
      (root : Option (FGBlock (Fin p.n))) (contested : Bool),
      let u := ev.time + 3 * p.Δ
      PhaseInterval p c E rho u (ev.time + budget) k.frontier root contested ∧
      (contested = true ↔ k.phase = .contest) ∧
      E.t_GST ≤ u ∧ u ≤ SA.proposalTime p.toParams q ∧
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q ∧
      SA.gateTime p.toParams q ≤ u + ρΓ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q ∧
      eraseFG Qfg = Q ∧
      (if contested then k.frontier else k.frontier - 1) ≤ (heightView p Qfg).h ∧
      (heightView p Qfg).h ≤ k.frontier ∧
      q ≤ r * p.R ∧ p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) ∧
      OpeningCovered p c E rho r Q ∧
      (∀ v, PhaseInterval p c E rho u v k.frontier root contested →
        RepairAfter p c E rho (β + 2 * p.k - 1) v) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hP := attempt_period_bounds p
  have huD : ev.time + 3 * p.Δ ≤ ev.time + budget := by
    have hΓ : 0 ≤ Γ p G := by
      have := (fgsa_gamma_bounds p G).1
      linarith [hrec.gapPos, p.deltaPos]
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    have hρ : 0 ≤ ρΓ p G := by
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos]
    linarith [p.deltaPos]
  obtain ⟨J, hp, _hframe⟩ := healing_attempt_settle_start p c E rho mono heldServices crossing hrec
    hvalid hstart huD hhor (attempt_quiet E rho hS hstart hstop)
  let u := ev.time + 3 * p.Δ
  have hsettled : ∃ (root : Option (FGBlock (Fin p.n))) (contested : Bool),
      PhaseInterval p c E rho u (ev.time + budget) k.frontier root contested ∧
      (contested = true ↔ k.phase = .contest) := by
    refine ⟨_, _, hp, ?_⟩
    cases k.phase with
    | gap => constructor <;> intro h <;> cases h
    | topJ => constructor <;> intro h <;> cases h
    | contest => exact ⟨fun _ => rfl, fun _ => rfl⟩
  obtain ⟨root, contested, hp, hcont⟩ := hsettled
  have hgst0 : E.t_GST ≤ ev.time := by
    obtain ⟨ev0, hi0, hgst0, _⟩ := hvalid
    have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
    exact he ▸ hgst0
  have hgst : E.t_GST ≤ u := by dsimp only [u]; linarith [p.deltaPos]
  obtain ⟨β, hβ, hmin⟩ := healing_rise_one_grid p u
  have hrepair := healing_tRepair E rho hrec mono crossing qc writes
  have hafter := ((hrepair G u _ _ root contested hrec.gap hrec.gapPos hgst hp).1 β hβ hmin).1
  obtain ⟨q, Q, hq, hgate, hQ, hexact⟩ :=
    ((hrepair G u _ _ root contested hrec.gap hrec.gapPos hgst hp).1 β hβ hmin).2
      (by dsimp only [u]; linarith [p.deltaPos])
  have hβl : β ≤ β + 2 * p.k - 1 := by
    have hk : 1 ≤ 2 * p.k := by have := p.kLarge; omega
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hk β)
  have hβI : (β : Time) ≤ ((β + 2 * p.k - 1 : Nat) : Time) := by exact_mod_cast hβl
  have hβt : SA.proposalTime p.toParams β ≤
      SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
    change 4 * p.Δ * (β : Time) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Time)
    nlinarith [p.deltaPos]
  have huq := hβ.le.trans (hβt.trans hq.le)
  have hgateD : SA.gateTime p.toParams q ≤ ev.time + budget := by
    dsimp only [u] at hgate
    linarith [p.deltaPos]
  obtain ⟨_i, Qfg, _hi, _hK, heq⟩ := healing_rise_one_gate_copy p c E rho hS hexact
    (hgateD.trans hhor) hQ.1.2
  obtain ⟨hlo, hhi⟩ := attempt_proposal_heights E rho hrec crossing
    hp huq hgateD hQ heq hexact
  have hex : ∃ r, q ≤ r * p.R := by
    refine ⟨q, le_mul_of_one_le_right (Nat.zero_le q) ?_⟩
    exact le_trans (by decide : 1 ≤ (2 : Nat)) p.RLarge
  let r := Nat.find hex
  have hqr : q ≤ r * p.R := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) q r hqr hfirst
  have har : p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) := by linarith
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hur : u ≤ p.actionTime r := by linarith
  have hpr := opening_phase_restrict E rho hp hur (har.trans hbudget)
  have hc := common_opening_covered E rho hrec mono crossing writes rowCoverage hgst
    hQ heq hexact huq hqr hpr
  refine ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, ?_⟩
  intro v hv
  exact ((hrepair G u v _ root contested hrec.gap hrec.gapPos hgst hv).1 β hβ hmin).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 firstRow / contest, with the standing ports and exact INLINE bodies.
The SO producer is rowPermission_covered. Both AttemptValid start arms are covered. -/
theorem healing_attempt_firstRow_contest
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  classical
  by_contra hstop
  have hbudget := healing_attempt_firstRow_contest_budget p G k htask hphase
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, _hq, _hgate, hQ, hexact, heq,
    hlo, hhi, hqr, har, hc, _hrepair⟩ := attempt_repair_opening E rho hrec mono crossing qc
      writes rowCoverage hvalid hstart hstop hhor (by rw [hbudget]; ring_nf; rfl)
  have hctrue : contested = true := hcont.mpr hphase
  rw [hctrue] at hp hlo
  have hh : (heightView p Qfg).h = k.frontier := Nat.le_antisymm hhi hlo
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hur : ev.time + 3 * p.Δ ≤ p.actionTime r := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hpr := opening_phase_restrict E rho hp hur (by rw [hbudget]; linarith)
  have he := common_entry_at_high E rho hrec mono crossing writes hgst hQ heq hexact huq
    hqr hpr hh
  exact hstop (attempt_row_of_covered E rho hrec hvalid hstart htask
    (by rw [hbudget]; linarith) hc he)

omit [Fintype V] hrec mono heldServices crossing qc writes rowCoverage in
private theorem attempt_row_of_high_source
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget : Time} {r : Nat} {Q : Block}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (htask : k.task = .firstRow) (hr : p.actionTime r ≤ ev.time + budget)
    (hcovered : OpeningCovered p c E rho r Q)
    {x : V} {K : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hh : (heightView p K).h = k.frontier) : AttemptEndsBy p c E rho k budget := by
  obtain ⟨L, nd, j, rSent, a, _hnd, hL, _hmem, _hQ, hrr, ha, hn⟩ := hcovered x hx
  have he : L = K := Option.some.inj (Option.some.inj (hL.symm.trans hK))
  subst L
  rw [hh] at hn
  have hj : k.start < j := by
    by_contra h
    obtain ⟨_, _, _, _, _, _, _, _, hnone⟩ := hvalid
    exact hnone htask j x rSent a k.frontier _ (Nat.le_of_not_gt h) ha hn rfl
  have hsend : p.actionTime rSent ≤ p.actionTime r := by
    rw [actionTime_periodW, actionTime_periodW]
    have hrr' : (rSent : Time) ≤ r := by exact_mod_cast hrr
    have hP := attempt_period_bounds p
    nlinarith [p.deltaPos]
  exact healing_attempt_ends_of_row E rho hstart hj ha.2.1 (hsend.trans hr) htask ha hn

variable
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))

include hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 firstRow / gap or topJ, with standing ports and the exact INLINE facts.
The low-entry branch uses renewed promotion within its existing gate horizon. -/
theorem healing_attempt_firstRow_other
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  classical
  by_contra hstop
  have hbudget := healing_attempt_firstRow_other_budget p G k htask hphase
  have hP := attempt_period_bounds p
  have hΓ : 0 ≤ Γ p G := by
    have := (fgsa_gamma_bounds p G).1
    linarith [hrec.gapPos, p.deltaPos]
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, hgate, hQ, hexact, heq,
    hlo, hhi, hqr, har, hc, hrepair⟩ := attempt_repair_opening E rho hrec mono crossing qc
      writes rowCoverage hvalid hstart hstop hhor (by rw [hbudget]; linarith [p.deltaPos])
  let u := ev.time + 3 * p.Δ
  have hcfalse : contested = false := Bool.eq_false_iff.mpr (fun ht => hphase (hcont.mp ht))
  rw [hcfalse] at hp hlo hrepair
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hur : u ≤ p.actionTime r := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    dsimp only [u]
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hrD : p.actionTime r ≤ ev.time + attemptBudget p G k := by
    rw [hbudget]; linarith [p.deltaPos]
  have hpr := opening_phase_restrict E rho hp hur hrD
  by_cases hh : (heightView p Qfg).h = k.frontier
  · have he := common_entry_at_high E rho hrec mono crossing writes hgst hQ heq hexact huq
      hqr hpr hh
    exact hstop (attempt_row_of_covered E rho hrec hvalid hstart htask hrD hc he)
  have hlow : (heightView p Qfg).h = k.frontier - 1 := by
    simp only [Bool.false_eq_true, ↓reduceIte, Height] at hlo hhi hh ⊢
    omega
  rcases common_entry_at_low E rho hrec mono crossing writes hgst hQ heq hexact huq hqr
      hpr hlow with he | ⟨⟨x, K, hx, hK, hhigh⟩, _hnext⟩
  · have hpromotionHor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon := by
      apply le_trans _ hhor
      rw [hbudget]
      linarith [p.deltaPos]
    have perm := healing_tPerm E rho hrec mono crossing writes
    rcases healing_renewedPromotion E rho hrec hδ hbound mono crossing perm rowsReceipt
        progressCoverage hfold faultQ honestQuorum r hpromotionHor u k.frontier root false
        (β + 2 * p.k - 1) q Q (k.frontier - 1) hgst hpr huq hqr hq hQ hexact he hc
        hrepair with hevent | hcarrier
    · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
      have hsi : k.start < V2.D.Run.idxBefore rho (p.actionTime r) :=
        (Gen.V2.Duty.index_lt_idxBefore_iff hrec.base.valid.toScheduleWellFormed hstart _).mpr
          (by
            change ev.time < p.actionTime r
            dsimp only [u] at hur
            exact (lt_add_of_pos_right ev.time
              (mul_pos (by decide : (0 : Time) < 3) p.deltaPos)).trans_le hur)
      have hj : k.start < i := hsi.trans_le
        ((preIdx_le_afterTicksIdx E rho hrec.base.valid.toScheduleWellFormed _).1.trans hi)
      exact hstop (healing_attempt_ends_of_event E rho hstart hj hev'
        (by
          calc
            ev'.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ := ht
            _ ≤ ev.time + attemptBudget p G k := by
              rw [hbudget]
              linarith only [har, hP, p.deltaPos]) heff)
    · obtain ⟨s, X, hnew, hslot, hslo, hshi, hheight, _hreceipt, hservice⟩ := hcarrier
      have ha := actionTime_periodW p r
      have hurS : u ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
      have hsGate : SA.gateTime p.toParams s ≤
          p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
        change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
        linarith
      have hsD : SA.gateTime p.toParams s ≤ ev.time + attemptBudget p G k := by
        rw [hbudget]; linarith [p.deltaPos]
      have hps := opening_phase_restrict E rho hp
        (by change u ≤ SA.proposalTime p.toParams s + 6 * p.Δ; linarith [p.deltaPos]) hsD
      obtain ⟨hexactS, _⟩ := hservice hps
      have hheights := attempt_proposal_heights E rho hrec crossing
        hp hurS hsD hnew rfl hexactS
      have hm : 1 ≤ k.frontier := by obtain ⟨_, _, _, _, _, hm, _⟩ := hvalid; exact hm
      have hhS : (heightView p X).h = k.frontier := by
        have hXhigh : k.frontier ≤ (heightView p X).h := by
          simpa only [Nat.sub_add_cancel hm] using hheight
        exact Nat.le_antisymm hheights.2 hXhigh
      have hex : ∃ r', s ≤ r' * p.R := by
        refine ⟨s, le_mul_of_one_le_right (Nat.zero_le s) ?_⟩
        exact le_trans (by decide : 1 ≤ (2 : Nat)) p.RLarge
      let r' := Nat.find hex
      have hsr : s ≤ r' * p.R := Nat.find_spec hex
      have hfirst : ∀ r'', s ≤ r'' * p.R → r' ≤ r'' := fun r'' hr'' => Nat.find_min' hex hr''
      obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) s r' hsr hfirst
      have hr'D : p.actionTime r' ≤ ev.time + attemptBudget p G k := by
        rw [hbudget]; linarith [p.deltaPos]
      have hur' : u ≤ p.actionTime r' := by
        have hsg : SA.gateTime p.toParams s = SA.proposalTime p.toParams s + 6 * p.Δ := rfl
        rw [hsg] at h0
        linarith [p.deltaPos]
      have hpr' := opening_phase_restrict E rho hp hur' hr'D
      have hc' := common_opening_covered E rho hrec mono crossing writes rowCoverage hgst
        hnew rfl hexactS hurS hsr hpr'
      have he' := common_entry_at_high E rho hrec mono crossing writes hgst hnew rfl hexactS
        hurS hsr hpr' hhS
      exact hstop (attempt_row_of_covered E rho hrec hvalid hstart htask hr'D hc' he')
  · exact hstop (attempt_row_of_high_source E rho
      hvalid hstart htask hrD hc hx hK hhigh)

omit qc rowCoverage in
private theorem attempt_terminal_contradiction
    {k : AttemptKey} {ev : V2.Event V (Obj p)} {budget u : Time}
    {root : Option (FGBlock (Fin p.n))} {contested : Bool} {q r : Nat} {Q : Block}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy p c E rho k budget)
    (hp : PhaseInterval p c E rho u (ev.time + budget) k.frontier root contested)
    (hu : ev.time + 3 * p.Δ ≤ u) (hgst : E.t_GST ≤ u)
    (huq : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (he : OpeningEntry p c E rho r k.frontier)
    (hc : OpeningCovered p c E rho r Q)
    (hterminal : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ ev.time + budget) :
    False := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hP := attempt_period_bounds p
  have hΓ : 0 ≤ Γ p G := by
    have := (fgsa_gamma_bounds p G).1
    linarith [hrec.gapPos, p.deltaPos]
  have hur : u ≤ p.actionTime r := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    change u ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hrD : p.actionTime r ≤ ev.time + budget := by linarith [p.deltaPos]
  have hpr := opening_phase_restrict E rho hp hur hrD
  have perm := healing_tPerm E rho hrec mono crossing writes
  rcases healing_renewedPromotion_terminal E rho hrec hδ hbound mono crossing perm
      rowsReceipt progressCoverage hfold faultQ honestQuorum r (hterminal.trans hp.2.1)
      u k.frontier root contested q Q k.frontier hgst hpr huq hqr he hc
      with hevent | hcarrier
  · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
    have hsi : k.start < V2.D.Run.idxBefore rho (p.actionTime r) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hstart _).mpr (by
        change ev.time < p.actionTime r
        linarith [p.deltaPos])
    have hj : k.start < i := hsi.trans_le ((preIdx_le_afterTicksIdx E rho hS _).1.trans hi)
    exact hstop (healing_attempt_ends_of_event E rho hstart hj hev'
      (ht.trans hterminal) heff)
  · obtain ⟨s, X, _hnew, _hslot, hslo, hshi, hh, y, hy, hheld⟩ := hcarrier
    let d := SA.proposalTime p.toParams s + p.Δ
    have ha := actionTime_periodW p r
    have hud : u ≤ d := by dsimp only [d]; linarith [p.deltaPos]
    have hdD : d ≤ ev.time + budget := by dsimp only [d]; linarith
    change X ∈ (V2.D.Run.stateBeforeTime E rho d y).st.fg.TF at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hS] at hheld
    have hcap := (hp.2.2.2 (V2.D.Run.idxBefore rho d) y
      (healing_phase_idxBefore_mono p c rho hud)
      (healing_phase_idx_le_time p c rho hdD) hy).1
    have hle := healing_phase_height_le p c E rho hheld
    change (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.h_max = k.frontier at hcap
    rw [hcap] at hle
    simp only [Height] at hh hle
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 raise / contest, with the standing ports and exact INLINE bodies.
Terminal promotion uses the first high opening within the frozen budget. -/
theorem healing_attempt_raise_contest
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  classical
  by_contra hstop
  have hbudget := healing_attempt_raise_contest_budget p G k htask hphase
  have hP := attempt_period_bounds p
  have hΓ : 0 ≤ Γ p G := by
    have := (fgsa_gamma_bounds p G).1
    linarith [hrec.gapPos, p.deltaPos]
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, _hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, hrepair⟩ := attempt_repair_opening E rho hrec mono crossing
      qc writes rowCoverage hvalid hstart hstop hhor (by rw [hbudget]; linarith [p.deltaPos])
  have hctrue : contested = true := hcont.mpr hphase
  rw [hctrue] at hp hlo hrepair
  have hh : (heightView p Qfg).h = k.frontier := Nat.le_antisymm hhi hlo
  have hur : ev.time + 3 * p.Δ ≤ p.actionTime r := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hpr := opening_phase_restrict E rho hp hur (by rw [hbudget]; linarith [p.deltaPos])
  have he := common_entry_at_high E rho hrec mono crossing writes hgst hQ heq hexact huq
    hqr hpr hh
  exact attempt_terminal_contradiction E rho hrec mono crossing writes hδ
    hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hstop hp
    le_rfl hgst huq hqr he hc (by rw [hbudget]; linarith only [har])

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
H.10 raise / gap or topJ, with the standing ports and exact INLINE bodies.
The low pivot uses existing gate service. Terminal promotion then uses a high opening. -/
theorem healing_attempt_raise_other
    {k : AttemptKey} {ev : V2.Event V (Obj p)}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hhor : ev.time + attemptBudget p G k ≤ rho.horizon)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    AttemptEndsBy p c E rho k (attemptBudget p G k) := by
  classical
  by_contra hstop
  have hbudget := healing_attempt_raise_other_budget p G k htask hphase
  have hP := attempt_period_bounds p
  have hΓ : 0 ≤ Γ p G := by
    have := (fgsa_gamma_bounds p G).1
    linarith [hrec.gapPos, p.deltaPos]
  obtain ⟨β, q, Q, Qfg, r, root, contested, hp, hcont, hgst, huq, hq, _hgate, hQ, hexact,
    heq, hlo, hhi, hqr, har, hc, hrepair⟩ := attempt_repair_opening E rho hrec mono crossing
      qc writes rowCoverage hvalid hstart hstop hhor (by rw [hbudget]; linarith [p.deltaPos])
  let u := ev.time + 3 * p.Δ
  have hcfalse : contested = false := Bool.eq_false_iff.mpr (fun ht => hphase (hcont.mp ht))
  rw [hcfalse] at hp hlo hrepair
  have hur : u ≤ p.actionTime r := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    dsimp only [u]
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    change ev.time + 3 * p.Δ ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hrD : p.actionTime r ≤ ev.time + attemptBudget p G k := by
    rw [hbudget]; linarith [p.deltaPos]
  have hpr := opening_phase_restrict E rho hp hur hrD
  by_cases hh : (heightView p Qfg).h = k.frontier
  · have he := common_entry_at_high E rho hrec mono crossing writes hgst hQ heq hexact huq
      hqr hpr hh
    exact attempt_terminal_contradiction E rho hrec mono crossing writes hδ
      hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hstop hp
      le_rfl hgst huq hqr he hc (by rw [hbudget]; linarith [p.deltaPos])
  have hlow : (heightView p Qfg).h = k.frontier - 1 := by
    simp only [Bool.false_eq_true, ↓reduceIte, Height] at hlo hhi hh ⊢
    omega
  rcases common_entry_at_low E rho hrec mono crossing writes hgst hQ heq hexact huq hqr
      hpr hlow with he | ⟨⟨x, K, hx, hK, hhigh⟩, hnext⟩
  · have hpromotionHor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon := by
      apply le_trans _ hhor
      rw [hbudget]
      linarith [p.deltaPos]
    have perm := healing_tPerm E rho hrec mono crossing writes
    rcases healing_renewedPromotion E rho hrec hδ hbound mono crossing perm rowsReceipt
        progressCoverage hfold faultQ honestQuorum r hpromotionHor u k.frontier root false
        (β + 2 * p.k - 1) q Q (k.frontier - 1) hgst hpr huq hqr hq hQ hexact he hc
        hrepair with hevent | hcarrier
    · obtain ⟨i, ev', hi, hev', heff, ht⟩ := hevent
      have hsi : k.start < V2.D.Run.idxBefore rho (p.actionTime r) :=
        (Gen.V2.Duty.index_lt_idxBefore_iff hrec.base.valid.toScheduleWellFormed hstart _).mpr
          (by change ev.time < p.actionTime r; dsimp only [u] at hur; linarith [p.deltaPos])
      have hj : k.start < i := hsi.trans_le
        ((preIdx_le_afterTicksIdx E rho hrec.base.valid.toScheduleWellFormed _).1.trans hi)
      exact hstop (healing_attempt_ends_of_event E rho hstart hj hev'
        (by
          calc
            ev'.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ := ht
            _ ≤ ev.time + attemptBudget p G k := by
              rw [hbudget]
              linarith only [har, hP, hΓ, p.deltaPos]) heff)
    · obtain ⟨s, X, hnew, _hslot, hslo, hshi, hheight, _hreceipt, hservice⟩ := hcarrier
      have ha := actionTime_periodW p r
      have hurS : u ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
      have hsGate : SA.gateTime p.toParams s ≤
          p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
        change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
        linarith
      have hsD : SA.gateTime p.toParams s ≤ ev.time + attemptBudget p G k := by
        rw [hbudget]; linarith [p.deltaPos]
      have hps := opening_phase_restrict E rho hp
        (by change u ≤ SA.proposalTime p.toParams s + 6 * p.Δ; linarith [p.deltaPos]) hsD
      obtain ⟨hexactS, _⟩ := hservice hps
      have hheights := attempt_proposal_heights E rho hrec crossing hp hurS hsD hnew rfl hexactS
      have hm : 1 ≤ k.frontier := by obtain ⟨_, _, _, _, _, hm, _⟩ := hvalid; exact hm
      have hhS : (heightView p X).h = k.frontier := by
        have hXhigh : k.frontier ≤ (heightView p X).h := by
          simpa only [Nat.sub_add_cancel hm] using hheight
        exact Nat.le_antisymm hheights.2 hXhigh
      have hex : ∃ r', s ≤ r' * p.R := by
        refine ⟨s, le_mul_of_one_le_right (Nat.zero_le s) ?_⟩
        exact le_trans (by decide : 1 ≤ (2 : Nat)) p.RLarge
      let r' := Nat.find hex
      have hsr : s ≤ r' * p.R := Nat.find_spec hex
      have hfirst : ∀ r'', s ≤ r'' * p.R → r' ≤ r'' := fun r'' hr'' => Nat.find_min' hex hr''
      obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) s r' hsr hfirst
      have hr'D : p.actionTime r' ≤ ev.time + attemptBudget p G k := by
        rw [hbudget]; linarith [p.deltaPos]
      have hur' : u ≤ p.actionTime r' := by
        have hsg : SA.gateTime p.toParams s = SA.proposalTime p.toParams s + 6 * p.Δ := rfl
        rw [hsg] at h0
        linarith [p.deltaPos]
      have hpr' := opening_phase_restrict E rho hp hur' hr'D
      have hc' := common_opening_covered E rho hrec mono crossing writes rowCoverage hgst
        hnew rfl hexactS hurS hsr hpr'
      have he' := common_entry_at_high E rho hrec mono crossing writes hgst hnew rfl hexactS
        hurS hsr hpr' hhS
      exact attempt_terminal_contradiction E rho hrec mono crossing writes hδ
        hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hstop hp
        le_rfl hgst hurS hsr he' hc'
        (by rw [hbudget]; linarith only [har, hsGate, h1])
  · have hanext : p.actionTime (r + 1) = p.actionTime r + P p := by
      rw [actionTime_periodW, actionTime_periodW]
      push_cast
      ring
    have hur' : u ≤ p.actionTime (r + 1) := by rw [hanext]; linarith [p.deltaPos]
    have hr'D : p.actionTime (r + 1) ≤ ev.time + attemptBudget p G k := by
      rw [hanext, hbudget]; linarith [p.deltaPos]
    have hpr' := opening_phase_restrict E rho hp hur' hr'D
    have hqr' : q ≤ (r + 1) * p.R := hqr.trans (Nat.mul_le_mul_right _ (Nat.le_succ r))
    have hc' := common_opening_covered E rho hrec mono crossing writes rowCoverage hgst
      hQ heq hexact huq hqr' hpr'
    exact attempt_terminal_contradiction E rho hrec mono crossing writes hδ
      hbound rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hstop hp
      le_rfl hgst huq hqr' (hnext hpr') hc'
      (by rw [hanext, hbudget]; linarith [p.deltaPos])

end Rows
end AvailableChain.FGSA.Run
end
