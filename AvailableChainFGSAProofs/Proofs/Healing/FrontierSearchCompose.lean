module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTop

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3.
The finite phase order charges gap and top J once, then contest repair and the tail.
The first rise and the first M+1 row retain their separate complete horizon guards. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- Blueprint 21:1722–1800; S5 F3, allowance geometry.
DC: SAME both frozen first labels exist. The one-lease window follows from the cut delay. -/
theorem frontierSearch_repair_start (E : Generic.Env V) (G : Time) {t ρbar : Time}
    (hdelay : recoveryStart p E + 2 * P p ≤ t)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) :
    FrontierRepairStart p E G (t + 3 * p.Δ) ρbar  := by
  have hsyncDelay : E.t_GST + 2 * P p ≤ t := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hsyncDelay : E.t_GST + 2 * P p ≤ t := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  let u := t + 3 * p.Δ
  have hΔ : 1 ≤ p.Δ := p.deltaPos
  rcases hmode with he | ⟨he, hk⟩
  · subst ρbar
    have hex : ∃ s, u < SA.proposalTime p.toParams s := by
      refine ⟨u.toNat + 1, ?_⟩
      change u < 4 * p.Δ * ((u.toNat + 1 : Nat) : Time)
      push_cast
      nlinarith [Int.self_le_toNat u, Int.natCast_nonneg u.toNat]
    exact .two (Nat.find hex) (Nat.find_spec hex) (fun b hb => Nat.find_min' hex hb)
  · subst ρbar
    have hex : ∃ b, u ≤ SA.voteTime p.toParams b := by
      refine ⟨u.toNat + 1, ?_⟩
      change u ≤ 4 * p.Δ * ((u.toNat + 1 : Nat) : Time) + p.Δ
      push_cast
      nlinarith [Int.self_le_toNat u, Int.natCast_nonneg u.toNat]
    let b := Nat.find hex
    have hb : u ≤ SA.voteTime p.toParams b := Nat.find_spec hex
    have hbi : (2 : Time) * p.R < b := by
      change u ≤ 4 * p.Δ * (b : Time) + p.Δ at hb
      change E.t_GST + 2 * (4 * (p.R : Time) * p.Δ) ≤ t at hsyncDelay
      dsimp only [u] at hb
      nlinarith [E.t_GST_nonneg]
    have hbn : 2 * p.R < b := by exact_mod_cast hbi
    have hwindow : p.k ≤ b + 1 := by omega
    have hshift : ((b + 1 - p.k : Nat) : Time) = (b : Time) + 1 - p.k := by
      rw [Nat.cast_sub hwindow]
      push_cast
      rfl
    have hki : (p.k : Time) ≤ 2 * p.R + 1 := by exact_mod_cast hk
    have hsync : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) := by
      change E.t_GST ≤ 4 * p.Δ * ((b + 1 - p.k : Nat) : Time) + p.Δ
      rw [hshift]
      change u ≤ 4 * p.Δ * (b : Time) + p.Δ at hb
      change E.t_GST + 2 * (4 * (p.R : Time) * p.Δ) ≤ t at hsyncDelay
      dsimp only [u] at hb
      nlinarith
    exact .one b hb (fun i hi => Nat.find_min' hex hi) hwindow hsync

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME an allowed repair charge is nonnegative under Recovery₂. -/
theorem frontierSearch_allowance_nonneg [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) : 0 ≤ ρbar := by
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  rcases hmode with he | ⟨he, _⟩
  · rw [he]
    change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
    have := (fgsa_gamma_bounds p G).1
    nlinarith [p.deltaPos, hrec.gapPos]
  · rw [he]
    change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
    have := (fgsa_gamma_bounds p G).1
    nlinarith [p.deltaPos, hrec.gapPos]

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME rebase a first rise through earlier same-frontier events. -/
theorem frontierSearch_rise_rebase (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho) {i j m : Nat} {D : Time} (hij : i ≤ j)
    (hf : frontierAtIdx p c E rho (j + 1) ≤ m) (hr : FrontierRiseBy p c E rho j m D) :
    FrontierRiseBy p c E rho i m D := by
  obtain ⟨k, ev, hjk, hk, ht, hh, hcap⟩ := (frontierRiseBy_iff p c E rho j m D).mp hr
  apply (frontierRiseBy_iff p c E rho i m D).mpr
  refine ⟨k, ev, by omega, hk, ht, hh, ?_⟩
  intro l hil hlk
  by_cases hlj : l ≤ j + 1
  · exact (healing_frontier_mono_all p c E rho mono hlj).trans hf
  · exact hcap l (by omega) hlk

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME the HG.3 rise stop supplies the first frontier rise, including equal times. -/
theorem frontierSearch_rise_of_stop (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {D : Time}
    (hf : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hr : FirstRiseStopBy p c E rho i m D) : FrontierRiseBy p c E rho i m D := by
  obtain ⟨j, ev, hij, hj, ht, _, hh, _⟩ := (firstRiseStopBy_iff p c E rho i m D).mp hr
  exact frontierSearch_first_rise p c E rho hs
    ⟨j, hij, healing_phase_lt_timeIdx p c E rho hs hj ht, hh⟩ hf

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME the unused phase charges remain available until the terminal tail. -/
def frontierSearch_remaining (p : Params) (G ΔF ρbar tail : Time) (kind : PhaseKind) : Time :=
  (if frontierSearch_phaseRank kind = 0 then E_gF p ΔF G ρbar else 0) +
    (if frontierSearch_phaseRank kind = 2 then 0 else E_jF p ΔF G ρbar) + (ρbar + 3 * p.Δ + tail)

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the arithmetic form without a pattern equation export. -/
theorem frontierSearch_remaining_eq (p : Params) (G ΔF ρbar tail : Time) (kind : PhaseKind) :
    frontierSearch_remaining p G ΔF ρbar tail kind =
      (if frontierSearch_phaseRank kind = 0 then E_gF p ΔF G ρbar else 0) +
        (if frontierSearch_phaseRank kind = 2 then 0 else E_jF p ΔF G ρbar) +
        (ρbar + 3 * p.Δ + tail) := by
  exact Eq.refl _

/-- Blueprint 21:1722–1800; S5 F3, finite phase composition.
DC: SAME gap and top-J cannot repeat. A saved seed leaves the supplied tail budget.
All repair labels and phase advances are proved from the standing inputs. -/
theorem frontierSearch_phase_tail [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho)
        (origin : RQCOrigin p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    (tail : Time) (htail : 0 ≤ tail)
    (hmode : ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hdelay : recoveryStart p E + 2 * P p ≤ ev.time)
    (hhor : ev.time + frontierSearch_remaining p G ΔF ρbar tail kind ≤ rho.horizon) :
    FrontierRiseBy p c E rho i m
      (ev.time + frontierSearch_remaining p G ΔF ρbar tail kind) ∨
    ∃ t, ev.time ≤ t ∧ t + tail ≤
      ev.time + frontierSearch_remaining p G ΔF ρbar tail kind ∧ StrongServed p c E rho m t := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hρ := frontierSearch_allowance_nonneg E rho hrec hmode
  have hP := frontierSearch_period_bound p
  have hΓ : 4 * p.Δ ≤ Γ p G := hrec.gapPos.trans (fgsa_gamma_bounds p G).1
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have heps := epsF_nonneg p ΔF hF
  have hg : 0 ≤ E_gF p ΔF G ρbar := by
    rw [E_gF_eq p ΔF G ρbar hbound]
    change 0 ≤ ρbar + 2 * P p + Γ p G - p.Δ
    linarith [p.deltaPos]
  have hj : 0 ≤ E_jF p ΔF G ρbar := by
    change 0 ≤ max _ _
    apply le_trans _ (le_max_right _ _)
    linarith [p.deltaPos]
  have go : ∀ n, ∀ {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind},
      2 - frontierSearch_phaseRank kind = n →
      FrontierSearchStart p c E rho i ev m kind → recoveryStart p E + 2 * P p ≤ ev.time →
      ev.time + frontierSearch_remaining p G ΔF ρbar tail kind ≤ rho.horizon →
      FrontierRiseBy p c E rho i m
        (ev.time + frontierSearch_remaining p G ΔF ρbar tail kind) ∨
      ∃ t, ev.time ≤ t ∧ t + tail ≤
        ev.time + frontierSearch_remaining p G ΔF ρbar tail kind ∧
        StrongServed p c E rho m t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i m ev kind hn hstart hdelay hhor
      have hfront := ((frontierSearchStart_iff p c E rho i ev m kind).mp hstart).2.2.2.1
      have mode := frontierSearch_repair_start E G hdelay hmode
      have hb : interruptedRepairBudget p G ΔF ρbar kind ≤
          frontierSearch_remaining p G ΔF ρbar tail kind := by
        cases kind <;> simp only [interruptedRepairBudget_gap, interruptedRepairBudget_topJ,
          interruptedRepairBudget_contest, frontierSearch_remaining_eq,
          frontierSearch_phaseRank_gap,
          frontierSearch_phaseRank_topJ, frontierSearch_phaseRank_contest, Nat.reduceEqDiff,
          ↓reduceIte] <;> linarith [p.deltaPos]
      have hbTail : interruptedRepairBudget p G ΔF ρbar kind + tail ≤
          frontierSearch_remaining p G ΔF ρbar tail kind := by
        cases kind <;> simp only [interruptedRepairBudget_gap, interruptedRepairBudget_topJ,
          interruptedRepairBudget_contest, frontierSearch_remaining_eq,
          frontierSearch_phaseRank_gap,
          frontierSearch_phaseRank_topJ, frontierSearch_phaseRank_contest, Nat.reduceEqDiff,
          ↓reduceIte] <;> linarith [p.deltaPos]
      have hpHor : ev.time + interruptedRepairBudget p G ΔF ρbar kind ≤ rho.horizon := by
        linarith only [hb, hhor]
      have result : FrontierHG3Result p c E rho i m ev.time
          (ev.time + interruptedRepairBudget p G ΔF ρbar kind) := by
        cases kind with
        | gap =>
          rw [interruptedRepairBudget_gap] at hpHor ⊢
          exact frontier_hg3_gap E rho hrec crossing mono repair common hδ hbound perm
            rowsReceipt progressCoverage hfold faultQ honestQuorum hstart mode hpHor
        | topJ =>
          rw [interruptedRepairBudget_topJ] at hpHor ⊢
          exact frontier_hg3_topJ E rho hrec crossing mono origin repair common
            hδ hbound
            perm rowsReceipt progressCoverage hfold faultQ honestQuorum hstart mode hpHor
        | contest =>
          rw [interruptedRepairBudget_contest] at hpHor ⊢
          exact frontier_hg3_contest E rho hrec crossing mono repair hstart mode hpHor
      rcases (frontierHG3Result_iff p c E rho i m ev.time _).mp result with
          hphase | hrise | ⟨t, hwt, ht, hserved⟩
      · obtain ⟨j, nextEv, nextKind, hij, ht, hnext, hrank⟩ :=
          frontierSearch_phase_step_of_crossing p c E rho crossing mono
            hs hstart hphase
        have htime : ev.time ≤ nextEv.time := by
          obtain ⟨hi, _⟩ := (frontierSearchStart_iff p c E rho i ev m kind).mp hstart
          obtain ⟨hjEv, _⟩ := (frontierSearchStart_iff p c E rho j nextEv m nextKind).mp hnext
          obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
          obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjEv
          have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
          rw [hie, hje] at hk
          exact V2.D.Engine.time_le_of_key_le _ _ hk
        have hcost : nextEv.time + frontierSearch_remaining p G ΔF ρbar tail nextKind ≤
            ev.time + frontierSearch_remaining p G ΔF ρbar tail kind := by
          cases kind <;> cases nextKind <;>
            simp only [frontierSearch_phaseRank_gap,
              frontierSearch_phaseRank_topJ, frontierSearch_phaseRank_contest] at hrank <;>
            try omega
          all_goals simp only [interruptedRepairBudget_gap, interruptedRepairBudget_topJ] at ht
          all_goals simp only [frontierSearch_remaining_eq, frontierSearch_phaseRank_gap,
          frontierSearch_phaseRank_topJ, frontierSearch_phaseRank_contest,
            Nat.reduceEqDiff, ↓reduceIte]
          all_goals linarith only [ht, hj]
        have hmeasure : 2 - frontierSearch_phaseRank nextKind < n := by
          rw [← hn]
          cases kind <;> cases nextKind <;> simp only [frontierSearch_phaseRank_gap,
            frontierSearch_phaseRank_topJ, frontierSearch_phaseRank_contest] at * <;> omega
        rcases ih _ hmeasure rfl hnext (hdelay.trans htime) (hcost.trans hhor) with
            hr | ⟨t, hnt, ht, hserved⟩
        · left
          have hf := ((frontierSearchStart_iff p c E rho j nextEv m nextKind).mp hnext).2.2.2.1
          exact frontierSearch_rise_mono p c E rho hcost
            (frontierSearch_rise_rebase E rho mono hij.le hf.le hr)
        · exact Or.inr ⟨t, htime.trans hnt, ht.trans hcost, hserved⟩
      · left
        exact frontierSearch_rise_mono p c E rho (by linarith only [hb])
          (frontierSearch_rise_of_stop E rho hs hfront.le hrise)
      · exact Or.inr ⟨t, hwt, by linarith only [ht, hbTail], hserved⟩
  exact go _ rfl hstart hdelay hhor

end AvailableChain.FGSA.Run
end
