module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTail -- shake: keep (example uses)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTop -- shake: keep (example uses)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchBudget -- shake: keep (example uses)

set_option linter.privateModule false

/-! HG.3 phase applications, finite interrupts, phase-order progress,
HG.4 exact-height row service, and aligned terminal-horizon STOP tests.
HG.4 rise and HG.5 full applications remain stopped at the terminal interface. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
example (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .gap = E_gF p ΔF G ρbar :=
  interruptedRepairBudget_gap p G ΔF ρbar

omit [DecidableEq V] in
example (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .topJ = E_jF p ΔF G ρbar :=
  interruptedRepairBudget_topJ p G ΔF ρbar

omit [DecidableEq V] in
example (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .contest = ρbar + 3 * p.Δ :=
  interruptedRepairBudget_contest p G ΔF ρbar

-- Height one retains the full frozen seed before projection.
example {t : Time} (h : StrongServed p c E rho 1 t) : ServedFrontier p c E rho 1 t :=
  h.toServedFrontier

-- An actual interrupt at the closed horizon forces the first-event arm.
example (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {ev : V2.Event V (Obj p)}
    (hij : i < j) (hj : rho.events[j]? = some ev) (ht : ev.time = rho.horizon)
    (heff : EffectiveEvent p c E rho j) : FirstEffectiveBy p c E rho i rho.horizon := by
  rcases frontierSearch_first_effective_split p c E rho hs i rho.horizon with h | hquiet
  · exact h
  · exact (hquiet j hij (healing_phase_lt_timeIdx p c E rho hs hj ht.le) heff).elim

-- An ordinary attempt stops at this event; frontier-only service can continue.
example {j : Nat} (heff : EffectiveEvent p c E rho j)
    (hsame : frontierAtIdx p c E rho j = frontierAtIdx p c E rho (j + 1)) :
    EffectiveEvent p c E rho j ∧
      ¬ frontierAtIdx p c E rho j < frontierAtIdx p c E rho (j + 1) := by
  exact ⟨heff, by rw [hsame]; exact lt_irrefl _⟩

-- A skip past M+1 retains its earlier honest M+1 row and event index.
example (cap : RCap p c E rho) {M i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hW : HeldAt p c E rho i x W) (hh : M + 2 ≤ (heightView p W).h) :
    ∃ j z r a e, j < i ∧ HonestRowAt p c E rho j z r a ∧
      namedEntry a.payload.height_pair = some (M + 1, e) :=
  frontierSearch_skipped_row p c E rho cap hW hh

-- Two completed allowance routes cannot select different first row rounds.
example {M r2 r1 : Nat} (h2 : HeightRow p c E rho r2 (M + 1))
    (hf2 : ∀ r, HeightRow p c E rho r (M + 1) → r2 ≤ r)
    (h1 : HeightRow p c E rho r1 (M + 1))
    (hf1 : ∀ r, HeightRow p c E rho r (M + 1) → r1 ≤ r) : r2 = r1 :=
  frontierSearch_first_row_unique p c E rho h2 hf2 h1 hf1

-- A row exactly at the closed horizon suffices for the least-row construction.
example {m r : Nat} (hr : HeightRow p c E rho r m)
    (ht : p.actionTime r = rho.horizon) : FirstHeightRowBy p c E rho m rho.horizon :=
  frontierSearch_first_row p c E rho hr ht.le

-- At m=1, HG.4 row service applies when the complete tail ends at the horizon.
example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {t : Time} (hserved : StrongServed p c E rho 1 t)
    (hhor : t + (P p - 4 * p.Δ) = rho.horizon)
    (hsame : ∃ j ev, rho.events[j]? = some ev ∧ t ≤ ev.time ∧
      ev.time ≤ rho.horizon ∧ EffectiveEvent p c E rho j ∧
      frontierAtIdx p c E rho j = frontierAtIdx p c E rho (j + 1)) :
    FirstHeightRowBy p c E rho 1 rho.horizon ∧
      ∃ j ev, rho.events[j]? = some ev ∧ t ≤ ev.time ∧
        ev.time ≤ rho.horizon ∧ EffectiveEvent p c E rho j ∧
        frontierAtIdx p c E rho j = frontierAtIdx p c E rho (j + 1) := by
  refine ⟨?_, hsame⟩
  simpa only [hhor] using
    healing_frontierTail_row E rho hrec mono crossing cap writes rowCoverage hserved hhor.le

-- Same-frontier stops advance the phase under the actual phase-order producer.
example (mono : RMono p c E rho) (hnr : V2.D.NoRestart rho)
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {kind : PhaseKind}
    {ev : V2.Event V (Obj p)} {deadline : Time}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hstop : FirstPhaseStopBy p c E rho i m deadline) :
    ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
      FrontierSearchStart p c E rho j nextEv m nextKind ∧
      frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind :=
  frontierSearch_phase_step p c E rho mono hnr hs hstart hstop

section PhaseApplications
variable [Fintype V] {G ΔF ρbar : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (crossing : RXing p c E rho)
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

-- Apply each phase lemma at the closed horizon, including height one.
example {i : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev 1 .gap)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_gF p ΔF G ρbar = rho.horizon) :
    FrontierHG3Result p c E rho i 1 ev.time rho.horizon := by
  simpa only [hhor] using frontier_hg3_gap E rho hrec crossing repair common hδ hbound perm
    rowsReceipt progressCoverage hfold faultQ honestQuorum hstart mode hhor.le

example (origin : RQCOrigin p c E rho) {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .topJ)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_jF p ΔF G ρbar = rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time rho.horizon := by
  simpa only [hhor] using frontier_hg3_topJ E rho hrec crossing origin repair common
    hδ hbound perm rowsReceipt progressCoverage hfold faultQ honestQuorum hstart mode hhor.le

example {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .contest)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + (ρbar + 3 * p.Δ) = rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time rho.horizon := by
  simpa only [hhor] using frontier_hg3_contest E rho hrec crossing repair hstart mode hhor.le

-- The two-sided top-J bound remains intact.
example (hF : 0 ≤ ΔF) : E_j p G ρbar ≤ E_jF p ΔF G ρbar ∧
    E_jF p ΔF G ρbar ≤ E_j p G ρbar + epsF p ΔF := E_jF_bounds p ΔF G ρbar hF
end PhaseApplications

example [Fintype V] {ΔF : Time} (hrec : Recovery₂ p c E rho (8 * p.Δ) ΔF) :
    Γ p (8 * p.Δ) = 8 * p.Δ := hrec.gamma_eq

example [Fintype V] {ΔF : Time} (hrec : Recovery₂ p c E rho (12 * p.Δ) ΔF) :
    Γ p (12 * p.Δ) = 12 * p.Δ := hrec.gamma_eq

example : ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
    d + (2 * 8 + 8 - 9) ≤ horizon → a + 2 * 8 + 8 - 9 ≤ horizon) :=
  frontierSearch_terminal_horizon_gap8

example : ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
    d + (2 * 8 + 12 - 9) ≤ horizon → a + 2 * 8 + 12 - 9 ≤ horizon) :=
  frontierSearch_terminal_horizon_gap12

#check InterruptedRepairStatement
#check FrontierTailStatement
#check FrontierSearchStatement
#check healing_frontierTail_row
#print axioms frontier_hg3_gap
#print axioms frontier_hg3_topJ
#print axioms frontier_hg3_contest
#print axioms frontierSearch_phase_step
#print axioms healing_frontierTail_row
#print axioms frontierSearch_terminal_horizon_gap8
#print axioms frontierSearch_terminal_horizon_gap12

end AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
end
