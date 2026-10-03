module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTail -- shake: keep (HG.4 closed-horizon row test)

set_option linter.privateModule false

/-! HG.3--HG.5 interface and support tests. The terminal-window example
refutes an arithmetic implication, not a valid execution or HG.4 itself.
Full search tests remain stopped with the principal search producers. -/

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

-- Delta=1, R=2, q=11, r=6, beta=8, entry slot=11, G=7, Gamma=4.
-- U_F=56, terminal deadline=61, but the full G-window ends at 63.
theorem terminal_window_guard_not_implied :
    ¬ (∀ U G gamma horizon : Int, 4 ≤ G → gamma = 4 * (G / 4) →
      U + gamma + 1 ≤ horizon → U + G ≤ horizon) := by
  intro h
  have hbad := h 56 7 4 61 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad


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
    (hhor : t + (P p - 4 * p.Δ) = rho.horizon) :
    FirstHeightRowBy p c E rho 1 rho.horizon := by
  simpa only [hhor] using
    healing_frontierTail_row E rho hrec mono crossing cap writes rowCoverage hserved hhor.le

#check InterruptedRepairStatement
#check FrontierTailStatement
#check FrontierSearchStatement
#check healing_frontierTail_row
#print axioms terminal_window_guard_not_implied

end AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
end
