module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSeed
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

/-! Blueprint 21 HG.3--HG.5 and H.11; frontier plan §3.3.
These are run-local conclusion contracts. Producers must use the standing
Recovery₂, RMono, RXing, RCap, RQCOrigin and exact INLINE facts.
No contract below assumes a weak-to-strong served reconstruction.
The two search tasks in H.11 are sequential: rise from M, then row at M+1. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21 HG.1:1500--1583; plan §3.3, saved-witness gap 7.
DC: SAME all frozen seed premises, including both first-label proofs.
The cap is at the current endpoint. A later endpoint needs its own cap. -/
def StrongServed (m : Nat) (t : Time) : Prop :=
  ∃ u J contested q Q Qfg,
    E.t_GST ≤ u ∧ HonestProposal E rho (fgsaInterface p c) q Q ∧
    eraseFG Qfg = Q ∧ (heightView p Qfg).h = m ∧ ExactService p c E rho q Q ∧
    FrontierSeedQualification p E u q ∧ u ≤ SA.proposalTime p.toParams q ∧
    PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested ∧
    SA.gateTime p.toParams q ≤ t ∧ t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)

/-- Blueprint 21 HG.1; plan §3.3. DC: SAME the complete internal witness interface. -/
theorem strongServed_iff (m : Nat) (t : Time) : StrongServed p c E rho m t ↔
  ∃ u J contested q Q Qfg,
    E.t_GST ≤ u ∧ HonestProposal E rho (fgsaInterface p c) q Q ∧
    eraseFG Qfg = Q ∧ (heightView p Qfg).h = m ∧ ExactService p c E rho q Q ∧
    FrontierSeedQualification p E u q ∧ u ≤ SA.proposalTime p.toParams q ∧
    PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested ∧
    SA.gateTime p.toParams q ≤ t ∧ t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m) := Iff.rfl

/-- Blueprint 21 HG.1; plan §3.3.
DC: SAME only the strong-to-weak projection is available. -/
theorem StrongServed.toServedFrontier {m : Nat} {t : Time}
    (h : StrongServed p c E rho m t) : ServedFrontier p c E rho m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, _, hp, he, hh, hs, _, _, _, hg, _, _⟩ := h
  exact ⟨q, Q, Qfg, hp, he, hh, hg, hs⟩

/-- Blueprint 21 H.10:1426--1499 and H.11:1744--1800.
DC: SAME an event start or the actual inclusive cut, without a served flag. -/
def FrontierSearchStart (i : Nat) (ev : V2.Event V (Obj p)) (m : Nat)
    (kind : PhaseKind) : Prop :=
  rho.events[i]? = some ev ∧ E.t_GST ≤ ev.time ∧
  (EffectiveEvent p c E rho i ∨
    ∃ rG, E.t_GST ≤ p.actionTime rG ∧
      (∀ r, E.t_GST ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧ timeIdx rho ev.time = i + 1) ∧
  frontierAtIdx p c E rho (i + 1) = m ∧ 1 ≤ m ∧
  AttemptPhaseAt p c E rho (i + 1) m kind

/-- Blueprint 21 HG.3:1639--1696, H.6/H.6-S.
DC: SAME the one-lease arm retains its synchronous first-HEAD window. -/
def FrontierRepairAllowance (G ρbar u : Time) : Prop :=
  ρbar = ρΓ p G ∨
    (ρbar = ρ₁ p G ∧ ∃ b : Slot,
      u ≤ SA.voteTime p.toParams b ∧
      (∀ s, u ≤ SA.voteTime p.toParams s → b ≤ s) ∧
      p.k ≤ b + 1 ∧ E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k))

/-- Blueprint 21 HG.3; plan §3.3 deadline interface.
DC: SAME use the frozen maxima; do not replace their definitions. -/
def interruptedRepairBudget (G ΔF ρbar : Time) (kind : PhaseKind) : Time :=
  match kind with
  | .gap => E_gF p ΔF G ρbar
  | .topJ => E_jF p ΔF G ρbar
  | .contest => ρbar + 3 * p.Δ

omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME gap deadline. -/
theorem interruptedRepairBudget_gap (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .gap = E_gF p ΔF G ρbar := by rfl

omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME top-J deadline, including epsF. -/
theorem interruptedRepairBudget_topJ (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .topJ = E_jF p ΔF G ρbar := by rfl

omit [DecidableEq V] in
/-- Blueprint 21 HG.3. DC: SAME contest deadline. -/
theorem interruptedRepairBudget_contest (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .contest = ρbar + 3 * p.Δ := by rfl

/-- Blueprint 21 H.10; plan gap 6.
DC: SAME the first actual effective event strictly after the start index. -/
def FirstEffectiveBy (i : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k)

/-- Blueprint 21 H.10; plan gap 6. DC: SAME actual first-event interface. -/
theorem firstEffectiveBy_iff (i : Nat) (deadline : Time) :
    FirstEffectiveBy p c E rho i deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent p c E rho j ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent p c E rho k) := Iff.rfl

/-- Blueprint 21 HG.1 and HG.4; plan §4.
DC: SAME a first frontier rise. Same-frontier events are permitted before it. -/
def FrontierRiseBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    m < frontierAtIdx p c E rho (j + 1) ∧
    (∀ k, i + 1 ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ m)

/-- Blueprint 21 HG.1/HG.4. DC: SAME first-rise interface. -/
theorem frontierRiseBy_iff (i m : Nat) (deadline : Time) :
    FrontierRiseBy p c E rho i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    m < frontierAtIdx p c E rho (j + 1) ∧
    (∀ k, i + 1 ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ m) := Iff.rfl

/-- Blueprint 21 HG.4--HG.5 and H.11.
DC: SAME actual first honest row, including an earlier SO-COV emission. -/
def FirstHeightRowBy (m : Nat) (deadline : Time) : Prop :=
  ∃ r, HeightRow p c E rho r m ∧
    (∀ r', HeightRow p c E rho r' m → r ≤ r') ∧ p.actionTime r ≤ deadline

/-- Blueprint 21 HG.4/H.11. DC: SAME first-row interface. -/
theorem firstHeightRowBy_iff (m : Nat) (deadline : Time) :
    FirstHeightRowBy p c E rho m deadline ↔
  ∃ r, HeightRow p c E rho r m ∧
    (∀ r', HeightRow p c E rho r' m → r ≤ r') ∧ p.actionTime r ≤ deadline := Iff.rfl

/-- Blueprint 21 HG.3; plan §3.3.
DC: SAME generic event start, full phase deadline and complete horizon guard. -/
def InterruptedRepairStatement (G ΔF ρbar : Time) : Prop :=
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ i ev m kind, FrontierSearchStart p c E rho i ev m kind →
    FrontierRepairAllowance p E G ρbar (ev.time + 3 * p.Δ) →
    ev.time + interruptedRepairBudget p G ΔF ρbar kind ≤ rho.horizon →
    FirstEffectiveBy p c E rho i
      (ev.time + interruptedRepairBudget p G ΔF ρbar kind) ∨
    FrontierRiseBy p c E rho i m
      (ev.time + interruptedRepairBudget p G ΔF ρbar kind) ∨
    (∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget p G ΔF ρbar kind ∧
      StrongServed p c E rho m t)

/-- Blueprint 21 HG.4; plan §3.3.
DC: SAME two independently guarded tasks from the current served start.
There is no no-effective-event premise and no second repair allowance. -/
def FrontierTailStatement (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ i ev m kind, FrontierSearchStart p c E rho i ev m kind →
    StrongServed p c E rho m ev.time →
    (ev.time + (2 * P p + Γ p G - 9 * p.Δ) ≤ rho.horizon →
      FrontierRiseBy p c E rho i m (ev.time + (2 * P p + Γ p G - 9 * p.Δ))) ∧
    (ev.time + (P p - 4 * p.Δ) ≤ rho.horizon →
      FirstHeightRowBy p c E rho m (ev.time + (P p - 4 * p.Δ)))

/-- Blueprint 21 HG.5; plan §3.3.
DC: SAME one-frontier rise task, before the H.11 second task. -/
def frontierSearchRiseBudget (G ΔF ρbar : Time) : Time :=
  E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar

/-- Blueprint 21 HG.5; plan §3.3.
DC: SAME one-frontier first-row task. -/
def frontierSearchRowBudget (G ΔF ρbar : Time) : Time :=
  E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar

/-- Blueprint 21 HG.5/H.11; plan §3.3.
DC: SAME inline cut/frontier/row cap. The second task is at M+1.
One rStar is quantified before both allowances, with each full horizon guard.
The first task also has its own independent rise horizon guard.
No reset witness, phase package, or downstream healing service is assumed. -/
def FrontierSearchStatement (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R → LivenessBoundW p ΔF →
  ∀ rG u₀ M, E.t_GST ≤ p.actionTime rG →
    (∀ r, E.t_GST ≤ p.actionTime r → rG ≤ r) → u₀ = p.actionTime (rG + 2) →
    E.t_GST + 2 * P p ≤ u₀ → M = honestFrontier p c E rho u₀ →
    (∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ M) →
    (∀ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
      u₀ + frontierSearchRiseBudget p G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
        M < frontierAtIdx p c E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M)) ∧
    ((∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      u₀ + frontierSearchRiseBudget p G ΔF ρbar +
        frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon) →
    ∃ rStar, HeightRow p c E rho rStar (M + 1) ∧
      (∀ r, HeightRow p c E rho r (M + 1) → rStar ≤ r) ∧
      ∀ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) →
        u₀ + frontierSearchRiseBudget p G ΔF ρbar +
          frontierSearchRowBudget p G ΔF ρbar ≤ rho.horizon →
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget p G ΔF ρbar ∧
          M < frontierAtIdx p c E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx p c E rho k ≤ M) ∧
          p.actionTime rStar ≤ ev.time + frontierSearchRowBudget p G ΔF ρbar)

end AvailableChain.FGSA.Run
end
