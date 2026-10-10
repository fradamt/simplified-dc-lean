module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

variable (mono : RMonoAll p c E rho)

variable (readyCut : ∀ t, recoveryStart p E ≤ t →
  E.t_GST ≤ slotStartZ p (((slotAt p t : Slot) : Int) - 1))

variable (heldServices : ∀ i (ev : V2.Event V (Obj p)) m,
  rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
  frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
  PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))

include mono readyCut heldServices

/-! H-ATTEMPT-2 CUT. These lemmas supply settlement for each budget row.
They retain the RXing input of H.8. They do not assert a complete row bound.
The AttemptValid start disjunction is not used, so its inclusive-cut arm
needs no effective event and no new settlement premise. -/

/-- ROOT-DIGEST W2b. H.8 settlement for either frozen AttemptValid start arm. -/
theorem healing_attempt_settle_start
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) := by
  obtain ⟨ev0, hi0, hgst, _hstart, hfront, hm, hkind, _⟩ := hvalid
  have he : ev0 = ev := Option.some.inj (hi0.symm.trans hstart)
  subst ev0
  obtain ⟨J, hsettled⟩ := healing_settle_start_on
    (hroots := hrec.base.receiptIdealization) p c E rho crossing hrec.base.valid
    mono hrec readyCut heldServices
    k.start ev v k.frontier k.phase hstart hgst
    hu hv hm hfront.symm hkind hquiet
  dsimp only [fgsa] at hsettled ⊢
  refine ⟨J, ?_⟩
  cases hphase : k.phase <;> simpa only [hphase] using hsettled

/-- Settlement for the raise / contest row, including the cut start. -/
theorem healing_attempt_raise_contest_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .raise) (_hphase : k.phase = .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) :=
  healing_attempt_settle_start p c E rho mono readyCut heldServices crossing hrec
    hvalid hstart hu hv hquiet

/-- Settlement for the raise / other row, including the cut start. -/
theorem healing_attempt_raise_other_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .raise) (_hphase : k.phase ≠ .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) :=
  healing_attempt_settle_start p c E rho mono readyCut heldServices crossing hrec
    hvalid hstart hu hv hquiet

/-- Settlement for the firstRow / contest row, including the cut start. -/
theorem healing_attempt_firstRow_contest_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .firstRow) (_hphase : k.phase = .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) :=
  healing_attempt_settle_start p c E rho mono readyCut heldServices crossing hrec
    hvalid hstart hu hv hquiet

/-- Settlement for the firstRow / other row, including the cut start. -/
theorem healing_attempt_firstRow_other_settle
    (crossing : RXing p c E rho) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {k : AttemptKey}
    {ev : V2.Event V (Obj p)} {v : Time}
    (hvalid : AttemptValid p c E rho k) (hstart : rho.events[k.start]? = some ev)
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, k.start < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j)
    (_htask : k.task = .firstRow) (_hphase : k.phase ≠ .contest) :
    ∃ J,
      let root := match k.phase with | .gap => none | .topJ => some J | .contest => none
      let contested := match k.phase with | .gap => false | .topJ => false | .contest => true
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v k.frontier root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st k.frontier root contested) :=
  healing_attempt_settle_start p c E rho mono readyCut heldServices crossing hrec
    hvalid hstart hu hv hquiet

end AvailableChain.FGSA.Run
end
