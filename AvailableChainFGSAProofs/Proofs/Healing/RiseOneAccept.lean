module
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionPhase

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1236–1237, 1467–1468; S5 M5b B2.
DC: SAME an effective event at or before D excludes the stopped genesis phase.
The result retains M1's actual first rise and accepted carrier. -/
theorem healing_rise_one_of_effective (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hne : rho.honest.Nonempty)
    {i : Nat} {ev : V2.Event V (Obj p)} {D : Time}
    (hi : rho.events[i]? = some ev) (ht : ev.time ≤ D)
    (heff : EffectiveEvent p c E rho i) : RiseOneBy p c E rho D := by
  by_contra hstop
  have hcut := healing_phase_lt_timeIdx p c E rho hs hi ht
  exact boot_not_effective_one p c E rho hnr
    (healing_rise_one_frontier p c E rho hs hnr hne hstop hcut) heff

/-- Blueprint 21:1236–1237, 1467–1468; S5 M5b step 6.
DC: SAME an actual accepted certificate supplies the frontier witness for M1.
The strict receipt cut can be the finite horizon. -/
theorem healing_rise_one_of_receipt (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {x : V} {X : FGBlock (Fin p.n)} {d D : Time}
    (hx : x ∈ rho.honest) (hh : 2 ≤ (heightView p X).h)
    (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ nd.st.fg.TF) d x)
    (hd : d ≤ D) : RiseOneBy p c E rho D := by
  change X ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF at hheld
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
  exact healing_rise_one_of_frontier p c E rho hs ⟨x, hx⟩
    (hh.trans ((healing_phase_height_le p c E rho hheld).trans
      ((healing_phase_local_le_frontier p c E rho hx).trans
        (healing_frontier_mono p c E rho hnr (healing_phase_idx_le_time p c rho hd)))))

/-- Blueprint 21:1410–1419, 1467–1468; S5 M5b B2.
DC: SAME r3 supplies the first honest receipt. In the genesis top-J phase,
each honest receiver has an F path to genesis, so the same signed proposal
is stored strictly before its deadline by every honest receiver. -/
theorem healing_rise_one_receipt_all [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    {u : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hgst : E.t_GST ≤ u)
    (hp : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) 1
      (some .genesis) false) :
    ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x := by
  classical
  obtain ⟨y, hy, hfirst⟩ := healing_promotion_first_receipt E rho hrec crossing hnew hu hgst hp
  intro x hx
  by_cases hxy : x = y
  · exact hxy ▸ hfirst
  let t := SA.proposalTime p.toParams s
  let d := t + p.Δ
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ip, raw, sup, rows, hip, hem, _⟩ :=
    healing_promotion_proposal_read p c E rho hs hnew
  let jd := V2.D.Run.idxBefore rho d
  have hujd : V2.D.Run.idxBefore rho u ≤ jd :=
    healing_phase_idxBefore_mono p c rho (by dsimp only [d, t]; linarith [p.deltaPos])
  obtain ⟨hH, _, _⟩ := hp.2.2.2 jd x hujd
    (healing_phase_idx_le_time p c rho le_rfl) hx
  have hFgen := (healing_phase_frontier_root p c E rho crossing hx
    (storeBundle_stateBefore E rho jd x).cstore.fg.gen
    (show (heightView p .genesis).h = (R_at p c E rho jd x).H from hH.symm)).1
  have hcompat : Block.Compatible (eraseFG X)
      (eraseFG (V2.D.Run.stateBeforeTime E rho d x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
    exact Bool.or_eq_true_iff.mpr (Or.inr (eraseFG_preceq
      (KitFG.preceq_trans hFgen (KitFG.genesis_preceq X))))
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    cases he : o.payload <;> simp only [fgsaDelay_def, he, hrec.base.delta]
    exact (hn (by
      change (match o.payload with | .row _ => True | _ => False)
      rw [he]
      trivial)).elim
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ delay
  have hT : Gen.V2.Duty.Trigger E rho
      (ofWire p ⟨.proposer s, .proposal (eraseFG X) raw sup rows⟩) t :=
    Or.inl ⟨_, hnew.1.2, ip, hip, hem⟩
  have hdline : max t E.t_GST + p.Δ = d := by rw [max_eq_left (hgst.trans hu)]
  obtain ⟨Y, hY, he⟩ := fgsa_proposal_receipt E rho hrec.base.delta hrec.base.valid
    hrec.base.noRestart (fun t => max t E.t_GST + p.Δ) rho.horizon s (eraseFG X)
    raw sup rows t x hD hT hx (hdline ▸ hp.2.1)
    (hdline ▸ lt_add_of_pos_right t p.deltaPos) (hdline ▸ hcompat)
  have heq : Y = X := eraseFG_injective he
  rw [hdline, heq] at hY
  exact hY

/-- Blueprint 21:1410–1419, 1467–1468; S5 M5b B2.
DC: SAME the inclusive r3 event split covers an event at the receipt deadline.
An earlier rise also ends this item. Only the no-rise arm uses the genesis
phase through the strict receipt cut; no phase is asserted after a rise. -/
theorem healing_rise_one_accept [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    {u D : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hgst : E.t_GST ≤ u)
    (hd : SA.proposalTime p.toParams s + p.Δ ≤ D) (hD : D ≤ rho.horizon) :
    RiseOneBy p c E rho D ∨
      ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x := by
  classical
  have hs := hrec.base.valid.toScheduleWellFormed
  have hne : rho.honest.Nonempty := ⟨_, hnew.1.2⟩
  rcases healing_promotion_event_split p c E rho hs u D with
    ⟨i, ev, _, hi, heff, ht, _⟩ | _hquiet
  · exact Or.inl (healing_rise_one_of_effective p c E rho hs hrec.base.noRestart hne hi ht heff)
  by_cases hrise : RiseOneBy p c E rho D
  · exact Or.inl hrise
  have hcut : timeIdx rho (SA.proposalTime p.toParams s + p.Δ) ≤ timeIdx rho D := by
    change (rho.events.filter (fun e => decide (e.time ≤ _))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ D))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      ((of_decide_eq_true he).trans hd))
  have hp := boot_phase_one p c E rho
    (show u ≤ SA.proposalTime p.toParams s + p.Δ by linarith [p.deltaPos]) (hd.trans hD)
    (fun i _ hi => healing_rise_one_frontier p c E rho hs hrec.base.noRestart hne
      hrise (hi.trans hcut))
  exact Or.inr (healing_rise_one_receipt_all p c E rho hrec crossing hnew hu hgst hp)

end AvailableChain.FGSA.Run
end
