module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainGeneric.Proofs.V2.Duty.Sleep

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Proposal processing is durable, including history before a receiver restart. -/
theorem fgsa_historySafeAt_of_proposal (x : V) (o : Obj p) (a : Time)
    {s : Slot} {N : NamedProposal p.n} (hd : (toWire p o).decode = some (.block s N)) :
    Gen.V2.Duty.HistorySafeAt E rho x o a := by
  rintro ⟨k, hk, hp⟩
  change processedS p (V2.D.Run.stateBefore E rho k x).st o = true at hp
  dsimp only [processedS] at hp
  rw [hd, decide_eq_true_eq] at hp
  obtain ⟨Y, hY, hroot⟩ := hp
  change processedS p (V2.D.Run.stateBefore E rho (V2.D.Run.actionCut rho a) x).st o = true
  dsimp only [processedS]
  rw [hd, decide_eq_true_eq]
  exact ⟨Y, (fgsa_store_durable p c E rho hk x).1 hY, hroot⟩

private theorem proposal_direct (st : State p.n) (parent o : Obj p)
    {s : Slot} {N : NamedProposal p.n} (hd : (toWire p o).decode = some (.block s N))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r M =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofHead] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofRow] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd

/-- A source proposal acceptance supplies nonnegative send time and well-formedness. -/
theorem fgsa_proposal_acceptance_facts (hV : V2.D.ExecutionValid E rho)
    {k : Nat} {v : V} {o : Obj p} {t : Time} {s : Slot} {N : NamedProposal p.n}
    (hd : (toWire p o).decode = some (.block s N))
    (hacc : V2.D.Run.acceptsAt E rho k v o t) :
    0 ≤ t ∧ (fgsa p c).wellFormed o = true := by
  obtain ⟨parent, he, hh⟩ := hacc.1
  have hp := proposal_direct _ parent o hd hh
  subst parent
  exact ⟨(hV.in_horizon _ (List.mem_of_getElem? he)).1, hV.wire k v o t he⟩

/-- A public awake anchor after the original acceptance supplies proposal handlers.
The source acceptance stays at its original time. The receiver uses its own epoch. -/
theorem fgsa_proposal_handlers_at_anchor (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) {x v : V} {o : Obj p} {k : Nat} {t a d : Time}
    {s : Slot} {N : NamedProposal p.n} (hx : x ∈ rho.honest)
    (hd : (toWire p o).decode = some (.block s N))
    (hacc : V2.D.Run.acceptsAt E rho k v o t) (hta : t ≤ a)
    (ha : 0 ≤ a) (hpub : V2.PublicTime E a) (hawake : E.awake x a = true)
    (had : a < d) (hhor : d ≤ rho.horizon)
    (hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho d)) :
    ∀ j u, a ≤ u → u < d → V2.D.Run.handlesAt E rho j x o u →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o := by
  have hS := hV.toScheduleWellFormed
  have hact := timely_of_relay_retained E rho (fgsaTimelyClock p c) (fgsaAdmitSound p c)
    hS (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
    (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
      fgsa_admissionTime_public p E hDelta obj) v k o t hacc
  have hacta := hact.trans ((Gen.V2.Duty.pubFloor_le E t).trans hta)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
    (hV.tick_total x hx a hpub ha (had.le.trans hhor) hawake)
  have hai : V2.D.Run.actionCut rho a ≤ i := by
    apply Nat.le_of_not_gt
    intro hn
    have ht := (V2.D.Engine.index_lt_actionCut_iff hS hi a).mp hn
    rcases ht with ht | ⟨_, hp⟩
    · exact (lt_irrefl a ht).elim
    · change (1 : Nat) = 0 at hp
      cases hp
  intro j u hau hud hh
  obtain ⟨parent, he, hp⟩ := hh
  have hparent := proposal_direct _ parent o hd hp
  subst parent
  refine ⟨hV.wire j x o u he, hV.deps j x o u he, ?_⟩
  exact Gen.V2.Duty.timely_of_clock E rho (fgsaTimelyClock p c) hS x o a i j hacta hi
    (V2.D.Engine.tick_index_lt_delivery E rho hS hi he hau)
    (hRF.mono hai ((Gen.V2.Duty.index_lt_idxBefore_iff hS he d).mpr hud).le)

/-- An enabled honest gate is awake from its label start through the gate. -/
theorem fgsa_enabledGate_awakeClosed (hV : V2.D.ExecutionValid E rho)
    {j : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho j x s) :
    AwakeClosed E x (slotStartZ p (s : Int)) (SA.gateTime p.toParams s) := by
  intro t ht0 hst htg
  have hA := hV.tick_awake x _ (List.mem_of_getElem? hG.1)
  cases ha : E.awake x t with
  | true => rfl
  | false =>
    obtain ⟨w, htw, hwg, hW⟩ := V2.D.Engine.wake_between htg ha hA
    have hw0 : 0 < w := lt_of_le_of_lt ht0 htw
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (hV.wake_restart x hx w hw0
      (hwg.trans (hV.in_horizon _ (List.mem_of_getElem? hG.1)).2) hW)
    have hkj := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hk hG.1 hwg
      (by change (0 : Nat) < 1; omega)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hV.toScheduleWellFormed hk hkj
    change (storeAt p c E rho j x).restartTime = some u at hu
    have hb := hG.2
    change (match (storeAt p c E rho j x).restartTime with
      | none => True | some w => w ≤ slotStartZ p (s : Int)) at hb
    rw [hu] at hb
    exact (not_lt_of_ge (hwu.trans hb) (hst.trans_lt htw)).elim

/-- An enabled gate has a local service epoch through each earlier strict read. -/
theorem fgsa_enabledGate_anchor_epoch (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {j : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho j x s)
    {a d : Time} (ha : slotStartZ p (s : Int) ≤ a) (had : a < d)
    (hd : d ≤ SA.gateTime p.toParams s) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho d) := by
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hV.toScheduleWellFormed had
  intro k t ht hat htd
  have hsw : slotStartZ p (s : Int) < t := ha.trans_lt hat
  have h0 : 0 ≤ slotStartZ p (s : Int) := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hw := (hR x t (List.mem_of_getElem? ht)).2.2
  have haw := fgsa_enabledGate_awakeClosed hV hx hG (t - 1)
    (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
    (by dsimp [Time] at *; omega)
  rw [haw] at hw
  cases hw

/-- Gate-path proposals use voteTime as anchor and earlyTime as deadline.
The exact enabled receiver guard supplies readiness and the receiver epoch. -/
theorem fgsa_gate_path_anchor_service (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) (hR : V2.D.RestartsAtWakes E rho)
    {j k : Nat} {x v : V} {s r : Slot} {o : Obj p} {N : NamedProposal p.n} {t : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hG : enabledGateAt p c E rho j x s)
    (hd : (toWire p o).decode = some (.block r N))
    (hacc : V2.D.Run.acceptsAt E rho k v o t) (ht : t < SA.voteTime p.toParams s) :
    Gen.V2.Duty.ReadyTrigger E rho o t x (SA.voteTime p.toParams s)
      (SA.earlyTime p.toParams s) ∧
    Gen.V2.Duty.HistorySafeAt E rho x o (SA.voteTime p.toParams s) ∧
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) ∧
    (∀ i u, SA.voteTime p.toParams s ≤ u → u < SA.earlyTime p.toParams s →
      V2.D.Run.handlesAt E rho i x o u →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho i x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho i x) o) := by
  have hpos := p.deltaPos
  have h0 : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  have hs : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    dsimp [Time] at *
    omega
  have hve : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
    dsimp [Time] at *
    omega
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    dsimp [Time] at *
    omega
  have hAw := fgsa_enabledGate_awakeClosed hV hx hG
  have hRF := fgsa_enabledGate_anchor_epoch hV hR hx hG hs hve heg
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  refine ⟨⟨v, hv, Or.inr ⟨k, hacc⟩, ?_⟩, fgsa_historySafeAt_of_proposal x o _ hd,
    hRF, fgsa_proposal_handlers_at_anchor hV hDelta hx hd hacc ht.le h0 hpub
      (hAw _ h0 hs (hve.le.trans heg)) hve
      (heg.trans (hV.in_horizon _ (List.mem_of_getElem? hG.1)).2) hRF⟩
  intro u hvu hue
  exact hAw u (h0.trans hvu) (hs.trans hvu) (hue.le.trans heg)

/-- Transfer proposals use earlyTime as anchor and freezeTime as deadline.
Joinedness at the next vote also supplies the epoch to that consuming vote. -/
theorem fgsa_transfer_path_anchor_service (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) {k : Nat} {y v : V} {s r : Slot}
    {o : Obj p} {N : NamedProposal p.n} {t : Time}
    (hy : y ∈ rho.honest) (hv : v ∈ rho.honest)
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hhor : SA.voteTime p.toParams (s + 1) ≤ rho.horizon)
    (hd : (toWire p o).decode = some (.block r N))
    (hacc : V2.D.Run.acceptsAt E rho k v o t) (ht : t < SA.earlyTime p.toParams s) :
    Gen.V2.Duty.ReadyTrigger E rho o t y (SA.earlyTime p.toParams s)
      (SA.freezeTime p.toParams s) ∧
    Gen.V2.Duty.HistorySafeAt E rho y o (SA.earlyTime p.toParams s) ∧
    V2.D.restartFree rho y (V2.D.Run.actionCut rho (SA.earlyTime p.toParams s))
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) ∧
    (∀ i u, SA.earlyTime p.toParams s ≤ u → u < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho i y o u →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho i y) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho i y) o) := by
  have hpos := p.deltaPos
  have h0 : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  have hs : slotStartZ p (((s + 1 : Nat) : Int) - 1) ≤ SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    push_cast
    ring_nf
    dsimp [Time] at *
    omega
  have hef : SA.earlyTime p.toParams s < SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 3 * p.Δ
    dsimp [Time] at *
    omega
  have hfv : SA.freezeTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith
  have hRF : V2.D.restartFree rho y
      (V2.D.Run.actionCut rho (SA.earlyTime p.toParams s))
      (V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1))) := by
    apply Gen.V2.Duty.restartFree_actionCut_idxBefore hV.toScheduleWellFormed (hef.trans hfv)
    intro i u he hau huv
    have hu0 := h0.trans hau.le
    exact (not_lt_of_ge (hJ.2.2 u hu0 huv.le (List.mem_of_getElem? he))
      (hs.trans_lt hau)).elim
  have hRFf := hRF.mono le_rfl (fgsa_idxBefore_mono rho hfv.le)
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
    push_cast
    ring
  refine ⟨⟨v, hv, Or.inr ⟨k, hacc⟩, ?_⟩, fgsa_historySafeAt_of_proposal y o _ hd,
    hRF, fgsa_proposal_handlers_at_anchor hV hDelta hy hd hacc ht.le h0 hpub
      (fgsa_awake_of_joinedAt E rho y (s + 1) _ _ hJ h0 hs (hef.trans hfv).le)
      hef (hfv.le.trans hhor) hRFf⟩
  intro u heu huf
  exact fgsa_awake_of_joinedAt E rho y (s + 1) _ _ hJ (h0.trans heu) (hs.trans heu)
    (huf.le.trans hfv.le)

end AvailableChain.FGSA.Run
end
