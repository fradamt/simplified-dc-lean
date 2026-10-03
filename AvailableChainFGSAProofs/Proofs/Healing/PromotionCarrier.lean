module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGSAProofs.Proofs.Shared.Channels

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The proposal read retains the emitted wire, its rows and its exact parent. -/
private theorem promotion_proposal_read (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {b : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s b) :
    ∃ j raw sup rows, rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
        V2.D.Run.emitsAt E rho j ∧
      let st := ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)).st
      proposalStateAt p c E rho s = some st ∧ st.slot p = s ∧
        b = .node (proposerHead p st s) s (packBody (c.app (rho.input
          (V2.D.proposerOf rho (fgsaInterface p c) s) (SA.proposalTime p.toParams s)))
          (proposalRows p st (proposerHead p st s))) ∧
        rows = proposalRows p st (proposerHead p st s) := by
  obtain ⟨hslot, o, ⟨j, hj, hem⟩, hpay⟩ := hp
  have hs0 : 0 < s := hslot.1
  change rho.events[j]? = some (.tick _ (SA.proposalTime p.toParams s)) at hj
  have hem0 := hem
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨auth, m⟩ := o
  cases m with
  | head B => cases hpay
  | row body => cases hpay
  | proposal b' raw sup rows =>
  cases hpay
  cases auth with
  | none =>
    change (⟨.none, _⟩ : Obj p) ∈ (if E.awake _ _ then
      (duties p _).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) _).filterMap
        (fun i => ((fgsa p c).act ((fgsa p c).clock _ _) d (rho.input _ _)).map
          (fun m => ⟨.seat (RunDuty.signLabel d) i, m⟩))) ++ [] else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, _, hm⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    · exact (List.not_mem_nil hem).elim
  | seat l seat =>
    obtain ⟨_, _, d, hl, ht, hm⟩ :=
      (V2.D.Engine.mem_tick_seat_iff E rho _ _ _ l seat _).mp hem
    cases d with
    | headAction v => cases hm
    | fgAction r =>
      change (attest p _ _ _).1.map Msg.row = some (.proposal b raw sup rows) at hm
      obtain ⟨body, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    | propAction s' =>
      have hss : s' = s := by
        change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
        have hΔ : (0 : Int) < p.Δ := p.deltaPos
        have he : (s' : Int) = s := by nlinarith
        exact_mod_cast he
      subst s'
      change RunLabel.prop s = l at hl
      subst l
      have hseat : seat = ⟨0, Nat.one_pos⟩ := by
        have h1 : (fgsa p c).seats (RunLabel.prop s) = 1 := rfl
        have hlt : seat.val < 1 := h1 ▸ seat.isLt
        exact Fin.ext (by change seat.val = 0; omega)
      subst seat
      let nd := V2.D.Run.stateBefore E rho j
        (V2.D.proposerOf rho (fgsaInterface p c) s)
      let st := ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st
      have htick : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
          (SA.proposalTime p.toParams s) = some j := by
        obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? rho
            (V2.D.proposerOf rho (fgsaInterface p c) s)
            (SA.proposalTime p.toParams s) = some k := by
          rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome,
            List.any_eq_true]
          exact ⟨_, List.mem_of_getElem? hj, by simp⟩
        exact (fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hk) hj) ▸ hk
      change (propose p st s).map (withApp _) = some (.proposal b raw sup rows) at hm
      rw [propose_head p st s (Nat.ne_of_gt hs0)] at hm
      have he : Msg.proposal
          (.node (proposerHead p st s) s (packBody (c.app (rho.input _ _))
            (proposalRows p st (proposerHead p st s))))
          ((proposerVotes st s).filterMap liftHead?)
          ((proposerSupport st s).filterMap liftHead?)
          (proposalRows p st (proposerHead p st s)) = .proposal b raw sup rows :=
        Option.some.inj hm
      cases he
      refine ⟨j, _, _, _, hj, hem0, ?_, fgsa_proposal_slot nd s, rfl, rfl⟩
      change (postClock E rho _ _).map (·.st) = some st
      rw [proposalTime_fgsa p c s, postClock_def, preTick_def]
      change (((V2.D.Run.tickIdx? rho _ (SA.proposalTime p.toParams s)).map
        (fun k => V2.D.Run.stateBefore E rho k _)).map
        (fun nd : Node p => (fgsa p c).clock nd (SA.proposalTime p.toParams s))).map
        (fun nd : Node p => nd.st) = some st
      rw [htick]
      rfl

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: SAME the honest proposal wire gives one FG carrier and its stored parent.
The result retains the original signed rows in their original order. -/
theorem healing_promotion_carrier [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    ∃ X : FGBlock (Fin p.n), eraseFG X = Q ∧ X.slot = s ∧
      (∃ rows, HonestCarrier p c E rho s Q rows ∧ X.rows = rows.filterMap RowWire.toRow?) ∧
      ∃ st, proposalStateAt p c E rho s = some st ∧
        FGSA.fgBlockOf st Q.parent = some X.parent := by
  obtain ⟨j, raw, sup, rows, hj, hem, hst, _hslot, hb, hrows⟩ :=
    promotion_proposal_read p c E rho hrec.base.valid.toScheduleWellFormed hQ
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v)
    (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : Q.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk Q rows = true := by
    rw [hb, hrows]
    exact rowsOk_node_packBody _ _ _ _
  have hne : Q ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st Q.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal Q raw sup rows⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  refine ⟨fgBlock P Q rows, eraseFG_fgBlock hne (hPe.trans hpar.symm) rows hok, ?_,
    ⟨rows, ⟨hQ, o, raw, sup, hemit, rfl⟩, rfl⟩, st, hst, ?_⟩
  · rw [fgBlock_slot, hb]
    rfl
  · rw [fgBlock_parent]
    exact hlook

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: SAME an honest slot after GST emits an actual proposal within the horizon.
Recovery supplies the awake proposer; the scheduled tick supplies emission. -/
theorem healing_promotion_slot_proposal [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    ∃ X : FGBlock (Fin p.n), HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧
      X.slot = s ∧
      ∃ rows, HonestCarrier p c E rho s (eraseFG X) rows ∧
        X.rows = rows.filterMap RowWire.toRow? := by
  have hmul : SA.proposalTime p.toParams s = ((4 * s : Nat) : Time) * p.Δ := by
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hrec.base.valid.toScheduleWellFormed
    hrec.base.delta (V2.D.proposerOf rho (fgsaInterface p c) s) hslot.2 (4 * s) (hmul ▸ hhor)
  rw [← hmul] at hi
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let nd := V2.D.Run.stateBefore E rho i v
  let st := FGSA.clock p nd.st (SA.proposalTime p.toParams s)
  obtain ⟨m, hm⟩ : ∃ m, (propose p st s).map
      (withApp (c.app (rho.input v (SA.proposalTime p.toParams s)))) = some m := by
    rw [propose_head p st s (Nat.ne_of_gt hslot.1)]
    exact ⟨_, rfl⟩
  obtain ⟨H, raw, sup, rows, rfl, _, _⟩ := rowsOk_withApp st s _ hm
  have hQ : HonestProposal E rho (fgsaInterface p c) s
      (.node H s (packBody (c.app (rho.input v (SA.proposalTime p.toParams s))) rows)) := by
    refine ⟨hslot, ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal
      (.node H s (packBody (c.app (rho.input v (SA.proposalTime p.toParams s))) rows))
      raw sup rows⟩, ⟨i, hi, ?_⟩, rfl⟩
    rw [(V2.D.Run.step_tick_eq E rho hi).2]
    exact (fgsa_emits_proposal E rho nd v _ s _).mpr
      ⟨hrec.awake v hslot.2 _ hgst hhor, rfl, rfl, hm⟩
  obtain ⟨X, he, hs, hc, _⟩ := healing_promotion_carrier E rho hrec hQ
  exact ⟨X, he ▸ hQ, hs, he ▸ hc⟩

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: SAME the gap slot carries an actual FG proposal on the same time grid.
The full gap window and the gate deadline are retained. -/
theorem healing_promotion_gap_proposal [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (r : Nat) (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      SA.gateTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ∧
      ∃ rows, HonestCarrier p c E rho s (eraseFG X) rows ∧
        X.rows = rows.filterMap RowWire.toRow? := by
  obtain ⟨hwindow, s, hlo, hhi, hslot, hgate⟩ := healing_promotion_gap E rho hrec r hgst hhor
  have hbefore : SA.proposalTime p.toParams s ≤ rho.horizon := by
    change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _ at hgate
    linarith [p.deltaPos]
  have hstart : E.t_GST ≤ SA.proposalTime p.toParams s := by
    have ha := actionTime_periodW p r
    have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
    have hP : 8 * p.Δ ≤ P p := by
      change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
      nlinarith [p.deltaPos]
    linarith [p.deltaPos]
  obtain ⟨X, hQ, hs, hc⟩ := healing_promotion_slot_proposal E rho hrec hslot hstart hbefore
  exact ⟨hwindow, s, X, hQ, hs, hlo, hhi, hgate, hc⟩

end AvailableChain.FGSA.Run
end
