module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.Frame
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- Blueprint 21:1410–1419; r3 A4.
DC: SAME first receipt uses the already-held parent and the strict deadline read.
RXing is applied to the parent, with its own proposer-floor bound.
At top J, the walk extends the fixed J, including genesis at m = 1. -/
theorem healing_promotion_first_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {s : Slot}
    {X : FGBlock (Fin p.n)}
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hafter : u ≤ SA.proposalTime p.toParams s) (hgst : E.t_GST ≤ u)
    (hp : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) m J contested) :
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y := by
  let t := SA.proposalTime p.toParams s
  let d := t + p.Δ
  let x := V2.D.proposerOf rho (fgsaInterface p c) s
  have hx : x ∈ rho.honest := hnew.1.2
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨ip, raw, sup, rows, hip, hem, hst, _, hbody, _⟩ :=
    healing_promotion_proposal_read p c E rho hs hnew
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho ip x) t).st
  have hfg : st.fg = (storeAt p c E rho ip x).fg := clock_fg p _ _
  have huip : V2.D.Run.idxBefore rho u ≤ ip := by
    by_contra hn
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hip u).mp (by omega)
    change t < u at hlt
    exact (not_lt_of_ge hafter) hlt
  have hipd : ip < V2.D.Run.idxBefore rho d :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hip d).mpr (lt_add_of_pos_right t p.deltaPos)
  have hiphi : ip ≤ timeIdx rho d :=
    hipd.le.trans (healing_phase_idx_le_time p c rho le_rfl)
  obtain ⟨hHi, hci, hri⟩ := hp.2.2.2 ip x huip hiphi hx
  have hne : (fullTree p st).Nonempty := by
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho ip x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    change (KitFG.storeFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨P, hP, heP, hfloor⟩ := healing_proposer_floor p c E rho hs s (eraseFG X) st
    hnew hst hne
  have hPX : P = X.parent := eraseFG_injective (heP.trans (eraseFG_parent X))
  subst P
  have hPip : X.parent ∈ (storeAt p c E rho ip x).fg.TF := by
    have hm := ((KitFG.mem_filteredFromView _ _ _ _).mp hP).1
    rwa [hfg] at hm
  let jd := V2.D.Run.idxBefore rho d
  have hujd : V2.D.Run.idxBefore rho u ≤ jd := huip.trans hipd.le
  have hjdhi : jd ≤ timeIdx rho d := healing_phase_idx_le_time p c rho le_rfl
  obtain ⟨hHd, hcd, hrd⟩ := hp.2.2.2 jd x hujd hjdhi hx
  have frameD := healing_phase_frame p c E rho crossing hx hp.2.2.1 hHd hcd hrd
  have hPjd := (fgsa_store_cumulative p c E rho hrec.base.noRestart hipd.le x).1 hPip
  have hfloorD : (R_at p c E rho jd x).lo ≤ (heightView p X.parent).h := by
    have hfi : (frameR p st).lo = if contested then m else m - 1 := by
      change (if (controls p st).contest then st.fg.h_max else st.fg.h_max - 1) = _
      have hHi' : st.fg.h_max = m := hfg ▸ hHi
      have hci' : (controls p st).contest = contested := by
        change (KitFG.storeControlsView (heightView p) st.fg).contest = contested
        rw [hfg]
        exact hci
      rw [hci', hHi']
    exact frameD.2.2.1 ▸ (hfi ▸ hfloor)
  have hparent : Block.Preceq (eraseFG (storeAt p c E rho jd x).fg.F) (eraseFG X.parent) := by
    cases J with
    | none =>
      obtain ⟨_, _, ⟨K, hK, hKF, hKlo⟩, _⟩ := frameD.2.2.2.1
      exact eraseFG_preceq (crossing jd jd x x K X.parent hx le_rfl hK hKF
        ⟨hx, hPjd⟩ (hKlo.trans_le hfloorD))
    | some B =>
      obtain ⟨_, _, _, _, _, hFB⟩ := frameD.2.2.2.1
      have hZ : (controls p st).Z = B := by
        have hri' : (controls p st).rootIsJ = true ∧ (controls p st).J = B := by
          change (KitFG.storeControlsView (heightView p) st.fg).rootIsJ = true ∧
            (KitFG.storeControlsView (heightView p) st.fg).J = B
          rw [hfg]
          exact hri
        change (if (controls p st).rootIsJ then st.fg.J else st.fg.F) = B
        rw [hri'.1]
        exact hri'.2
      have hBP : Block.Preceq (eraseFG B) (eraseFG X).parent := by
        have hwalk : Block.Preceq (eraseFG (controls p st).Z) (proposerHead p st s) := by
          rw [proposerHead_def]
          exact Gen.Pure.block_preceq_trans (fgsa_Z_preceq_liveRoot p st)
            (liveRoot_preceq_headInTree p st _ (proposerVotes st s) (proposerSupport st s))
        rw [hZ] at hwalk
        have hpar : (eraseFG X).parent = proposerHead p st s := by rw [hbody]; rfl
        rw [hpar]
        exact hwalk
      rw [← eraseFG_parent]
      exact Gen.Pure.block_preceq_trans (eraseFG_preceq hFB) hBP
  have hPX : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node P slot body rows => exact KitFG.preceq_parent_node _ _ _ _
  have hcompat : Block.Compatible (eraseFG X)
      (eraseFG (V2.D.Run.stateBeforeTime E rho d x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (Gen.Pure.block_preceq_trans hparent (eraseFG_preceq hPX)))
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
    Or.inl ⟨x, hx, ip, hip, hem⟩
  have hdline : max t E.t_GST + p.Δ = d := by rw [max_eq_left (hgst.trans hafter)]
  obtain ⟨Y, hY, he⟩ := fgsa_proposal_receipt E rho hrec.base.delta hrec.base.valid
    hrec.base.noRestart (fun t => max t E.t_GST + p.Δ) rho.horizon s (eraseFG X)
    raw sup rows t x hD hT hx (hdline ▸ hp.2.1)
    (hdline ▸ lt_add_of_pos_right t p.deltaPos) (hdline ▸ hcompat)
  have heq : Y = X := eraseFG_injective he
  rw [hdline, heq] at hY
  exact ⟨x, hx, hY⟩

end AvailableChain.FGSA.Run
end
