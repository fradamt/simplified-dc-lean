module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- Blueprint 21:1385–1410; r3 A3.
DC: SAME the fixed original rows give coverage only at unchanged parent height.
Assembly supplies rowsReceipt, progressCoverage, the honest-seat quorum and FaultQ.
No batch is built in the parent-already-crossed branch of hfold. -/
theorem healing_promotion_advance (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s) :
    height + 1 ≤ (heightView p X).h := by
  classical
  have ha := actionTime_periodW p r
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hgate : p.actionTime r ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
  have hstart : E.t_GST ≤ p.actionTime r := hgst.trans (by
    have havote : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      rw [actionTime_periodW]
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
        (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ
      push_cast
      nlinarith [p.deltaPos]
    exact hu.trans havote)
  have hc : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s := by
    rw [carrierTimeW_def]
    have := betaF_le_period p ΔF hbound
    linarith [p.deltaPos]
  obtain ⟨_, _, _, hdeadline, _, hafter⟩ :=
    healing_promotion_row_deadline E rho hrec hbound (rSent := r) le_rfl hstart hc
  have hhor : SA.proposalTime p.toParams s ≤ rho.horizon := hphase.2.1
  obtain ⟨U, hU, hUslot, hUP, hrows⟩ := healing_promotion_same_rows E rho hrec perm
    hentry hcovered hgst hphase hu hgate hafter hnew hslot
  have hmature : U.slot + p.δt ≤ X.slot := by
    rw [hslot]
    exact healing_promotion_maturity_of_action p hδ hUslot hs
  have hX : X ≠ .genesis := by
    intro he
    have ht := hnew.1.1
    rw [← hslot, he] at ht
    cases ht
  apply (hfold height U X hX hU hUP ?_ (fun _ => hmature)).1
  intro hpar
  obtain ⟨Y, he, _, hcarrier, st, hst, hlookup⟩ := healing_promotion_carrier E rho hrec hnew
  have hYX : Y = X := eraseFG_injective he
  subst Y
  have hinv := (storeBundle_of_reachable p st
    (healing_promotion_proposal_reachable p c E rho hst)).cstore
  have hparent : X.parent ∈ st.fg.TF := ((fgBlockOf_spec p st hinv _ _).mp hlookup).1
  have hb : BatchPrem p c E rho ΔF .progress r height U X := by
    refine ⟨hrec.base, faultQ, hrec.deltaF, rowsReceipt, ?_, ?_, ?_, ?_, hU, hUP, ?_⟩
    · rw [hslot]
      exact ⟨hdeadline, hhor⟩
    · rw [hslot]
      exact hcarrier
    · rw [hslot]
      exact hafter
    · refine ⟨honestSeats p c rho, subset_rfl, honestQuorum, ?_⟩
      intro i hi
      have hx : rho.seatOf (.base .fg) i ∈ rho.honest := by
        rw [honestSeats_def] at hi
        exact (Finset.mem_filter.mp hi).2
      obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, _, _, _, hr, hrow, hn, hvalid⟩ :=
        hrows _ hx
      obtain ⟨i', hauth⟩ := honestRow_auth p c rho E hrec.base.valid hrow
      have hseat : rho.seatOf (.base .fg) i' = rho.seatOf (.base .fg) i := by
        have hem := hrow.2.2
        cases a with
        | mk auth body =>
          change auth = .seat .fg i' at hauth
          subst auth
          exact ((fgsa_emitsAt_row E rho j _ _ hrow.2.1 i' body).mp hem).2.1
      have hii : i' = i := (hrec.base.linked.toCStar (.base .fg) trivial).1 hseat
      subst i'
      refine ⟨j, rSent, a, p.actionTime rSent, hr, hrow, hauth, hn, ?_, rfl,
        (hvalid hpar).1, (hvalid hpar).2⟩
      change rho.events[j]?.map V2.Event.time = some (p.actionTime rSent)
      rw [hrow.2.1]
      rfl
    · intro i _ W hW hn
      exact healing_rows_above_entry_at_height p st
        (healing_promotion_proposal_reachable p c E rho hst) .progress height U X.parent
        hparent hpar i W hW hn
  exact progressCoverage r height U X hb hpar

end AvailableChain.FGSA.Run
end
