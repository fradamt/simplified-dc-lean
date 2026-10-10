module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem frontierSearch_age_advance (E : Generic.Env V)
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
    {U0 : FGBlock (Fin p.n)}
    (hsource : ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
      (heightView p K).T_h = U0)
    (hc : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s)
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s)
    (hage : SA.proposalTime p.toParams U0.slot + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s) :
    height + 1 ≤ (heightView p X).h := by
  classical
  have hstart : E.t_GST ≤ p.actionTime r := hgst.trans (by
    have havote : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      rw [actionTime_periodW]
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
        (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ
      push_cast
      nlinarith [p.deltaPos]
    exact hu.trans havote)
  obtain ⟨_, _, _, hdeadline, _, hafter⟩ :=
    healing_promotion_row_deadline E rho hrec hbound (rSent := r) le_rfl hstart hc
  have hhor : SA.proposalTime p.toParams s ≤ rho.horizon := hphase.2.1
  obtain ⟨U, hU, hUslot, hUP, hrows⟩ := healing_promotion_same_rows E rho hrec perm
    hentry hcovered hgst hphase hu hgate hafter hnew hslot
  have hUU : U = U0 := by
    obtain ⟨x, K, hx, hK, hKU⟩ := hsource
    obtain ⟨K', _, _, _, _, _, hK', _, _, _, _, _, hKU', _⟩ := hrows x hx
    have hKK : K' = K := Option.some.inj (Option.some.inj (hK'.symm.trans hK))
    exact hKU'.symm.trans (hKK ▸ hKU)
  have hmature : U.slot + p.δt ≤ X.slot := by
    rw [hslot, hUU]
    exact healing_promotion_maturity p hδ hage
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
        hparent hpar hUP i W hW hn
  exact progressCoverage r height U X hb hpar


omit [Fintype V] in
private theorem frontierSearch_age_phase_cut (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {u v w : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hp : PhaseInterval p c E rho u v m J contested) (huw : u ≤ w) (hwv : w ≤ v) :
    PhaseInterval p c E rho u w m J contested := by
  refine ⟨huw, hwv.trans hp.2.1, hp.2.2.1, ?_⟩
  intro i x hui hiw hx
  apply hp.2.2.2 i x hui _ hx
  apply hiw.trans
  change (rho.events.filter (fun e => decide (e.time ≤ w))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ v))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    ((of_decide_eq_true he).trans hwv))

private theorem frontierSearch_age_grid (r s : Nat) (U : FGBlock (Fin p.n)) (ΔF : Time)
    (hlo : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) <
      SA.proposalTime p.toParams s) :
    carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s ∧
    SA.proposalTime p.toParams U.slot + 2 * P p ≤ SA.proposalTime p.toParams s := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have h1 := lt_of_le_of_lt (le_max_left _ _) hlo
  have h2 := lt_of_le_of_lt (le_max_right _ _) hlo
  have h1' : 4 * p.Δ * ((r : Time) * p.R + kappaF p ΔF - 1) < 4 * p.Δ * (s : Time) := by
    rw [betaF_def] at h1
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      4 * (kappaF p ΔF : Time) * p.Δ - 4 * p.Δ < 4 * p.Δ * (s : Time) at h1
    convert h1 using 1; ring
  have h2' : 4 * p.Δ * ((U.slot : Time) + 2 * p.R - 1) < 4 * p.Δ * (s : Time) := by
    change 4 * p.Δ * (U.slot : Time) + 2 * (4 * (p.R : Time) * p.Δ) -
      4 * p.Δ < 4 * p.Δ * (s : Time) at h2
    convert h2 using 1; ring
  have hs1 : (r : Time) * p.R + kappaF p ΔF ≤ s := by
    have hlt : (r : Time) * p.R + kappaF p ΔF - 1 < s := by nlinarith
    linarith only [Int.add_one_le_iff.mpr hlt]
  have hs2 : (U.slot : Time) + 2 * p.R ≤ s := by
    have hlt : (U.slot : Time) + 2 * p.R - 1 < s := by nlinarith
    linarith only [Int.add_one_le_iff.mpr hlt]
  constructor
  · rw [carrierTimeW_def, betaF_def]
    change (r : Time) * (4 * (p.R : Time) * p.Δ) + 4 * (kappaF p ΔF : Time) * p.Δ ≤
      4 * p.Δ * (s : Time)
    nlinarith
  · change 4 * p.Δ * (U.slot : Time) + 2 * (4 * (p.R : Time) * p.Δ) ≤
      4 * p.Δ * (s : Time)
    nlinarith

/-- Blueprint 21 HG.3/HG.2. DC: SAME the actual source entry is an explicit
local branch input. The producer uses the frozen progress fold and full G window.
INLINE rowsReceipt: fgsa_tRowsReceipt; progressCoverage: fgsa_batchCoverage.
The caller must prove the window and gate bound from its own deadline. -/
theorem frontierSearch_age_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
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
    {u D : Time} {m height r : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {U : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hsource : ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
      (heightView p K).T_h = U)
    (hgst : E.t_GST ≤ u) (hstart : E.t_GST ≤ (r : Time) * P p)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hp : PhaseInterval p c E rho u D m J contested)
    (hwin : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon)
    (hbudget : max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) ≤ D) :
    ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      p.actionTime r < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s ≤ D ∧ height + 1 ≤ (heightView p X).h := by
  obtain ⟨_, s, hlo, hhi, hslot, _, hgate⟩ :=
    healing_promotion_age_gap E rho hrec.toRecovery₂ r U.slot hstart hwin
  have hgateD : SA.gateTime p.toParams s ≤ D := hgate.trans hbudget
  have hhor : SA.proposalTime p.toParams s ≤ rho.horizon := by
    change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D at hgateD
    linarith [p.deltaPos, hp.2.1]
  obtain ⟨hc, hage⟩ := frontierSearch_age_grid r s U ΔF hlo
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  have hcarrier : p.actionTime r < carrierTimeW p ΔF r := by
    rw [actionTime_periodW, carrierTimeW_def, betaF_def]
    nlinarith [p.deltaPos]
  have hat : p.actionTime r < SA.proposalTime p.toParams s := hcarrier.trans_le hc
  have havote : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
    rw [actionTime_periodW]
    change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
      (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have hut : u ≤ SA.proposalTime p.toParams s := hu.trans (havote.trans hat.le)
  have hpT := frontierSearch_age_phase_cut E rho hp hut (by
    change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D at hgateD
    linarith [p.deltaPos])
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    have hcs := hc
    rw [carrierTimeW_def, betaF_def] at hcs
    change (r : Time) * P p + 4 * (kappaF p ΔF : Time) * p.Δ ≤
      4 * p.Δ * (s : Int) at hcs
    nlinarith [p.deltaPos]
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ hws he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hwgst : w ≤ E.t_GST := by
      by_contra hn
      exact hrec.suffixNoRestart _ hslot.2 j w hj (lt_of_not_ge hn)
        ((hws.trans hhor).trans_lt (lt_add_of_pos_right _ (by decide)))
    exact hwgst.trans hcut
  obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
    hslot (hgst.trans hut) hhor hjoin
  have hh := frontierSearch_age_advance E rho hrec.toRecovery₂ hδ hbound perm rowsReceipt
    progressCoverage hfold faultQ honestQuorum hentry hcovered hgst hpT hu hsource
    hc hat.le hage hnew hXslot
  exact ⟨s, X, hnew, hXslot, hat, hgateD, hh⟩

end AvailableChain.FGSA.Run
end
