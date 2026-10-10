module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionSource

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem promotion_age_advance (E : Generic.Env V)
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
  apply promotion_age_advance_of_source E rho hrec (r := r) (s := s) (U := U)
    ?_ hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum
  refine ⟨hU, hUP, hnew, hslot, hstart, hc, hUU.symm ▸ hage, hhor, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn, _⟩ := hrows x hx
  exact ⟨j, rSent, a, hr, ha, hn⟩


omit [Fintype V] in
private theorem promotion_age_phase_cut (E : Generic.Env V)
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

/-- Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME the strict age trigger gives the carrier and maturity grid bounds. -/
theorem promotion_age_grid (r s : Nat) (U : FGBlock (Fin p.n)) (ΔF : Time)
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

/-- Blueprint 21:1592–1638; S5 H1, receipt half of persistent-phase HG.2.
DC: SAME the receipt half ends at t_X+Δ and uses the terminal budget.
The repair label and repair continuation belong only to the service tail. -/
theorem healing_promotion_age_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (crossing : RXing p c E rho) (perm : TPerm p c E rho)
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
    {r height : Nat} {Q : Block}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hgst : E.t_GST ≤ u) (hstart : E.t_GST ≤ (r : Time) * P p)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R)) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ v, PhaseInterval p c E rho u v m J contested →
        max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon →
        max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ v →
        let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
        ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
          U_F < SA.proposalTime p.toParams s ∧ SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
          height + 1 ≤ (heightView p X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
          SA.proposalTime p.toParams s + p.Δ ≤
            max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
              (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) := by
  obtain ⟨U, hU, hUslot, hrows⟩ := healing_promotion_bounded_rows E rho hrec.toRecovery₂ hentry
    hcovered
  have hsource : ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
      (heightView p K).T_h = U := by
    have hne : rho.honest.Nonempty := by
      have hn : Fintype.card V = p.n :=
        (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hf := hrec.fault
      rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
      have := p.nPos
      omega
    obtain ⟨x, hx⟩ := hne
    obtain ⟨K, _, _, _, _, _, hK, _, _, _, _, _, hKU, _⟩ := hrows x hx
    exact ⟨x, K, hx, hK, hKU⟩
  refine ⟨U, hU, hUslot, ?_⟩
  intro v hp hwin hbudget
  obtain ⟨_, s, hlo, hhi, hslot, hterminal, hgate⟩ :=
    healing_promotion_age_gap E rho hrec.toRecovery₂ r U.slot hstart hwin
  have hreceiptv : SA.proposalTime p.toParams s + p.Δ ≤ v := hterminal.trans hbudget
  have hhor : SA.proposalTime p.toParams s ≤ rho.horizon := by
    linarith [p.deltaPos, hp.2.1]
  obtain ⟨hc, hage⟩ := promotion_age_grid r s U ΔF hlo
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  have hcarrier : p.actionTime r ≤ carrierTimeW p ΔF r := by
    rw [actionTime_periodW, carrierTimeW_def, betaF_def]
    nlinarith [p.deltaPos]
  have hat : p.actionTime r ≤ SA.proposalTime p.toParams s := hcarrier.trans hc
  have havote : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
    rw [actionTime_periodW]
    change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
      (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have hut : u ≤ SA.proposalTime p.toParams s := hu.trans (havote.trans hat)
  have hpT := promotion_age_phase_cut E rho hp hut (by
    linarith [p.deltaPos])
  have hgsts : E.t_GST ≤ SA.proposalTime p.toParams s := hgst.trans hut
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    unfold slotStartZ
    change (r : Time) * P p + betaF p ΔF ≤ 4 * p.Δ * (s : Int) at hc
    have hb : 8 * p.Δ ≤ betaF p ΔF := by
      rw [betaF_def]
      nlinarith [p.deltaPos]
    nlinarith [p.deltaPos]
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ _ hw
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hw
    exact (healing_recovery_restart_bound E rho hrec hslot.2 hk).trans hcut
  obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
    hslot hgsts hhor hjoin
  have hh := promotion_age_advance E rho hrec.toRecovery₂ hδ hbound perm rowsReceipt
    progressCoverage hfold
    faultQ honestQuorum hentry hcovered hgst hpT hu hsource hc hat hage hnew hXslot
  have hpD : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ)
      m J contested := promotion_age_phase_cut E rho hp (by linarith [p.deltaPos]) (by
    linarith [p.deltaPos])
  have hreceipt := healing_promotion_first_receipt E rho hrec.toRecovery₂ crossing (services s) hnew
    hut hgst hpD
  exact ⟨s, X, hnew, hXslot, hlo, hhi, hh, hreceipt, hterminal⟩

/-- Blueprint 21:1592–1638; S5 H1, service tail of persistent-phase HG.2.
DC: SAME service alone uses repair continuation and the phase through the gate.
The gate budget is the original HG.2b_F maximum. -/
theorem healing_promotion_age_service_tail (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {u : Time} {m r : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {l s : Slot} {U X : FGBlock (Fin p.n)}
    (hl : SA.proposalTime p.toParams l < (r : Time) * P p)
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hlo : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) <
      SA.proposalTime p.toParams s)
    (hhi : SA.proposalTime p.toParams s ≤
      max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
        (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + Γ p G)
    (hpgate : PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested) :
    ExactService p c E rho s (eraseFG X) ∧
      SA.gateTime p.toParams s ≤
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  have hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s := by
    have ht := lt_of_le_of_lt (le_max_left _ _) hlo
    rw [betaF_def] at ht
    nlinarith [p.deltaPos]
  refine ⟨healing_promotion_continuing_service E rho hrepair hls hnew hpgate, ?_⟩
  have hgate : max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) =
      max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
        (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + Γ p G + 6 * p.Δ := by
    rw [actionTime_periodW, epsF_def, ← max_add_add_right, ← max_add_add_right]
    congr 1 <;> ring
  rw [hgate]
  change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
  linarith only [hhi]

/-- Blueprint 21:1592–1638; r3 A5, persistent-phase HG.2.
DC: SAME the age trigger uses q = U.slot for the actual fixed starting entry.
The full G window and a phase through the gate budget are explicit local
premises. First receipt remains strict and block delay remains Δ. -/
theorem healing_promotion_age_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (crossing : RXing p c E rho) (perm : TPerm p c E rho)
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
    {r height : Nat} {l : Slot} {Q : Block}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hgst : E.t_GST ≤ u) (hstart : E.t_GST ≤ (r : Time) * P p)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hl : SA.proposalTime p.toParams l < (r : Time) * P p)
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ v, PhaseInterval p c E rho u v m J contested →
        max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon →
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) ≤ v →
        let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
          (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
        ∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
          U_F < SA.proposalTime p.toParams s ∧ SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
          height + 1 ≤ (heightView p X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
          SA.proposalTime p.toParams s + p.Δ ≤
            max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
              (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ∧
          (PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
            ExactService p c E rho s (eraseFG X) ∧
            SA.gateTime p.toParams s ≤
              max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
                (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ)) := by
  obtain ⟨U, hU, hUslot, hreceipt⟩ := healing_promotion_age_receipt E rho hrec services hδ hbound
    crossing perm rowsReceipt progressCoverage hfold faultQ honestQuorum
    hentry hcovered hgst hstart hu
  refine ⟨U, hU, hUslot, ?_⟩
  intro v hp hwin hbudget
  have hb : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) ≤ v := by
    obtain ⟨ha, hU⟩ := max_le_iff.mp hbudget
    apply max_le <;> linarith [p.deltaPos]
  obtain ⟨s, X, hnew, hslot, hlo, hhi, hh, hr, ht⟩ := hreceipt v hp hwin hb
  refine ⟨s, X, hnew, hslot, hlo, hhi, hh, hr, ht, ?_⟩
  intro hpgate
  exact healing_promotion_age_service_tail E rho hrec.toRecovery₂ hl hrepair hnew hlo hhi hpgate

end AvailableChain.FGSA.Run
end
