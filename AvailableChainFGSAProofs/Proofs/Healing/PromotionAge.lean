module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME fixed opening rows, saved entry, and parent path at the proposal read.
The time fields are local grid and horizon facts. No phase is stored here. -/
structure PromotionSourceAt (p : Params) (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (r height : Nat)
    (U : FGBlock (Fin p.n)) (s : Slot) (X : FGBlock (Fin p.n)) : Prop where
  entry : EntryAt p U height
  parentPath : FGBlock.Preceq U X.parent
  proposal : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)
  slot : X.slot = s
  sync : E.t_GST ≤ p.actionTime r
  carrier : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s
  age : SA.proposalTime p.toParams U.slot + 2 * P p ≤ SA.proposalTime p.toParams s
  horizon : SA.proposalTime p.toParams s ≤ rho.horizon
  rows : ∀ x ∈ rho.honest, ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
    NamesEntry p .progress a height U

/-- Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME progress uses the fixed rows and source path at the proposal read.
The core has no phase, permanence, repair, or service endpoint premise. -/
theorem promotion_age_advance_of_source (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {U X : FGBlock (Fin p.n)} {s : Slot}
    (src : PromotionSourceAt p c E rho ΔF r height U s X)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho)) :
    height + 1 ≤ (heightView p X).h := by
  classical
  obtain ⟨hU, hUP, hnew, hslot, hstart, hc, hage, hhor, hrows⟩ := src
  obtain ⟨_, _, _, hdeadline, _, hafter⟩ :=
    healing_promotion_row_deadline E rho hrec hbound (rSent := r) le_rfl hstart hc
  have hmature : U.slot + p.δt ≤ X.slot := by
    rw [hslot]
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
      obtain ⟨j, rSent, a, hr, hrow, hn⟩ :=
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
      have hT : (heightView p X.parent).T_h = U :=
        ((fgCertificateLaws p).height.entry_plateau hUP
          (hU.1.trans hpar.symm)).symm.trans hU.2
      obtain ⟨b, hb, hpair⟩ : ∃ b, a.toRow? = some b ∧
          b.height_pair = a.payload.height_pair := by
        cases a with
        | mk auth payload =>
          change auth = .seat .fg i at hauth
          subst auth
          exact ⟨_, rfl, rfl⟩
      have hm : Window.heightMatch (parentFoldState p s X.parent) b = true := by
        obtain ⟨_, hn'⟩ := hn
        rw [Window.heightMatch_def, hpair, hn']
        change decide (height = (heightView p X.parent).h ∧
          U.root = (heightView p X.parent).T_h.root) = true
        rw [hpar, hT]
        exact decide_eq_true ⟨rfl, rfl⟩
      have hv : Window.rowValidW (parentFoldState p s X.parent) a = true :=
        (Window.rowValidW_iff _ a).mpr ⟨b, hb, Or.inl hm⟩
      have hvalid : ValidForParent p c E rho X.slot (eraseFG X) a ∧
          HeightMatch p c E rho X.slot (eraseFG X) a := by
        rw [hslot]
        refine ⟨⟨st, X.parent, hst, hlookup, hv⟩, st, X.parent, hst, hlookup, ?_⟩
        obtain ⟨_, hn'⟩ := hn
        rw [hn']
        change some (height, U.root) = some ((heightView p X.parent).h,
          (heightView p X.parent).T_h.root)
        rw [hpar, hT]
      refine ⟨j, rSent, a, p.actionTime rSent, hr, hrow, hauth, hn, ?_, rfl,
        hvalid.1, hvalid.2⟩
      change rho.events[j]?.map V2.Event.time = some (p.actionTime rSent)
      rw [hrow.2.1]
      rfl
    · intro i _ W hW hn
      exact healing_rows_above_entry_at_height p st
        (healing_promotion_proposal_reachable p c E rho hst) .progress height U X.parent
        hparent hpar i W hW hn
  exact progressCoverage r height U X hb hpar


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
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
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
  obtain ⟨U, hU, hUslot, hrows⟩ := healing_promotion_bounded_rows E rho hrec hentry hcovered
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
    healing_promotion_age_gap E rho hrec r U.slot hstart hwin
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
  obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec hslot hgsts hhor
  have hh := promotion_age_advance E rho hrec hδ hbound perm rowsReceipt progressCoverage hfold
    faultQ honestQuorum hentry hcovered hgst hpT hu hsource hc hat hage hnew hXslot
  have hpD : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ)
      m J contested := promotion_age_phase_cut E rho hp (by linarith [p.deltaPos]) (by
    linarith [p.deltaPos])
  have hreceipt := healing_promotion_first_receipt E rho hrec crossing hnew hut hgst hpD
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
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
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
  obtain ⟨U, hU, hUslot, hreceipt⟩ := healing_promotion_age_receipt E rho hrec hδ hbound
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
  exact healing_promotion_age_service_tail E rho hrec hl hrepair hnew hlo hhi hpgate

end AvailableChain.FGSA.Run
end
