module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRows -- shake: keep (row source)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt -- shake: keep (row time)

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

/-- ROOT-DIGEST W2b. Blueprint 21:1592–1638; S5 H1, route step 6.
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
        hparent hpar hUP i W hW hn
  exact progressCoverage r height U X hb hpar


end AvailableChain.FGSA.Run
end
