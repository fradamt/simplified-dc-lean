module
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGSA.Proofs.WindowRetention
public import AvailableChainKitFG.CausalCapCore
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- Assembly supplies this raw origin from execution validity (B28).
variable (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
    HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
      ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)

omit [Fintype V] in
/-- DC: INTENTIONAL: local equation for the linked-seat filter. -/
private theorem khistory_honestSeats_def : honestSeats p c rho =
    @Finset.filter (Fin p.n) (fun i => rho.seatOf (.base .fg) i ∈ rho.honest)
      (fun i => Classical.propDecidable (rho.seatOf (.base .fg) i ∈ rho.honest)) Finset.univ := rfl

omit [Fintype V] in
/-- DC: INTENTIONAL: membership uses the definition's classical decision procedure. -/
private theorem khistory_honestSeats_mem (i : Fin p.n) :
    i ∈ honestSeats p c rho ↔ rho.seatOf (.base .fg) i ∈ rho.honest := by
  rw [khistory_honestSeats_def p c rho]
  simpa only [Finset.mem_univ, true_and] using
    (@Finset.mem_filter (Fin p.n) (fun k => rho.seatOf (.base .fg) k ∈ rho.honest)
      (fun k => Classical.propDecidable (rho.seatOf (.base .fg) k ∈ rho.honest))
      Finset.univ i)

omit [DecidableEq V] [Fintype V] in
/-- DC: INTENTIONAL: local equation for optional event time. -/
private theorem khistory_eventTime_def (j : Nat) :
    eventTime rho j = rho.events[j]?.map V2.Event.time := rfl

/-- DC: INTENTIONAL: local equation for optional row height. -/
private theorem khistory_rowHeight_def (a : RowWire p.n) : rowHeight a =
    (match a.payload.height_pair with | .empty => none | .vote h _ _ => some h) := rfl

/-- FINAL 22:948–958. Linked unit-weight seats bound the faulty weight.
DC: INTENTIONAL: FG-SA uses linked seats. -/
private theorem khistory_faulty_weight (base : BaseSet p c E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (Finset.univ \ honestSeats p c rho) < p.E.q := by
  classical
  have hsub : (Finset.univ \ honestSeats p c rho).image (rho.seatOf (.base .fg)) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    have hn := (Finset.mem_sdiff.mp hi).2
    exact fun hh => hn ((khistory_honestSeats_mem p c rho i).mpr hh)
  have hinj : Function.Injective (fun i : Fin p.n => rho.seatOf (.base .fg) i) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hc : (Finset.univ \ honestSeats p c rho).card ≤
      (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective _ hinj).symm.trans_le (Finset.card_le_card hsub)
  have hw : p.E.weightOf (Finset.univ \ honestSeats p c rho) =
      (Finset.univ \ honestSeats p c rho).card := by
    change (∑ _ ∈ Finset.univ \ honestSeats p c rho, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt hQ.lt

omit [Fintype V] in
/-- FINAL 22:948–958. A seat outside the faulty set is honest.
DC: INTENTIONAL: FG-SA uses linked seats. -/
private theorem khistory_honest_seat (u : Row (Fin p.n))
    (hf : u.signer ∉ Finset.univ \ honestSeats p c rho) :
    rho.seatOf (.base .fg) u.signer ∈ rho.honest := by
  classical
  have hm : u.signer ∈ honestSeats p c rho := by
    by_contra hn
    exact hf (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩)
  exact (khistory_honestSeats_mem p c rho u.signer).mp hm

/-- FINAL 22:954–956. Decode the exact signed wire payload.
DC: INTENTIONAL: FG-SA uses seat-authenticated wires. -/
private theorem khistory_decode {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

omit [Fintype V] in
/-- FINAL 22:954–956. The emission tick gives its exact action time.
DC: INTENTIONAL: the run uses event-indexed emission. -/
private theorem khistory_event_time {j r : Nat} {z : V} {a : RowWire p.n}
    (hj : HonestRowAt p c E rho j z r a) :
    eventTime rho j = some (p.actionTime r) := by
  rw [khistory_eventTime_def p c rho, hj.2.1]
  rfl

include horigin in
/-- FINAL 22:954–956. Authenticate each raw carrier before its strict cut.
DC: ProposalBridge.lean:324; FG-SA retains the delivery witness. -/
private theorem khistory_raw_origin (base : BaseSet p c E rho)
    (B W : FGBlock (Fin p.n)) (cut : Time) (u : Row (Fin p.n))
    (hraw : ChainRowsBefore p c E rho B cut) (hpath : FGBlock.Preceq W B)
    (hocc : u ∈ W.rows) (hh : rho.seatOf (.base .fg) u.signer ∈ rho.honest) :
    ∃ j r a t, HonestRowAt p c E rho j (rho.seatOf (.base .fg) u.signer) r a ∧
      a.toRow? = some u ∧ eventTime rho j = some t ∧ t < cut := by
  obtain ⟨x, s, hx, hs, hW⟩ := hraw W hpath u hocc
  have held : HeldAt p c E rho (V2.D.Run.idxBefore rho s) x W := by
    refine ⟨hx, ?_⟩
    change W ∈ (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho s) x).st.fg.TF
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho s base.valid.toScheduleWellFormed]
    exact hW
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ :=
    horigin _ x W held u (mem_chainRows_of_carrier (preceq_refl _) hocc)
  have hsign : RowSigner p c rho a (rho.seatOf (.base .fg) u.signer) :=
    ⟨u.signer, har, rfl⟩
  obtain ⟨hb, ht⟩ := he _ hsign hh
  obtain ⟨j, _hji, hj⟩ := hb
  have hts := (Gen.V2.Duty.index_lt_idxBefore_iff
    base.valid.toScheduleWellFormed hk s).mp hki
  exact ⟨j, r, a, p.actionTime r, hj, ha, khistory_event_time p c E rho hj,
    (ht.trans_lt hts).trans hs⟩

/-- FINAL 22:954–956. A matching pair has the stated wire height.
DC: INTENTIONAL: the wire height is optional for an empty pair. -/
private theorem khistory_matching_height {u : Row (Fin p.n)} {a : RowWire p.n}
    {y : Nat} {T : BlockId} (ha : a.toRow? = some u)
    (hm : u.height_pair.matchesEntry y T = true) : rowHeight a = some y := by
  rw [khistory_decode p ha]
  cases hp : u.height_pair with
  | empty => simp only [hp, NamedHeightPair.matchesEntry] at hm; contradiction
  | vote h U timeout =>
    have hh : h = y := by
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      exact hm.1
    rw [khistory_rowHeight_def p]
    change some h = some y
    rw [hh]

include horigin in
/-- FINAL 22:1771–1780. No honest height-y row precedes the first action.
DC: CarrierTimeoutGate.lean:121; FG-SA uses a raw parent-chain cut. -/
theorem noMixedPreBatchParent (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : PreBatchPrem p c E rho q y U X) : NoMixedOnPath p X y := by
  intro W hWP hm
  obtain ⟨hp, hw, _hj⟩ := hm
  have hne : W ≠ .genesis := by
    intro heq
    subst W
    change (heightView p .genesis).h = y at hp
    rw [hp] at hw
    simp only [Height] at hw
    omega
  obtain ⟨C, u, hCW, hu, hf, hmatch⟩ := crossing_honest_matching_row_of_bridge
    p.E p.cfg (heightView p) (heightView_bridge p) (Finset.univ \ honestSeats p c rho)
    y hne hp hw (khistory_faulty_weight p c E rho h.base h.faultQ)
  obtain ⟨j, r, a, t, hj, ha, ht, hearly⟩ := khistory_raw_origin p c E rho horigin
    h.base X.parent C h.cut u h.rows (preceq_trans hCW hWP) hu
    (khistory_honest_seat p c rho u hf)
  have hlate := h.noRow j _ r a y t hj (khistory_matching_height p ha hmatch)
    (le_refl _) ht
  exact (not_lt.mpr hlate) (hearly.trans_le h.early)


/-- FINAL 22:954–956. Expose the carrier of a raw chain row.
DC: INTENTIONAL: the endpoint need not be held. -/
private theorem khistory_carrier (B : FGBlock (Fin p.n)) (u : Row (Fin p.n))
    (hu : u ∈ chainRows B) : ∃ W, FGBlock.Preceq W B ∧ u ∈ W.rows := by
  induction B with
  | genesis => exact (Finset.notMem_empty u hu).elim
  | node P s x rs ih =>
    change u ∈ rs.toFinset ∪ chainRows P at hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact ⟨.node P s x rs, preceq_refl _, List.mem_toFinset.mp hu⟩
    · obtain ⟨W, hWP, hu⟩ := ih hu
      exact ⟨W, preceq_node_of_preceq s x rs hWP, hu⟩

include horigin in
/-- FINAL 22:948–958. Raw rows before a cut bound the endpoint height.
DC: INTENTIONAL: each raw carrier is authenticated separately. -/
private theorem khistory_chain_height_le (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (B : FGBlock (Fin p.n)) (cut : Time) (m : Nat)
    (hraw : ChainRowsBefore p c E rho B cut)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m) :
    (heightView p B).h ≤ m + 1 := by
  by_contra hn
  obtain ⟨C, _hCB, _hC, Q, hQ, hw⟩ := (fgCertificateLaws p).height.height_crossing
    B (m + 1) (by simp only [Height]; omega) (by simp only [Height] at *; omega)
  obtain ⟨seat, hs, hf⟩ := honest_in_quorum p.E (Finset.univ \ honestSeats p c rho)
    hQ (khistory_faulty_weight p c E rho base faultQ)
  obtain ⟨W, u, hWB, hu, hsign, hm⟩ := hw seat hs
  have hfu : u.signer ∉ Finset.univ \ honestSeats p c rho := hsign ▸ hf
  obtain ⟨j, r, a, t, hj, ha, ht, hearly⟩ := khistory_raw_origin p c E rho horigin
    base B W cut u hraw hWB hu (khistory_honest_seat p c rho u hfu)
  have hb := hrows j _ r a (m + 1) t hj (khistory_matching_height p ha hm) ht hearly
  omega

include horigin in
/-- FINAL 22:952–958. A positive W certificate has an honest raw row before the cut.
DC: INTENTIONAL: the active W certificate supplies the exact finality height. -/
private theorem khistory_finality_origin (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (X : FGBlock (Fin p.n)) (cut : Time) (y : Nat)
    (hraw : ChainRowsBefore p c E rho X cut)
    (hy : 0 < y) (hF : y ≤ (finalityView p X).h_F) :
    ∃ j z r a t, HonestRowAt p c E rho j z r a ∧
      finHeight a = some (finalityView p X).h_F ∧ eventTime rho j = some t ∧ t < cut := by
  let R := fun u : Row (Fin p.n) => ∃ j r a t,
    HonestRowAt p c E rho j (rho.seatOf (.base .fg) u.signer) r a ∧
      a.toRow? = some u ∧ eventTime rho j = some t ∧ t < cut
  obtain ⟨u, _hu, _hf, ho, hp⟩ := finalityCap_row_of_certificate p.E
    (heightView p) (finalityView p) (fgCertificateLaws p)
    (Finset.univ \ honestSeats p c rho) (khistory_faulty_weight p c E rho base faultQ)
    y X R (by
      intro u hu hf
      obtain ⟨W, hWX, hu⟩ := khistory_carrier p X u hu
      exact khistory_raw_origin p c E rho horigin base X W cut u hraw hWX hu
        (khistory_honest_seat p c rho u hf)) hy hF
  obtain ⟨j, r, a, t, hj, ha, ht, hearly⟩ := ho
  refine ⟨j, _, r, a, t, hj, ?_, ht, hearly⟩
  rw [khistory_decode p ha]
  change u.finality_pair.map (·.height) = some (finalityView p X).h_F
  rw [hp]
  rfl

/-- FINAL 22:1061–1070. A justified target crossing creates the exact retained W key.
DC: W4FKChainJustification.lean:185; FG-SA appends the key to its window. -/
private theorem khistory_retained_cross (y : Nat) (U C : FGBlock (Fin p.n))
    (hc : JustifiedCross p C U y) : Window.RetainedW p C y U := by
  obtain ⟨hp, hh, hJ, hj⟩ := hc
  have hne : C ≠ .genesis := by
    intro heq
    subst C
    change (heightView p .genesis).h = y at hp
    rw [hp] at hh
    simp only [Height] at hh
    omega
  cases C with
  | genesis => exact (hne rfl).elim
  | node P s x rs =>
    change (heightView p P).h = y at hp
    have hp' : (Window.derive p p.K_W P).h = y := by
      simpa only [heightView_def, Window.projectHeight_def] using hp
    have hj' : (Window.derive p p.K_W (.node P s x rs)).h_j = y := by
      simpa only [heightView_def, Window.projectHeight_def] using hj
    have hJ' : (Window.derive p p.K_W (.node P s x rs)).J = U := by
      simpa only [heightView_def, Window.projectHeight_def] using hJ
    have ht : Window.targetQuorum p.E
        (Window.finalizeWindow p.E (Window.certificateFolded p p.K_W (.node P s x rs))) =
          true := by
      rcases Window.window_latest_pair_kept p p.K_W P s x rs with kept | crossed
      · have below := (fgCertificateLaws p).height.justified_below_height P
        simp only [heightView_def, Window.projectHeight_def] at below
        rw [← kept.1, hj', hp'] at below
        exact (Nat.lt_irrefl y below).elim
      · exact crossed.2.2
    have latest : (Window.derive p p.K_W (.node P s x rs)).h_j =
        (Window.finalizeWindow p.E
          (Window.certificateFolded p p.K_W (.node P s x rs))).h ∧
        (Window.derive p p.K_W (.node P s x rs)).J =
        (Window.finalizeWindow p.E
          (Window.certificateFolded p p.K_W (.node P s x rs))).T_h := by
      change (Window.process_height_events p.E p.cfg p.K_W
          (Window.certificateFolded p p.K_W (.node P s x rs))).h_j = _ ∧
        (Window.process_height_events p.E p.cfg p.K_W
          (Window.certificateFolded p p.K_W (.node P s x rs))).J = _
      rw [Window.process_height_events_def, ite_eq_left ht]
      exact ⟨rfl, rfl⟩
    obtain ⟨_hw, older, appended, _hord, _hf⟩ :=
      Window.window_target_appended_newest p p.K_W p.kWLarge P s x rs ht
    rw [latest.1.symm.trans hj', latest.2.symm.trans hJ'] at appended
    rw [Window.RetainedW_def]
    refine ⟨⟨y, U, ∅⟩, ?_, rfl, rfl⟩
    rw [appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)

include horigin in
/-- FINAL 22:945–958,1218–1223. Fresh raw history fixes the endpoint and retains its W key.
DC: W4FKChainJustification.lean:185; FG-SA also proves the strict W finality bound. -/
theorem justifyFresh_W (q y : Nat) (U X : FGBlock (Fin p.n)) (hX : X ≠ .genesis)
    (hentry : EntryAt p U y) (hpath : FGBlock.Preceq U X.parent)
    (hcover : (heightView p X.parent).h = y → CoveredByChild p .target X U y)
    (hnomix : NoMixedOnPath p X y) (h : FreshPrem p c E rho q y X) :
    (heightView p X).h = y + 1 ∧ (heightView p X).J = U ∧
      (heightView p X).h_j = y ∧ (Window.derive p p.K_W X).h_F < y ∧
      Window.RetainedW p X y U := by
  obtain ⟨C, hCX, hc⟩ := fgsa_justifyAt p y U X hX hentry hpath hcover hnomix
  have hy : 0 < y := by
    have hb := (fgCertificateLaws p).height.one_le_h U
    rw [hentry.1] at hb
    simp only [Height] at *
    omega
  have hlo := (fgCertificateLaws p).height.h_mono hCX
  rw [hc.2.1] at hlo
  have hhi := khistory_chain_height_le p c E rho horigin h.base h.faultQ X h.cut y
    h.rows (by
      intro j z r a H t hj ha ht hearly
      by_contra hn
      have hlate := h.noNextRow j z r a H t hj ha (by omega) ht
      exact (not_lt.mpr hlate) (hearly.trans_le h.early))
  have hh : (heightView p X).h = y + 1 := by simp only [Height] at *; omega
  obtain ⟨hJ, hj⟩ := justification_eq_on_plateau_of_bridge p.E p.cfg
    (heightView p) (heightView_bridge p) hCX (hc.2.1.trans hh.symm)
  have hJU := hJ.trans hc.2.2.1
  have hjy := hj.trans hc.2.2.2
  have hf : (finalityView p X).h_F < y := by
    by_contra hn
    obtain ⟨j, z, r, a, t, hj, ha, ht, hearly⟩ :=
      khistory_finality_origin p c E rho horigin h.base h.faultQ X h.cut y h.rows hy
        (Nat.le_of_not_gt hn)
    have hlate := h.noFinRow j z r a _ t hj ha (Nat.le_of_not_gt hn) ht
    exact (not_lt.mpr hlate) (hearly.trans_le h.early)
  have hfW : (Window.derive p p.K_W X).h_F < y := by
    simpa only [finalityView_def, Window.certificateFinality_def,
      Window.projectFinality_def] using hf
  obtain ⟨e, he, hey, heU⟩ := khistory_retained_cross p y U C hc
  obtain ⟨d, hd, hdy, hdU, _hbits⟩ := Window.window_retained_of_scalar p p.K_W p.kWLarge
    C X hCX e he (by rw [hey]; exact hfW) (by
      have hjW : (Window.derive p p.K_W X).h_j = y := by
        simpa only [heightView_def, Window.projectHeight_def] using hjy
      rw [hjW, hey]
      have hK := p.kWLarge
      simp only [Height] at *
      omega)
  exact ⟨hh, hJU, hjy, hfW, d, hd, hdy.trans hey, hdU.trans heU⟩


include horigin in
/-- FINAL 22:923–938. A held chain has no crossing above its honest row bound.
DC: INTENTIONAL: timed raw origin replaces a selected-pool bound. -/
private theorem khistory_held_height_le (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (hheld : HeldAt p c E rho i x B)
    (hbefore : ∀ k o t, k < i → rho.events[k]? = some (.deliver x o t) → t < cut) :
    (heightView p B).h ≤ m + 1 := by
  by_contra hn
  obtain ⟨C, _hCB, _hC, Q, hQ, hw⟩ := (fgCertificateLaws p).height.height_crossing
    B (m + 1) (by simp only [Height]; omega) (by simp only [Height] at *; omega)
  obtain ⟨seat, hs, hf⟩ := honest_in_quorum p.E (Finset.univ \ honestSeats p c rho)
    hQ (khistory_faulty_weight p c E rho base faultQ)
  obtain ⟨W, u, hWB, hu, hsign, hm⟩ := hw seat hs
  have hfu : u.signer ∉ Finset.univ \ honestSeats p c rho := hsign ▸ hf
  have hhonest := khistory_honest_seat p c rho u hfu
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ :=
    horigin i x B hheld u (mem_chainRows_of_carrier hWB hu)
  have hsigner : RowSigner p c rho a (rho.seatOf (.base .fg) u.signer) :=
    ⟨u.signer, har, rfl⟩
  obtain ⟨hb, hrt⟩ := he _ hsigner hhonest
  obtain ⟨j, _hji, hj⟩ := hb
  have ht := hrt.trans_lt (hbefore k o t hki hk)
  have bound := hrows j _ r a (m + 1) (p.actionTime r) hj
    (khistory_matching_height p ha hm) (khistory_event_time p c E rho hj) ht
  omega

include horigin in
/-- FINAL 22:923–938. Strict raw history caps a held block before the cut.
DC: INTENTIONAL: a delivery witness makes the event cut strict. -/
theorem raw_causal_cap_before (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (hcut : i ≤ V2.D.Run.idxBefore rho cut) (hheld : HeldAt p c E rho i x B) :
    (heightView p B).h ≤ m + 1 := by
  apply khistory_held_height_le p c E rho horigin base faultQ m cut hrows i x B hheld
  intro k o t hki hk
  exact (Gen.V2.Duty.index_lt_idxBefore_iff base.valid.toScheduleWellFormed hk cut).mp
    (hki.trans_le hcut)

include horigin in
/-- FINAL 22:923–938. The tick read precedes every delivery at the same time.
DC: INTENTIONAL: event phases give a strict cut across different nodes' ticks. -/
theorem raw_causal_cap_at_tick (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (v : V)
    (htick : rho.events[i]? = some (.tick v cut)) (hheld : HeldAt p c E rho i x B) :
    (heightView p B).h ≤ m + 1 := by
  apply khistory_held_height_le p c E rho horigin base faultQ m cut hrows i x B hheld
  intro k o t hki hk
  by_contra hn
  have hik := V2.D.Engine.tick_index_lt_delivery E rho
    base.valid.toScheduleWellFormed htick hk (le_of_not_gt hn)
  exact (Nat.lt_asymm hki hik)

/-- FINAL 22:217–220,923–944. Positive delay and round length order the actions.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
private theorem khistory_action_strictMono : StrictMono p.actionTime := by
  intro m n hmn
  change 4 * p.Δ * ((m * p.R : Nat) : Int) + 6 * p.Δ <
    4 * p.Δ * ((n * p.R : Nat) : Int) + 6 * p.Δ
  have hR : 0 < p.R := by have h := p.RLarge; omega
  have hΔ : 0 < 4 * p.Δ := mul_pos (by decide) p.deltaPos
  have hmul : m * p.R < n * p.R := Nat.mul_lt_mul_of_pos_right hmn hR
  have hprod : 4 * p.Δ * ((m * p.R : Nat) : Int) <
      4 * p.Δ * ((n * p.R : Nat) : Int) :=
    mul_lt_mul_of_pos_left (Int.ofNat_lt.mpr hmul) hΔ
  exact Int.add_lt_add_right hprod _

include horigin in
/-- FINAL 22:923–944,1188–1208. Include action q rows up to the strict next-action cut.
DC: INTENTIONAL: the current-action bound is explicit and has no source circularity. -/
theorem raw_causal_cap_through_action (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (q m : Nat)
    (hpre : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < p.actionTime q → h ≤ m)
    (haction : ∀ j z a h, HonestRowAt p c E rho j z q a → rowHeight a = some h → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (hcut : i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)))
    (hheld : HeldAt p c E rho i x B) : (heightView p B).h ≤ m + 1 := by
  apply raw_causal_cap_before p c E rho horigin base faultQ m (p.actionTime (q + 1))
    _ i x B hcut hheld
  intro j z r a H t hj ha ht hearly
  have heq : p.actionTime r = t :=
    Option.some.inj ((khistory_event_time p c E rho hj).symm.trans ht)
  have hrq : r ≤ q := by
    have hlt : p.actionTime r < p.actionTime (q + 1) := heq ▸ hearly
    have := (khistory_action_strictMono p).lt_iff_lt.mp hlt
    omega
  rcases Nat.lt_or_eq_of_le hrq with hlt | rfl
  · exact hpre j z r a H t hj ha ht
      (heq ▸ khistory_action_strictMono p hlt)
  · exact haction j z a H hj ha

end AvailableChain.FGSA.Run
end
