module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3. Finite phase composition.
Gap and top J are charged once, then contest repair and the tail. A saved seed keeps
the supplied tail budget and no second repair charge. The composition core takes the
per-phase result of the actual start; the full theorem supplies it from the three d5c
phase consumers. The repair allowance at each actual phase start (with its
nonnegativity and repair-start geometry) is an explicit leaf.

Terminal checkpoint (plan checkpoint 2026-10-12 §3.2, route (c)): `TerminalPromotionFact`
stays an unproved intermediate statement. No theorem here reads it. Owner: the P0zF
release ledger (class: open intermediate); it gets no completion credit. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (Jst : Time) (leaseSlots : Nat)
variable (obs : FGObservationLaws R O) (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

private theorem p0d5d_frontier_mono (mono : FGRunOrderLaws E rho R) {i j : Nat}
    (hij : i ≤ j) : frontierAtIdx R E rho i ≤ frontierAtIdx R E rho j := by
  apply Finset.sup_le
  intro x hx
  exact (mono.mono i j x hx hij).2.2.trans
    (Finset.le_sup (f := fun y => (R.core (rho.stateBefore E j y)).fg.h_max) hx)

omit [DecidableEq V] in
private theorem p0d5d_lt_timeIdx (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {e : V2.Event V Prot.Object} (hk : rho.events[k]? = some e) {t : Time}
    (ht : e.time ≤ t) : k < timeIdx rho t := by
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk (t + 1)).mpr (Int.lt_add_one_iff.mpr ht)
  refine hlt.trans_le ?_
  change (rho.events.filter (fun e => decide (e.time < t + 1))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (Int.lt_add_one_iff.mp (of_decide_eq_true he)))

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME rebase a first rise through earlier same-frontier events. -/
theorem frontierSearch_rise_rebase (mono : FGRunOrderLaws E rho R) {i j m : Nat} {D : Time}
    (hij : i ≤ j) (hf : frontierAtIdx R E rho (j + 1) ≤ m)
    (hr : FrontierRiseBy R E rho j m D) : FrontierRiseBy R E rho i m D := by
  obtain ⟨k, ev, hjk, hk, ht, hh, hcap⟩ := (FrontierRiseBy_def R E rho j m D).mp hr
  apply (FrontierRiseBy_def R E rho i m D).mpr
  refine ⟨k, ev, by omega, hk, ht, hh, ?_⟩
  intro l hil hlk
  by_cases hlj : l ≤ j + 1
  · exact (p0d5d_frontier_mono R E rho mono hlj).trans hf
  · exact hcap l (by omega) hlk

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME the HG.3 rise stop supplies the first frontier rise, including equal times. -/
theorem frontierSearch_rise_of_stop (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat}
    {D : Time} (hf : frontierAtIdx R E rho (i + 1) ≤ m)
    (hr : FirstRiseStopBy R E rho O i m D) : FrontierRiseBy R E rho i m D := by
  obtain ⟨j, ev, hij, hj, ht, _, hh, _⟩ := (FirstRiseStopBy_def R E rho O i m D).mp hr
  exact frontierSearch_first_rise R E rho hs ⟨j, hij, p0d5d_lt_timeIdx E rho hs hj ht, hh⟩ hf

include obs cert inv justif keep in
/-- Blueprint 21:1722–1800; S5 F3, finite phase composition core.
DC: SAME gap and top J cannot repeat; a saved seed leaves the supplied tail budget.
`step` is the result of the actual phase consumer at each actual start; the protocol
keeps its own served predicate. -/
theorem frontierSearch_phase_compose (hT : FGTimingLaws T) (crossing : RXing R E rho O)
    (schedule : V2.D.ScheduleWellFormed E rho) (mono : FGRunOrderLaws E rho R)
    (Served : Nat → Time → Prop) {G ΔF ρbar t0 tail : Time} (hG : 4 * T.delta ≤ G)
    (hρ : 0 ≤ ρbar) (htail : 0 ≤ tail)
    (step : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind → t0 ≤ ev.time →
      ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon →
      FirstPhaseStopBy R E rho O i m (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
      FirstRiseStopBy R E rho O i m (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
      ∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget T G ΔF ρbar kind ∧
        Served m t)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind) (hdelay : t0 ≤ ev.time)
    (hhor : ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + frontierSearch_remaining T G ΔF ρbar tail kind) ∨
    ∃ t, ev.time ≤ t ∧ t + tail ≤ ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ∧
      Served m t := by
  classical
  have hP := frontierSearch_period_bound T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hd := hT.delta_pos
  have hj : 0 ≤ E_jF T ΔF G ρbar := by
    unfold E_jF
    exact le_trans (by linarith) (le_max_right _ _)
  have go : ∀ n, ∀ {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind},
      2 - frontierSearch_phaseRank kind = n →
      FrontierSearchStart R E rho O T Jst i ev m kind → t0 ≤ ev.time →
      ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ≤ rho.horizon →
      FrontierRiseBy R E rho i m (ev.time + frontierSearch_remaining T G ΔF ρbar tail kind) ∨
      ∃ t, ev.time ≤ t ∧ t + tail ≤ ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ∧
        Served m t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i m ev kind hn hstart hdelay hhor
      have hfront := ((FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart).2.2.2.1
      have hb : interruptedRepairBudget T G ΔF ρbar kind + tail ≤
          frontierSearch_remaining T G ΔF ρbar tail kind := by
        cases kind <;> simp only [interruptedRepairBudget_gap_def,
          interruptedRepairBudget_topJ_def, interruptedRepairBudget_contest_def,
          frontierSearch_remaining_def, frontierSearch_phaseRank_gap_def,
          frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def,
          Nat.reduceEqDiff, ↓reduceIte] <;> linarith
      have hpHor : ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon := by
        linarith only [hb, hhor, htail]
      rcases step i ev m kind hstart hdelay hpHor with hphase | hrise | ⟨t, hwt, ht, hserved⟩
      · obtain ⟨j, nextEv, nextKind, hij, ht, hnext, hrank⟩ :=
          frontierSearch_phase_step_of_crossing (R := R) (E := E) (rho := rho) (O := O)
            (T := T) (Jst := Jst) (Ef := Ef) (obs := obs) (cert := cert) (inv := inv)
            (justif := justif) (keep := keep) crossing mono schedule hstart hphase
        have htime : ev.time ≤ nextEv.time := by
          obtain ⟨hi, _⟩ := (FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart
          obtain ⟨hjEv, _⟩ :=
            (FrontierSearchStart_def R E rho O T Jst j nextEv m nextKind).mp hnext
          obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
          obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjEv
          have hk := (List.pairwise_iff_getElem.mp schedule.sorted) i j hil hjl hij
          rw [hie, hje] at hk
          exact V2.D.Engine.time_le_of_key_le _ _ hk
        have hcost : nextEv.time + frontierSearch_remaining T G ΔF ρbar tail nextKind ≤
            ev.time + frontierSearch_remaining T G ΔF ρbar tail kind := by
          cases kind <;> cases nextKind <;>
            simp only [frontierSearch_phaseRank_gap_def, frontierSearch_phaseRank_topJ_def,
              frontierSearch_phaseRank_contest_def] at hrank <;>
            try omega
          all_goals simp only [interruptedRepairBudget_gap_def,
            interruptedRepairBudget_topJ_def] at ht
          all_goals simp only [frontierSearch_remaining_def, frontierSearch_phaseRank_gap_def,
            frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def,
            Nat.reduceEqDiff, ↓reduceIte]
          all_goals linarith only [ht, hj]
        have hmeasure : 2 - frontierSearch_phaseRank nextKind < n := by
          rw [← hn]
          cases kind <;> cases nextKind <;> simp only [frontierSearch_phaseRank_gap_def,
            frontierSearch_phaseRank_topJ_def, frontierSearch_phaseRank_contest_def] at * <;>
            omega
        rcases ih _ hmeasure rfl hnext (hdelay.trans htime) (hcost.trans hhor) with
            hr | ⟨t, hnt, ht, hserved⟩
        · left
          have hf :=
            ((FrontierSearchStart_def R E rho O T Jst j nextEv m nextKind).mp hnext).2.2.2.1
          exact frontierSearch_rise_mono R E rho hcost
            (frontierSearch_rise_rebase R E rho mono hij.le hf.le hr)
        · exact Or.inr ⟨t, htime.trans hnt, ht.trans hcost, hserved⟩
      · left
        exact frontierSearch_rise_mono R E rho (by linarith only [hb, htail])
          (frontierSearch_rise_of_stop R O E rho schedule hfront.le hrise)
      · exact Or.inr ⟨t, hwt, by linarith only [ht, hb], hserved⟩
  exact go _ rfl hstart hdelay hhor

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, finite phase composition.
DC: SAME gap and top J cannot repeat. A saved seed leaves the supplied tail budget.
Every phase result comes from its d5c consumer. The repair allowance at each actual
start after `Jst + 2P` is a leaf (FG-SA proves it for ρΓ and the guarded ρ₁). -/
theorem frontierSearch_phase_tail (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (crossing : RXing R E rho O) (schedule : V2.D.ScheduleWellFormed E rho)
    (mono : FGRunOrderLaws E rho R)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (joinedTick : ∀ iy y t, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
      joined (Prot.clock (rho.stateBefore E iy y) t) = true)
    (readyCut : ∀ t, Jst ≤ t → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V Prot.Object) m,
      rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
      PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
    (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
      W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF ρbar : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalService R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCovered R S E rho O.height T D.heightPair r Q ∧
      ((O.height Qfg).h = m - 1 → OpeningEntry R E rho O.height T r (m - 1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (O.height K).h = m))
    (heldSlot : ∀ i x A K, K ∈ (R.core (rho.stateBefore E i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot)
    (proposalSlot : ∀ q Q K, HonestProposal E rho I q Q → R.erase K = Q → K.slot = q)
    (justifiedSource : ∀ i x, x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ HonestRowAt S E rho T j y r a ∧
        actionSourceFG R E rho T y r = some (some K) ∧
        (O.height K).T_h = (R.core (rho.stateBefore E i x)).fg.J)
    (parentFrame : ∀ q Q, HonestProposal E rho I q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho I q) (T.proposal q)) ∧
      ∀ Qfg, R.erase Qfg = Q → FGBlock.Preceq
        (O.controls (rho.stateBefore E j (V2.D.proposerOf rho I q))).Z Qfg.parent)
    (allowance : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
      Jst + 2 * FGCompose.P T ≤ ev.time →
      FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta))
    (tail : Time) (htail : 0 ≤ tail)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hdelay : Jst + 2 * FGCompose.P T ≤ ev.time)
    (hhor : ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + frontierSearch_remaining T G ΔF ρbar tail kind) ∨
    ∃ t, ev.time ≤ t ∧ t + tail ≤ ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ∧
      StrongServed R S E rho O T I D.heightPair Jst leaseSlots m t := by
  refine frontierSearch_phase_compose (R := R) (O := O) (T := T) (E := E) (rho := rho)
    (Ef := Ef) (Jst := Jst) (obs := obs) (cert := cert) (inv := inv) (justif := justif)
    (keep := keep) hT crossing schedule mono
    (StrongServed R S E rho O T I D.heightPair Jst leaseSlots) hG
    (allowance i ev m kind hstart hdelay).1 htail ?_ hstart hdelay hhor
  intro i ev m kind hst hdl hph
  have hal := allowance i ev m kind hst hdl
  have res : FrontierHG3Result R S E rho O T I D.heightPair Jst leaseSlots i m ev.time
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) := by
    cases kind with
    | gap =>
      exact frontier_hg3_gap (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
        (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
        (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
        (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
        (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
        (inv := inv) (justif := justif) (keep := keep) (positive := positive)
        (coreLaws := coreLaws) (erasePreceq := erasePreceq) (joined := joined)
        (receipt := receipt) hT hk crossing schedule mono awake joinedTick readyCut
        hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal read
        order signer sourceParent hδ hbound rowsReceipt progressCoverage hfold
        honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect floor gateCopy
        service common heldSlot proposalSlot hst hal hph
    | topJ =>
      exact frontier_hg3_topJ (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
        (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
        (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
        (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
        (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
        (inv := inv) (justif := justif) (keep := keep) (positive := positive)
        (coreLaws := coreLaws) (erasePreceq := erasePreceq) (joined := joined)
        (receipt := receipt) hT hk crossing schedule mono awake joinedTick readyCut
        hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal read
        order signer sourceParent hδ hbound rowsReceipt progressCoverage hfold
        honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect floor gateCopy
        service common justifiedSource parentFrame hst hal hph
    | contest =>
      exact frontier_hg3_contest (R := R) (S := S) (E := E) (rho := rho) (O := O) (T := T)
        (I := I) (pair := D.heightPair) (Jst := Jst) (leaseSlots := leaseSlots) (Ef := Ef)
        (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
        (positive := positive) (coreLaws := coreLaws) (erasePreceq := erasePreceq)
        (joined := joined) (receipt := receipt) hT hk crossing schedule mono hdelta hJst
        awake joinedTick readyCut hServices receiptHeld hG floor gateCopy service hst hal hph
  exact (FrontierHG3Result_def R S E rho O T I D.heightPair Jst leaseSlots i m ev.time _).mp res

end AvailableChain.FGCompose
end
