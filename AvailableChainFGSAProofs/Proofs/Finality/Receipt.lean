module
public import AvailableChainFGSAProofs.Proofs.Finality.Carry
public import AvailableChainFGSAProofs.Proofs.Finality.Rows
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSAClaims.Statements.FinalityApi
public import AvailableChainFGSAClaims.Statements.Packages.Safety

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Window (CoveredW)
open Gen.V2.Duty (faulty)

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Paper 22:1286–1305: the kernel supplies the execution, fault bound and horizon.
DC: INTENTIONAL local W deadline, with separate row delay and no GST healing bound. -/
theorem receipt_kernel_fields (G ΔF : Time) (pt : KernelPt)
    (h : KernelPrem_W p c G ΔF E rho pt) :
    BaseSet p c E rho ∧ (faulty rho).card ≤ (p.n - 1) / 3 ∧
      kernelDeadlineW p ΔF (pt.r + 2) ≤ rho.horizon :=
  ⟨h.set.base, h.set.fault, h.hhor⟩

/-- Paper 22:1286–1289: carriage gives a finalized descendant in both branches.
DC: INTENTIONAL greatest-ready W fold; prior coverage is a separate branch.
The fold proves only carrier finality. It does not prove receipt or guards. -/
theorem receipt_finalized_of_carriage (hsel : TRowsSelect p c E rho)
    (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin p.n))
    (hne : X ≠ .genesis) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X) :
    FGBlock.Preceq U (Window.derive p p.K_W X).F := by
  rcases terminalCarriage_W_of_tRowsSelect p c E rho hsel ΔF q y A U X h with
      hcovered | ⟨_hvalid, hcover⟩
  · exact ((Window.CoveredW_def p X y U).mp (covered_parent_W p y U X hcovered)).2
  · exact (pendingFold_consume_W p y U X ⟨hne, hcover⟩).1

private theorem receipt_finality (X : FGBlock (Fin p.n)) :
    (finalityView p X).F = (Window.derive p p.K_W X).F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def]

omit [DecidableEq V] [Fintype V] in
private theorem receipt_eventTime (i : Nat) :
    eventTime rho i = rho.events[i]?.map V2.Event.time := rfl

omit [Fintype V] in
private theorem receipt_stored_block (i : Nat) (x : V) (C : FGBlock (Fin p.n))
    (hC : C ∈ (storeAt p c E rho i x).fg.TF) (hne : C ≠ .genesis) :
    FinalityBlock p c E rho C := by
  obtain ⟨wire, ⟨hwire, hblock⟩, _hunique⟩ :=
    (storeBundle_stateBefore E rho i x).meta.treeWire C hC hne
  obtain ⟨j, o, t, _hji, he, hto, ⟨s, b, raw, sup, rows, hp, ha⟩, _hr⟩ :=
    stored_proposal_delivered E rho i x wire hwire
  have hw : wire = ⟨.proposer s, .proposal b raw sup rows⟩ := by
    rw [← hto]
    change (⟨toAuth p o.auth, o.payload⟩ : Wire p.n) = _
    rw [hp, ha]
    rfl
  rw [hw] at hblock
  have hb : b = eraseFG C := Option.some.inj hblock
  rw [FinalityBlock_def]
  exact ⟨o, b, raw, sup, rows, hp, Or.inr ⟨x, t, List.mem_of_getElem? he⟩,
    hb ▸ Gen.Pure.block_preceq_refl _⟩

omit [Fintype V] in
private theorem receipt_ready_block (i : Nat) (x : V) (X : FGBlock (Fin p.n))
    (t : Time) (hready : Ready_W p c E rho i x X t) : FinalityBlock p c E rho X := by
  obtain ⟨o, s, raw, sup, rows, P, he, hd, _hp, _ha, _hX⟩ :=
    (Ready_W_def p c E rho i x X t).mp hready
  have hp := congrArg Signed.payload (decode_eq_block.mp hd)
  change o.payload = Msg.proposal (eraseFG X) raw sup rows at hp
  rw [FinalityBlock_def]
  exact ⟨o, eraseFG X, raw, sup, rows, hp,
    Or.inr ⟨x, t, List.mem_of_getElem? he⟩, Gen.Pure.block_preceq_refl _⟩

/-- Paper 22:1145–1146, 1296: I3 compares F before carrier admission.
DC: INTENTIONAL W certificate agreement. Assembly supplies I3 from Foundations;
the honest emission supplies the carrier block before Ready exists. -/
theorem receipt_finCmp_of_block (base : BaseSet p c E rho)
    (faultBound : (faulty rho).card ≤ (p.n - 1) / 3)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (i : Nat) (x : V) (X U : FGBlock (Fin p.n))
    (hfinal : FGBlock.Preceq U (Window.derive p p.K_W X).F)
    (hblock : FinalityBlock p c E rho X) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F U ∨
      FGBlock.Preceq U (storeAt p c E rho i x).fg.F := by
  obtain ⟨C, hC, hCF⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.Fcar
  change (finalityView p C).F = (storeAt p c E rho i x).fg.F at hCF
  by_cases hgen : C = .genesis
  · subst C
    have hF : (storeAt p c E rho i x).fg.F = .genesis := by
      rw [← hCF, receipt_finality]
      rfl
    exact Or.inl (hF ▸ KitFG.genesis_preceq U)
  have hc := hI3 ⟨base, faultBound⟩ C X _ _ _ _
    (receipt_stored_block p c E rho i x C hC hgen)
    hblock
    ((FinalityFinalizedAt_def p C _ _).mpr ⟨hCF, rfl⟩)
    ((FinalityFinalizedAt_def p X _ _).mpr ⟨receipt_finality p X, rfl⟩)
  rcases Bool.or_eq_true_iff.mp hc with hbelow | habove
  · exact KitFG.preceq_total_of_common hbelow hfinal
  · exact Or.inr (KitFG.preceq_trans hfinal habove)

/-- Paper 22:1145–1146, 1296: I3 compares F at this same Ready event.
DC: INTENTIONAL W certificate agreement. Assembly supplies I3 from Foundations;
the Finality lane uses only its explicit safety-premise supplier. -/
theorem receipt_finCmp (base : BaseSet p c E rho)
    (faultBound : (faulty rho).card ≤ (p.n - 1) / 3)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (i : Nat) (x : V) (X U : FGBlock (Fin p.n)) (t : Time)
    (hfinal : FGBlock.Preceq U (Window.derive p p.K_W X).F)
    (hready : Ready_W p c E rho i x X t) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F U ∨
      FGBlock.Preceq U (storeAt p c E rho i x).fg.F := by
  exact receipt_finCmp_of_block p c E rho base faultBound hI3 i x X U hfinal
    (receipt_ready_block p c E rho i x X t hready)

omit [Fintype V] in
/-- Paper 22:1290–1302: the pre-next-action cap bounds the inserted h_max.
DC: INTENTIONAL W receipt insert, with height views and the shared causal cap.
The receiver and carrier use the same selected event index. -/
theorem receipt_cap (ΔF : Time) (q y i : Nat) (x : V) (X : FGBlock (Fin p.n))
    (t : Time) (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hv : V2.D.ExecutionValid E rho)
    (hheight : y + 1 ≤ (heightView p X).h)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (q + 1) → h ≤ y + 1) :
    (receiptInsert_W p c E rho i x X).h_max ≤ (heightView p X).h + 1 := by
  have hnext := (KernelBeforeNextActionW_def p ΔF q).mp
    (kernel_before_next_actionW p ΔF q hbound)
  have htime : ∃ e, rho.events[i]? = some e ∧ e.time = t := by
    rw [receipt_eventTime] at ht
    exact Option.map_eq_some_iff.mp ht
  obtain ⟨e, he, htime⟩ := htime
  have hi : i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)) := by
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hv.toScheduleWellFormed he
      (p.actionTime (q + 1))).mpr (htime ▸ hbefore.trans hnext)
    exact Nat.le_of_lt hlt
  have hcap : ∀ W ∈ (storeAt p c E rho i x).fg.TF, (heightView p W).h ≤ y + 2 := by
    intro W hW
    exact actual_anchor_cap p c E rho q y hcapBefore hrows i x W hi ⟨hx, hW⟩
  have hmax := (storeBundle_stateBefore E rho i x).cstore.fg.hmax
  change (storeAt p c E rho i x).fg.h_max =
    (storeAt p c E rho i x).fg.TF.sup (fun W => (heightView p W).h) ⊔ 1 at hmax
  have hm : (storeAt p c E rho i x).fg.h_max ≤ y + 2 := by
    rw [hmax]
    exact max_le (Finset.sup_le hcap) (Nat.succ_le_succ (Nat.zero_le (y + 1)))
  rw [receiptInsert_W_def]
  change max (storeAt p c E rho i x).fg.h_max (heightView p X).h ≤ (heightView p X).h + 1
  exact max_le (hm.trans (Nat.add_le_add_right hheight 1)) (Nat.le_succ _)

omit [Fintype V] in
/-- Paper 22:1294–1296: the separate finality lag excludes a higher receiver certificate.
DC: INTENTIONAL W F carrier at the pre-handler read; Assembly supplies finality lag.
This height bound does not produce delivery or cached-J source provenance. -/
theorem receipt_receiver_finalityLag (ΔF : Time) (q y i : Nat) (x : V) (t : Time)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hv : V2.D.ExecutionValid E rho)
    (hfinalityLag : ∀ (r k j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      0 < k → j ≤ V2.D.Run.idxBefore rho (p.actionTime (r + 1)) →
      HeldAt p c E rho j z W →
      (∀ l u s a row T timeout, HonestRowAt p c E rho l u s a →
        RowWire.toRow? a = some row → row.height_pair = .vote k T timeout →
        ¬ p.actionTime s < p.actionTime r) → (finalityView p W).h_F < k)
    (hrowsEarlier : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime q → h < y + 1) :
    ∃ C, HeldAt p c E rho i x C ∧
      (finalityView p C).F = (storeAt p c E rho i x).fg.F ∧
      (finalityView p C).h_F < y + 1 := by
  have hnext := (KernelBeforeNextActionW_def p ΔF q).mp
    (kernel_before_next_actionW p ΔF q hbound)
  have htime : ∃ e, rho.events[i]? = some e ∧ e.time = t := by
    rw [receipt_eventTime] at ht
    exact Option.map_eq_some_iff.mp ht
  obtain ⟨e, he, htime⟩ := htime
  have hi : i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)) := by
    exact Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hv.toScheduleWellFormed he
      (p.actionTime (q + 1))).mpr (htime ▸ hbefore.trans hnext))
  obtain ⟨C, hC, hCF⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.Fcar
  have hheld : HeldAt p c E rho i x C := ⟨hx, hC⟩
  refine ⟨C, hheld, hCF, hfinalityLag q (y + 1) i x C (Nat.zero_lt_succ _) hi hheld ?_⟩
  intro j z r a row T timeout ha hd hp hlt
  exact (Nat.lt_irrefl _) (hrowsEarlier j z r a row (y + 1) T timeout ha hd hp hlt)

omit [Fintype V] in
/-- Paper 22:1297–1302: the h_j = y case has its cached anchor on the carrier path.
DC: INTENTIONAL W cached-J guard. This does not produce source provenance;
Per-height justification uniqueness must prove the cached equality in this case. -/
theorem receipt_jPath_of_cached_anchor (i : Nat) (x : V) (X U : FGBlock (Fin p.n))
    (hcached : (storeAt p c E rho i x).fg.J = U) (hpath : FGBlock.Preceq U X.parent) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.J X ∨
      (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j := by
  have hp : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node P s body rows => exact KitFG.preceq_parent_node P s body rows
  exact Or.inl (hcached ▸ KitFG.preceq_trans hpath hp)

private theorem receipt_parent_path (X : FGBlock (Fin p.n)) : FGBlock.Preceq X.parent X := by
  cases X with
  | genesis => exact KitFG.preceq_refl _
  | node P s body rows => exact KitFG.preceq_parent_node P s body rows

private theorem receipt_proposal_checks (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    FGSA.wellFormed p ⟨.proposer s, .proposal b raw support rows⟩ =
      (b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
        raw.all (fun v => match v.decode? with
          | some (r, _, _) => r + 1 == b.slot
          | none => false) &&
        support.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
        rowsOk b rows) := rfl

/-- Paper 22:1294–1296, 995–1002: a checked delivery admits the actual carrier.
DC: INTENTIONAL selected W handler; R6 checks every carried row against its parent. -/
theorem receipt_ready_of_delivery (G ΔF : Time) (hrec : Recovery₂ p c E rho G ΔF)
    (i : Nat) (x : V) (X : FGBlock (Fin p.n)) (t : Time)
    (o : Obj p) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (he : rho.events[i]? = some (.deliver x o t))
    (hd : (toWire p o).decode = some (.block X.slot (eraseFG X) raw sup rows))
    (htrigger : Gen.V2.Duty.Trigger E rho o (SA.proposalTime p.toParams X.slot))
    (ht : SA.proposalTime p.toParams X.slot ≤ t)
    (hF : FGBlock.Preceq (storeAt p c E rho i x).fg.F X) :
    Ready_W p c E rho i x X t := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hD := hrec.base.valid.toDeliveryWellFormed
  have hwf := hD.wire i x o t he
  change FGSA.wellFormed p (toWire p o) = true at hwf
  have hw := decode_eq_block.mp hd
  have hwf' : FGSA.wellFormed p ⟨.proposer X.slot,
      .proposal (eraseFG X) raw sup rows⟩ = true := hw ▸ hwf
  have hdeps := hD.deps i x o t he
  change depsS p (storeAt p c E rho i x) o = true at hdeps
  dsimp only [depsS] at hdeps
  rw [hd] at hdeps
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hdeps
  have hPe := ((FGSA.parentFG_spec _ (FGSA.rootInj_all _) _ P).mp hP).2
  have hchecks := hwf'
  rw [receipt_proposal_checks] at hchecks
  simp only [Bool.and_eq_true] at hchecks
  obtain ⟨⟨⟨⟨⟨⟨hb, _hs⟩, _hps⟩, _hraw⟩, _hsup⟩, _hrvalid⟩, hok⟩ := hchecks
  have hbne : eraseFG X ≠ .genesis := by simpa using hb
  have hparent : eraseFG X.parent = (eraseFG X).parent := by
    cases X with
    | genesis => rfl
    | node P s body rs => rfl
  have hPX : P = X.parent := FGSA.eraseFG_injective (hPe.trans hparent.symm)
  subst P
  have hX : FGSA.fgBlock X.parent (eraseFG X) rows = X :=
    FGSA.eraseFG_injective (FGSA.eraseFG_fgBlock hbne hparent rows hok)
  have hvalid := fgsa_trigger_rowsValid E rho o _ X.slot (eraseFG X) raw sup rows
    htrigger hd (storeAt p c E rho i x) X.parent hP
  have hfresh := hD.fresh i x o t he
  change processedS p (storeAt p c E rho i x) o = false at hfresh
  dsimp only [processedS] at hfresh
  rw [hd] at hfresh
  have htime : 0 ≤ SA.proposalTime p.toParams X.slot := by
    change 0 ≤ 4 * p.Δ * (X.slot : Int)
    exact mul_nonneg (mul_nonneg (by decide) (le_of_lt p.deltaPos)) (Int.natCast_nonneg _)
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams X.slot) := by
    refine ⟨4 * X.slot, ?_⟩
    change 4 * p.Δ * (X.slot : Int) = _
    rw [hrec.base.delta]
    push_cast
    ring
  have hx := hS.honest_only _ (List.mem_of_getElem? he)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hS.tick_total x hx _ hpub htime
    (ht.trans (hS.in_horizon _ (List.mem_of_getElem? he)).2))
  have hij := V2.D.Engine.tick_index_lt_delivery E rho hS hj he ht
  have ho : o = ofWire p ⟨.proposer X.slot, .proposal (eraseFG X) raw sup rows⟩ := by
    apply toWire_injective
    rw [toWire_ofWire]
    exact hw
  have htimely := Gen.V2.Duty.timely_of_clock E rho (fgsaTimelyClock p c) hS x o
    (SA.proposalTime p.toParams X.slot) j i (by
      rw [fgsaTimelyClock_actTime p c o]
      rw [ho]
      exact le_rfl) hj hij (hrec.base.noRestart.restartFree x j i)
  have hslot : (eraseFG X).slot ≤ (storeAt p c E rho i x).slot p := by
    rw [ho] at htimely
    change 4 * p.Δ * (X.slot : Int) ≤ (storeAt p c E rho i x).base.now at htimely
    rw [FGSA.eraseFG_slot]
    exact (fgsa_slot_threshold_iff p _ (htime.trans htimely) X.slot).mpr htimely
  have hacc : FGSA.blockAccepted p (storeAt p c E rho i x) X.slot
      (eraseFG X) X.parent rows = true := by
    rw [FGSA.blockAccepted_of_wellFormed p _ _ _ raw sup rows _ hwf', hX]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨⟨⟨hslot, of_decide_eq_false hfresh⟩, hF⟩, hvalid⟩
  exact (Ready_W_def p c E rho i x X t).mpr ⟨o, X.slot, raw, sup, rows, X.parent,
    he, hd, hP, hacc, hX⟩

omit [Fintype V] in
private theorem receipt_carrier_eq (s : Slot) (B : Block) (rows : List (RowWire p.n)) :
    HonestCarrier p c E rho s B rows =
      (HonestProposal E rho (fgsaInterface p c) s B ∧
        ∃ o raw sup, V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
          (V2.D.proposalTime (fgsaInterface p c) s) ∧ o.payload = .proposal B raw sup rows) := rfl

omit [Fintype V] in
private theorem receipt_proposer_honest (s : Slot) (B : Block)
    (h : HonestProposal E rho (fgsaInterface p c) s B) :
    V2.D.proposerOf rho (fgsaInterface p c) s ∈ rho.honest := by
  exact ((Gen.V2.Duty.HonestSlot_def rho (fgsaInterface p c) s).mp h.1).2

/-- Paper 22:1294–1296: I3 and C1 give a selected covered-or-admitted event.
DC: INTENTIONAL W delivery with strict broadcast time and dependency admission.
The fold supplies only hfinal; it does not supply delivery or guards. -/
theorem receipt_delivery (G ΔF : Time) (hrec : Recovery₂ p c E rho G ΔF)
    (X U : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hcarrier : HonestCarrier p c E rho X.slot (eraseFG X) rows)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot)
    (hhor : SA.proposalTime p.toParams X.slot + p.Δ ≤ rho.horizon)
    (hfinal : FGBlock.Preceq U (Window.derive p p.K_W X).F)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true) :
    Nonempty (BlockDelivery_W p c E rho X U (SA.proposalTime p.toParams X.slot)
      (SA.proposalTime p.toParams X.slot + p.Δ)) := by
  classical
  obtain ⟨hproposal, o, raw, sup, hem, hpayload⟩ :=
    (receipt_carrier_eq p c E rho _ _ rows).mp hcarrier
  change Obj p at o
  have hhon := receipt_proposer_honest p c E rho _ _ hproposal
  have hd : (toWire p o).decode = some (.block X.slot (eraseFG X) raw sup rows) := by
    obtain ⟨j, hj, ho⟩ := hem
    change rho.events[j]? = some (.tick
      (V2.D.proposerOf rho (fgsaInterface p c) X.slot) (SA.proposalTime p.toParams X.slot)) at hj
    have hawake : E.awake (V2.D.proposerOf rho (fgsaInterface p c) X.slot)
        (SA.proposalTime p.toParams X.slot) = true := by
      exact hrec.awake _ hhon _ hgst
        ((le_of_lt (lt_add_of_pos_right _ p.deltaPos)).trans hhor)
    have hwf := honest_emit_wellFormed E rho hrec.base.valid.toDeliveryWellFormed
      hrec.base.valid.toScheduleWellFormed j _ _ hj hhon hawake o ho
    change FGSA.wellFormed p (toWire p o) = true at hwf
    cases o with
    | mk auth payload =>
      dsimp only at hpayload
      subst payload
      cases auth with
      | none => cases hwf
      | seat label seat =>
        cases label with
        | base label => cases label <;> cases hwf
        | prop s =>
          change FGSA.wellFormed p ⟨.proposer s, .proposal (eraseFG X) raw sup rows⟩ = true at hwf
          rw [receipt_proposal_checks] at hwf
          simp only [Bool.and_eq_true] at hwf
          have hs := beq_iff_eq.mp hwf.1.1.1.1.1.2
          rw [FGSA.eraseFG_slot] at hs
          subst s
          rfl
  have htrigger : Gen.V2.Duty.Trigger E rho o (SA.proposalTime p.toParams X.slot) :=
    Or.inl ⟨_, hhon, hem⟩
  have hblock : FinalityBlock p c E rho X := by
    rw [FinalityBlock_def]
    exact ⟨o, eraseFG X, raw, sup, rows, hpayload, Or.inl ⟨_, _, hem⟩,
      Gen.Pure.block_preceq_refl _⟩
  let a := SA.proposalTime p.toParams X.slot
  let D := a + p.Δ
  have hdelay : max a E.t_GST + fgsaDelay E.Δ ΔF o = D := by
    rw [max_eq_left hgst]
    have heq : fgsaDelay E.Δ ΔF o = p.Δ := by
      rw [fgsaDelay_def, hpayload, hrec.base.delta]
    rw [heq]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hFD : FGBlock.Preceq (Window.derive p p.K_W X).F X := by
    rw [← receipt_finality]
    exact KitFG.preceq_trans ((fgCertificateLaws p).finalized_preceq_justified X)
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry X)
        ((fgCertificateLaws p).height.entry_preceq X))
  have hwitness : ∀ x ∈ rho.honest, ∃ i t,
      eventTime rho i = some t ∧ t < D ∧
      (FGBlock.Preceq U (storeAt p c E rho (i + 1) x).fg.F ∨
        (a ≤ t ∧ Ready_W p c E rho i x X t)) := by
    intro x hx
    have hread := Gen.V2.Duty.stateBefore_idxBefore E rho D hS
    have hcmp := receipt_finCmp_of_block p c E rho hrec.base hrec.fault hI3
      (V2.D.Run.idxBefore rho D) x X U hfinal hblock
    by_cases hcovered : FGBlock.Preceq U
        (storeAt p c E rho (V2.D.Run.idxBefore rho D) x).fg.F
    · have hapos : 0 ≤ a := by
        change 0 ≤ 4 * p.Δ * (X.slot : Int)
        exact mul_nonneg (mul_nonneg (by decide) (le_of_lt p.deltaPos)) (Int.natCast_nonneg _)
      have hpub : V2.PublicTime E a := by
        refine ⟨4 * X.slot, ?_⟩
        change 4 * p.Δ * (X.slot : Int) = _
        rw [hrec.base.delta]
        push_cast
        ring
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
        (hS.tick_total x hx a hpub hapos ((le_of_lt (lt_add_of_pos_right a p.deltaPos)).trans hhor))
      have hjD := (Gen.V2.Duty.index_lt_idxBefore_iff hS hj D).mpr
        (by change a < a + p.Δ; exact lt_add_of_pos_right _ p.deltaPos)
      have hlen : V2.D.Run.idxBefore rho D ≤ rho.events.length := by
        rw [V2.D.Run.idxBefore_def]
        exact List.length_filter_le ..
      have hn : 0 < V2.D.Run.idxBefore rho D := by omega
      let i := V2.D.Run.idxBefore rho D - 1
      have hil : i < rho.events.length := by dsimp only [i]; omega
      have he := List.getElem?_eq_getElem hil
      refine ⟨i, rho.events[i].time, ?_, ?_, Or.inl ?_⟩
      · rw [receipt_eventTime, he]
        rfl
      · exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mp (by dsimp only [i]; omega)
      · have hi : i + 1 = V2.D.Run.idxBefore rho D := by dsimp only [i]; omega
        rwa [hi]
    · have hFU := hcmp.resolve_right hcovered
      have hFX : FGBlock.Preceq (storeAt p c E rho (V2.D.Run.idxBefore rho D) x).fg.F X :=
        KitFG.preceq_trans hFU (KitFG.preceq_trans hfinal hFD)
      have hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho D x) o = false := by
        change excludesS p (V2.D.Run.stateBeforeTime E rho D x).st o = false
        have hc : Block.compatible (eraseFG X)
            (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) = true := by
          rw [← hread]
          exact Bool.or_eq_true_iff.mpr (Or.inr (FGSA.eraseFG_preceq hFX))
        dsimp only [excludesS]
        rw [hd]
        simp only [blockExcluded, activeCompatible, hc, Bool.not_true, Bool.false_or]
        exact fgsa_trigger_invalid_false E rho o a X.slot (eraseFG X) raw sup rows
          htrigger hd _
      obtain ⟨t, hat, htD, i, envelope, he, hh⟩ := hrec.sync.broadcast_emitted _ hhon o a hem
        x hx (hdelay ▸ hhor) (hdelay ▸ hNX)
      have hdirect : envelope = o := by
        rcases hh with h | h
        · exact h
        · cases hd' : (toWire p envelope).decode with
          | none => simp only [hd'] at h
          | some m =>
            cases m with
            | vote => simp only [hd'] at h
            | row => simp only [hd'] at h
            | block s b rs sp ws =>
              rw [hd'] at h
              rcases h.2 with h | h
              · obtain ⟨wire, _, hw⟩ := List.mem_map.mp h
                have hdw := congrArg Wire.decode (congrArg (toWire p) hw)
                rw [toWire_ofHead, hd] at hdw
                cases wire with
                | mk auth body =>
                  rcases auth with (⟨(_ | _), _⟩ | _ | _) <;> simp [Wire.decode] at hdw
              · obtain ⟨wire, _, hw⟩ := List.mem_map.mp h
                have hdw := congrArg Wire.decode (congrArg (toWire p) hw)
                rw [toWire_ofRow, hd] at hdw
                cases wire with
                | mk auth body =>
                  rcases auth with (⟨(_ | _), _⟩ | _ | _) <;> simp [Wire.decode] at hdw
      subst envelope
      have htD' : t < D := hdelay ▸ htD
      have hiD := (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mpr htD'
      have hmono := fgsa_monoAlong_preceq_F p c (storeAt p c E rho i x).fg.F
      rw [Gen.V2.Duty.MonoAlong_def] at hmono
      have hFF := V2.D.Engine.stateBefore_stable _ hmono.1 hmono.2.1 hmono.2.2 E rho
        (Nat.le_of_lt hiD) x (hrec.base.noRestart.restartFree x i _) (KitFG.preceq_refl _)
      have hFiX := KitFG.preceq_trans hFF hFX
      refine ⟨i, t, ?_, htD', Or.inr ⟨hat, ?_⟩⟩
      · rw [receipt_eventTime, he]
        rfl
      · exact receipt_ready_of_delivery p c E rho G ΔF hrec i x X t o raw sup rows
          he hd htrigger hat hFiX
  choose index time witness using hwitness
  exact ⟨{ selected := fun x hx => ⟨index x hx, time x hx⟩, witness := witness }⟩

omit [DecidableEq V] [Fintype V] in
private theorem receipt_height_hj (X : FGBlock (Fin p.n)) :
    (heightView p X).h_j = (Window.derive p p.K_W X).h_j := by
  simp only [heightView_def, Window.projectHeight_def]

private theorem receipt_height_genesis :
    (heightView p (.genesis : FGBlock (Fin p.n))).h = 1 := by
  rw [heightView_def, Window.derive_def, Window.projectHeight_def, Window.initial_def]

omit [DecidableEq V] [Fintype V] in
private theorem receipt_actionTime_strictMono : StrictMono p.actionTime := by
  intro a b hab
  have hab' : (a : Int) < b := by exact_mod_cast hab
  have hR : (0 : Int) < p.R := by exact_mod_cast (show 0 < p.R by have := p.RLarge; omega)
  have hpos : (0 : Int) < 4 * p.Δ * (p.R : Int) :=
    mul_pos (mul_pos (by decide) p.deltaPos) hR
  change 4 * p.Δ * ((a * p.R : Nat) : Int) + 6 * p.Δ <
    4 * p.Δ * ((b * p.R : Nat) : Int) + 6 * p.Δ
  push_cast
  convert add_lt_add_right (mul_lt_mul_of_pos_left hab' hpos) (6 * p.Δ) using 1 <;> ring

omit [Fintype V] in
private theorem receipt_mu_eq : muOf p c E rho = max 1 (sSup (oldRowHeights p c E rho)) := rfl

private theorem receipt_high_eq (w : HealingWitness) (X : FGBlock (Fin p.n)) :
    high p w X = (w.M + 1 ≤ (heightView p X).h) := rfl

/-- Paper 22:1297–1302: a high cached J is on the terminal carrier path.
DC: INTENTIONAL W cached pair and action-source ancestry. Stratification and
emitted-name provenance are explicit Foundations inputs; H2 supplies the path. -/
theorem receipt_jPath (ΔF : Time) (q y i : Nat) (x : V) (A U X : FGBlock (Fin p.n))
    (t : Time) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X)
    (w : HealingWitness) (hinput : HealingInput p c E rho w ΔF)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hslot : X.slot = q * p.R + kappaF p ΔF)
    (hanchor : (heightView p A).h_j = y) (hfloor : w.M + 1 ≤ y)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.J X ∨
      (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j := by
  by_cases hstrict : (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j
  · exact Or.inr hstrict
  have hXj : y ≤ (Window.derive p p.K_W X).h_j := by
    have hm := Window.window_hj_mono p p.K_W p.kWLarge A X
      (KitFG.preceq_trans h.path (receipt_parent_path p X))
    rw [← receipt_height_hj, hanchor] at hm
    exact hm
  obtain ⟨C, hC, _hFC, hCJ, hJ⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.pair.1
  change (storeAt p c E rho i x).fg.h_j = (heightView p C).h_j at hCJ
  have hCpos : (heightView p C).h_j ≠ 0 := by
    simp only [Height] at hCJ hXj hfloor hstrict ⊢
    omega
  have hJheight := (fgJustificationLaws p).J_height C hCpos
  have hJne : (heightView p C).J ≠ .genesis := by
    intro hg
    rw [hg] at hJheight
    have hz : (heightView p C).h_j = 1 :=
      hJheight.symm.trans (receipt_height_genesis p)
    have hmu := hinput.wit.mu_le
    rw [receipt_mu_eq] at hmu
    have hM : 1 ≤ w.M := (le_max_left 1 _).trans hmu
    simp only [Height] at hCJ hXj hfloor hstrict hz ⊢
    omega
  have hcert : (heightView p C).J ∈ certified p C := by
    rw [certified_def]
    exact ⟨C, KitFG.preceq_refl _, Or.inl rfl⟩
  obtain ⟨u, r, a, hrowBefore, hnames⟩ := hStrat i x C hx hC _ hcert hJne
  obtain ⟨j, hji, hrow⟩ := (HonestRowBefore_def p c E rho i u r a).mp hrowBefore
  obtain ⟨S, hsource, hentry, hJS⟩ := hEmittedSource j u r a _ hrow hnames
  have hJeq : (heightView p C).J = (heightView p S).T_h :=
    FGBlock.root_injective (congrArg Prod.snd hentry)
  have hhigh : high p w S := by
    rw [receipt_high_eq]
    have hheight := congrArg Prod.fst hentry
    simp only [Height] at hCJ hXj hfloor hstrict hJheight hheight ⊢
    omega
  have hnext := (KernelBeforeNextActionW_def p ΔF q).mp
    (kernel_before_next_actionW p ΔF q hbound)
  rw [receipt_eventTime] at ht
  obtain ⟨e, he, htime⟩ := Option.map_eq_some_iff.mp ht
  have hi : i < V2.D.Run.idxBefore rho (p.actionTime (q + 1)) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed he _).mpr
      (htime ▸ hbefore.trans hnext)
  have hrtime := (Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed
    hrow.2.1 _).mp (hji.trans hi)
  have hrq : r ≤ q := Nat.le_of_lt_succ ((receipt_actionTime_strictMono p).lt_iff_lt.mp hrtime)
  obtain ⟨rows, hcarrier, _⟩ := h.carrier
  have hproposal := ((receipt_carrier_eq p c E rho _ _ rows).mp hcarrier).1
  have hFpos := E.Δ_pos.trans_le h.deltaF
  have hk := kappaF_ge_two p ΔF (le_of_lt hFpos)
  have hlabel : r * p.R + 2 ≤ X.slot := by
    rw [hslot]
    exact Nat.add_le_add (Nat.mul_le_mul_right p.R hrq) hk
  have hbasepath := hinput.t.h2 u r S X.slot (eraseFG X) hrow.1 hsource hhigh hproposal hlabel
  rw [FGSA.eraseFG_parent] at hbasepath
  have hpath : FGBlock.Preceq S X.parent :=
    FGSA.preceq_of_eraseFG_preceq (KitFG.viewRootInj_all {S, X.parent})
      ⟨S, by simp, KitFG.preceq_refl _⟩ ⟨X.parent, by simp, KitFG.preceq_refl _⟩ hbasepath
  exact Or.inl (hJ.trans hJeq ▸ KitFG.preceq_trans hJS
    (KitFG.preceq_trans hpath (receipt_parent_path p X)))

/-- Paper 22:1286–1305: the terminal carrier gives every AcceptPrem_W field.
DC: INTENTIONAL local W receipt and same-event guards. The final action is
q = pt.r + 2; Assembly supplies the stated Foundations and K-MID inputs. -/
theorem receipt_acceptPrem_W (G ΔF : Time) (pt : KernelPt)
    (hkernel : KernelPrem_W p c G ΔF E rho pt) (y : Nat) (A U X : FGBlock (Fin p.n))
    (h : TerminalCarriagePrem_W p c E rho ΔF (pt.r + 2) y A U X)
    (hslot : X.slot = (pt.r + 2) * p.R + kappaF p ΔF)
    (hne : X ≠ .genesis) (hsel : TRowsSelect p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hanchor : (heightView p A).h_j = y) (hfloor : pt.w.M + 1 ≤ y)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (pt.r + 2 + 1) → h ≤ y + 1) :
    Nonempty (AcceptPrem_W p c E rho X U (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF (pt.r + 2))) := by
  have hdeadline : SA.proposalTime p.toParams X.slot + p.Δ =
      kernelDeadlineW p ΔF (pt.r + 2) := by
    rw [hslot, ← fgsa_grid_sa_proposalTime, fgsa_grid_carrier_timeW,
      carrierTimeW_def, kernelDeadlineW_def]
  have hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot := by
    have hFpos := E.Δ_pos.trans_le h.deltaF
    have hmax := le_max_right (p.actionTime (pt.r + 2)) E.t_GST
    have hhor := h.horizon.1
    simp only [Time] at hmax hhor hFpos ⊢
    omega
  have hfinal := receipt_finalized_of_carriage p c E rho hsel ΔF (pt.r + 2) y A U X hne h
  obtain ⟨rows, hcarrier, _⟩ := h.carrier
  obtain ⟨delivery⟩ := receipt_delivery p c E rho G ΔF hkernel.set X U rows hcarrier hgst
    (hdeadline ▸ hkernel.hhor) hfinal hI3
  rw [hdeadline] at delivery
  have hheight : y + 1 ≤ (heightView p X).h := by
    rw [← h.freshHeight]
    exact (fgCertificateLaws p).height.h_mono
      (KitFG.preceq_trans h.path (receipt_parent_path p X))
  refine ⟨{ base := hkernel.set.base
            faultBound := hkernel.set.fault
            finalized := hfinal
            deliver := delivery
            horizon := hkernel.hhor
            guards := { finCmp := ?_, jPath := ?_, cap := ?_ } }⟩
  · intro x hx
    dsimp only
    intro hready
    exact receipt_finCmp p c E rho hkernel.set.base hkernel.set.fault hI3
      (delivery.selected x hx).index x X U (delivery.selected x hx).time hfinal hready
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_jPath p c E rho ΔF (pt.r + 2) y (delivery.selected x hx).index x A U X
      (delivery.selected x hx).time h pt.w hkernel.input hx hkernel.bound hw.1 hw.2.1
      hslot hanchor hfloor hStrat hEmittedSource
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_cap p c E rho ΔF (pt.r + 2) y (delivery.selected x hx).index x X
      (delivery.selected x hx).time hx hkernel.bound hw.1 hw.2.1 hkernel.set.base.valid
      hheight hcapBefore hrows

end AvailableChain.FGSA.Run
end
