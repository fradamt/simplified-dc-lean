module
public import AvailableChainFGSAProofs.Proofs.Finality.Carry
public import AvailableChainFGSAProofs.Proofs.Finality.Rows
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
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
    (receipt_ready_block p c E rho i x X t hready)
    ((FinalityFinalizedAt_def p C _ _).mpr ⟨hCF, rfl⟩)
    ((FinalityFinalizedAt_def p X _ _).mpr ⟨receipt_finality p X, rfl⟩)
  rcases Bool.or_eq_true_iff.mp hc with hbelow | habove
  · exact KitFG.preceq_total_of_common hbelow hfinal
  · exact Or.inr (KitFG.preceq_trans hfinal habove)

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
    change rho.events[i]?.map V2.Event.time = some t at ht
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
    change rho.events[i]?.map V2.Event.time = some t at ht
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
/-- Paper 22:1297–1302: an explicit cached anchor is on the carrier path.
DC: INTENTIONAL W cached-J guard. This does not produce source provenance;
Assembly must supply the stated cached equality at the selected pre-handler read. -/
theorem receipt_jPath_of_cached_anchor (i : Nat) (x : V) (X U : FGBlock (Fin p.n))
    (hcached : (storeAt p c E rho i x).fg.J = U) (hpath : FGBlock.Preceq U X.parent) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.J X ∨
      (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j := by
  have hp : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node P s body rows => exact KitFG.preceq_parent_node P s body rows
  exact Or.inl (hcached ▸ KitFG.preceq_trans hpath hp)

end AvailableChain.FGSA.Run
end
