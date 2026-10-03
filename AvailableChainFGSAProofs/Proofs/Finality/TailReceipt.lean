module
public import AvailableChainFGSAProofs.Proofs.Finality.Receipt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Paper 22:1286–1305, plan §4: the terminal carrier gives every AcceptPrem_W field at
any final action q. This is receipt_acceptPrem_W with the kernel record replaced by its
used fields, so the Tail kernel can use q = r+1.
DC: INTENTIONAL local W receipt and same-event guards; Assembly supplies the stated
Foundations and cap inputs. -/
theorem ktail_acceptPrem_W (G ΔF : Time) (q : Nat) (w : HealingWitness)
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (hinput : HealingInput p c E rho w ΔF)
    (hhor : kernelDeadlineW p ΔF q ≤ rho.horizon)
    (y : Nat) (A U X : FGBlock (Fin p.n))
    (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X)
    (hslot : X.slot = q * p.R + kappaF p ΔF)
    (hne : X ≠ .genesis) (hsel : TRowsSelect p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hanchor : (heightView p A).h_j = y) (hfloor : w.M + 1 ≤ y)
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
      p.actionTime r < p.actionTime (q + 1) → h ≤ y + 1) :
    Nonempty (AcceptPrem_W p c E rho X U (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF q)) := by
  have hdeadline : SA.proposalTime p.toParams X.slot + p.Δ = kernelDeadlineW p ΔF q := by
    rw [hslot, ← fgsa_grid_sa_proposalTime, fgsa_grid_carrier_timeW,
      carrierTimeW_def, kernelDeadlineW_def]
  have hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot := by
    have hFpos := E.Δ_pos.trans_le h.deltaF
    have hmax := le_max_right (p.actionTime q) E.t_GST
    have hhor' := h.horizon.1
    simp only [Time] at hmax hhor' hFpos ⊢
    omega
  have hfinal := receipt_finalized_of_carriage p c E rho hsel ΔF q y A U X hne h
  obtain ⟨rows, hcarrier, _⟩ := h.carrier
  obtain ⟨delivery⟩ := receipt_delivery p c E rho G ΔF hrec X U rows hcarrier hgst
    (hdeadline ▸ hhor) hfinal hI3
  rw [hdeadline] at delivery
  have hXp : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node P s body rows => exact KitFG.preceq_parent_node P s body rows
  have hheight : y + 1 ≤ (heightView p X).h := by
    rw [← h.freshHeight]
    exact (fgCertificateLaws p).height.h_mono (KitFG.preceq_trans h.path hXp)
  refine ⟨{ base := hrec.base
            faultBound := hrec.fault
            finalized := hfinal
            deliver := delivery
            horizon := hhor
            guards := { finCmp := ?_, jPath := ?_, cap := ?_ } }⟩
  · intro x hx
    dsimp only
    intro hready
    exact receipt_finCmp p c E rho hrec.base hrec.fault hI3
      (delivery.selected x hx).index x X U (delivery.selected x hx).time hfinal hready
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_jPath p c E rho ΔF q y (delivery.selected x hx).index x A U X
      (delivery.selected x hx).time h w hinput hx hbound hw.1 hw.2.1
      hslot hanchor hfloor hStrat hEmittedSource
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_cap p c E rho ΔF q y (delivery.selected x hx).index x X
      (delivery.selected x hx).time hx hbound hw.1 hw.2.1 hrec.base.valid
      hheight hcapBefore hrows

end AvailableChain.FGSA.Run
end
