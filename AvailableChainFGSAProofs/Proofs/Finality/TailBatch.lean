module
public import AvailableChainFGSAProofs.Proofs.Finality.ActionTime
public import AvailableChainFGSAProofs.Proofs.Finality.TailMixed
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Paper 22:1985–2009 (FT-Tail-W): the honest label HEADs extend the witness Q,
and the reader's finality is below Q, so the shared admission lemma gives the batch.
DC: Goldfish/Confirmation.lean:494,508; honest/rest partition at the action read. -/
theorem ktail_action_walk_batch {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (ow : TailOpeningWitness_W p c E rho ΔF pt) :
    ∀ x ∈ rho.honest, ∀ nd,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      ∃ raw support seats m,
        FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support ∧
        Gen.Pure.Batch (Finset.card seats) m ∧
        WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1) raw support (eraseFG ow.Q) seats m := by
  classical
  intro x hx nd hnd
  obtain ⟨_, _, _, _, hs2, hGST, _⟩ := ktail_bounds hT
  obtain ⟨hvGST, hvte, heh, hvthor⟩ := finality_action_time_bounds p pt.r (pt.r + 1)
    (by omega) E.t_GST E.Δ rho.horizon hGST hT.set.base.delta ow.actionInRun
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hT.set.sync (fgsaDelay_nonrow E.Δ _) hvGST hvte heh
  have hcover : ∀ y H, y ∈ rho.honest →
      headAtLabel p c E rho y ((pt.r + 1) * p.R + 1) = some H →
      Block.Preceq (eraseFG ow.Q) H := by
    intro y H hy hH
    have hc1 : pt.r * p.R ≤ (pt.carrier : Nat) := by
      have := hT.carrier.1
      omega
    exact hT.input.ac.h2' pt.carrier (eraseFG ow.Q) ow.honestQ (hs2.trans hc1) y _ H hy
      (Nat.succ_le_succ hT.carrier.2.1) hH
  obtain ⟨k, hk, _, hread⟩ := ktail_action_store p c E rho x _ nd hnd
  obtain ⟨_, hsuf, hcut⟩ := ktail_action_suffix hT hk
  have hF := ktail_F_below_witness hT ow (k + 1) x hx hsuf hcut
    (ktail_action_S_cover hT ow hx hk)
  rw [hread] at hF
  obtain ⟨hcount, hwalk, hhead⟩ := fgsa_action_walk_batch E rho hT.set.base (pt.r + 1) hsync
    (fun y hy => hT.set.awake y hy _ hvGST hvthor) (hT.set.batch hvGST hvthor)
    (eraseFG ow.Q) x nd hnd hcover (eraseFG_preceq hF)
  exact ⟨_, _, _, _, hhead, hcount, hwalk⟩

/-- Paper 22:1985–2009 (FT-Tail-W): the full tail kernel, with the action batch
and mixed arm proved. All remaining inputs have existing Foundations producers.
DC: INTENTIONAL: W Tail kernel with local receipt guards. -/
theorem tail_kernel_W_full_of (G ΔF : Time) (pt : TailKernelPt p)
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (hqc : RQCOrigin p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
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
    (hmono : RMono p c E rho) (hXing : RXing p c E rho) :
    ∀ x ∈ rho.honest,
      AcceptsFinalBefore p c E rho x pt.U (kernelDeadlineW p ΔF (pt.r + 1)) :=
  tail_kernel_W_of_relay G ΔF pt hT hOrigin hBatch hSOCOVTarget hqc hI3 hStrat hEmittedSource
    hcapBefore (ktail_action_walk_batch hT) hmono hXing

end AvailableChain.FGSA.Run
end
