module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowth

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan A1–A6; bp 03 §5 (03:418–458);
DC Generic/Lemmas.lean:60 liveFrom_of_includedFrom.
Unfolded CleanGrowthClaim body. Select one awake honest proposal at the trigger
and use its gate by the original deadline.
Assembly supplies the inclusion fields and event monotonicity inline. -/
theorem clean_growth_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      IsGateTick p c rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (hmono : Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length))
    (hrec : AwakeProposerRecurrenceFrom p c E rho 0 G)
    (hgap : 4 * p.Δ ≤ G) (t : Time) (ht : 0 ≤ t)
    (hhor : t + G + 6 * p.Δ ≤ rho.horizon) :
    ∃ s B, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      HonestProposal E rho (fgsaInterface p c) s B ∧
      ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
        (∀ x ∈ rho.honest, Block.Prec (V2.D.outputAt E rho g x t) B) ∧
        (∀ x ∈ rho.honest, Block.Preceq B (V2.D.outputAt E rho g x (t + G + 6 * p.Δ))) := by
  have hd := p.deltaPos
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hG : 0 ≤ G := (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le).trans hgap
  have hwindow : t + G ≤ rho.horizon := (le_add_of_nonneg_right h6).trans hhor
  have htD : t ≤ t + G + 6 * p.Δ :=
    (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right h6)
  obtain ⟨s, hfuture, hupper, hh, ha⟩ := hrec t ht hwindow
  have hs := hset.pre.base.valid.toScheduleWellFormed
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hset.pre.base.delta hh ha (hupper.trans hwindow)
  have hgate : SA.gateTime p.toParams s ≤ t + G + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have hincl := clean_inclusion_body E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows ⟨s, B⟩ hprop (hgate.trans hhor) hmono
  refine ⟨s, B, jointGrowthAt_of_inclusion
    (fun g x u => V2.D.outputAt E rho g x u)
    (fun g => g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed])
    (· ∈ rho.honest) (V2.D.proposalTime (fgsaInterface p c))
    (HonestProposal E rho (fgsaInterface p c)) s B t (t + G + 6 * p.Δ)
    hfuture hprop ?_ ?_ ?_⟩
  · intro g x hg hx
    rw [fgsa_outputAt_eq_S_at E rho hs g hg x t,
      fgsa_outputAt_eq_S_at E rho hs g hg x (t + G + 6 * p.Δ)]
    exact hmono _ _ x (List.length_filter_le _ _) (List.length_filter_le _ _)
      (V2.D.Engine.read_length_mono _ _ htD) hx
  · intro g x hg hx
    exact hincl g hg _ x ⟨hgate, hhor⟩ hx
  · intro g x hg _
    exact fgsa_output_noFuture_of_slot E rho hs ht hfuture hslot.ge g hg x

end AvailableChain.FGSA.Run
end
