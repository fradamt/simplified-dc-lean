module
public import AvailableChainFGSAClaims.Claims.Healing
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Shared.Healed
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

/-! Holds claim → claim implications only; its Claims/* imports are an exact L42 exception.
P3 r3.5.8 R5-66. -/

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open Gen.Pure (CompatOn MonoOn)

variable {p : Params}

/-- The family-(0) client claim follows from the Linked-only claim. -/
theorem clientSafety_base (h : ClientSafetyClaim p) : ClientSafetyBaseClaim p :=
  fun c E rho _ hb => h c E rho hb.set.linked

theorem cleanHistory_of_cut (h : CleanCutClaim p) : CleanHistoryClaim p :=
  fun c E rho _ pt hc => (h c E rho pt ⟨hc.set.toCleanCut⟩).1

theorem cleanPrefixTruncation_of_cut (h : CleanCutClaim p) : CleanPrefixTruncationClaim p :=
  fun c E rho _ pt hc => (h c E rho pt ⟨hc.set.toCleanCut⟩).2

theorem cleanSafety_outputs (h : CleanSafetyClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {pt : Unit}
    (hc : CleanPrem p c E rho pt ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) ∧
      MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) :=
  (h c E rho pt hc).2.2

/-- Blueprint 21 H.20–H.22; f07w-rulings S4.5 DEFAULT REVISED.
DC: additive internal corollary, not a standalone frozen healing claim.
HTimeConcl supplies the input and both bound links. Restrict its healed suffix
to GST + B_HF; no recovery or service premise is added. -/
theorem uniformHealing_of_hTimeConcl (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (h : HTimeConcl p c E rho G ΔF) :
    Healed p c E rho (E.t_GST + B_HF p ΔF G) := by
  obtain ⟨w, input, start, bound⟩ := h
  exact healed_mono_start p c E rho (start.trans bound.le) input.healed

private theorem fgsa_gst_window_nonneg (p : Params) (ΔF : Time) (g : Nat) :
    0 ≤ W_W p ΔF g := by
  have hΔ : 0 ≤ p.Δ := p.deltaPos.le
  rw [W_W_def, betaF_def]
  change 0 ≤ ((g : Time) + 2) * (4 * (p.R : Time) * p.Δ) +
    4 * (kappaF p ΔF : Time) * p.Δ + p.Δ
  positivity

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_finalityLivenessGST_recFE (hH : HTimeClaim p)
    (hL : FinalityLivenessRecFEClaim_W p) : FinalityLivenessGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, hL G ΔF g w hδ c E rho pt ?_⟩
  exact ⟨h.set, input, start.trans (bound.le.trans h.late), h.hhor⟩

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_finalityLivenessGST_recF4 (hH : HTimeClaim p)
    (hL : FinalityLivenessRecF4Claim_W p) : FinalityLivenessGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, hL G ΔF g w hδ c E rho pt ?_⟩
  exact ⟨h.set, input, start.trans (bound.le.trans h.late), h.hhor⟩

/-- Blueprint 22:1421–1430. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_proposalFinalGST_recFE (hH : HTimeClaim p)
    (hL : ProposalFinalRecFEClaim_W p) : ProposalFinalGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, hL G ΔF g w hδ c E rho pt ?_⟩
  exact ⟨h.set, input, h.prop, start.trans (bound.le.trans h.late), h.hhor⟩

/-- Blueprint 22:1421–1430. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_proposalFinalGST_recF4 (hH : HTimeClaim p)
    (hL : ProposalFinalRecF4Claim_W p) : ProposalFinalGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, hL G ΔF g w hδ c E rho pt ?_⟩
  exact ⟨h.set, input, h.prop, start.trans (bound.le.trans h.late), h.hhor⟩

/-- Blueprint 22:1434–1451. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_aboveFrontierGST_recFE (hH : HTimeClaim p)
    (hL : AboveFrontierRecFEClaim_W p) : AboveFrontierGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right (mul_nonneg (by decide) hW)).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, hL G ΔF g w hδ c E rho pt ?_⟩
  have hsecond : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon := by
    simpa only [two_mul, ← add_assoc] using h.hhor
  exact ⟨h.set, input, start.trans (bound.le.trans h.late),
    (le_add_of_nonneg_right hW).trans hsecond, hsecond⟩

/-- Blueprint 22:1434–1451. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_aboveFrontierGST_recF4 (hH : HTimeClaim p)
    (hL : AboveFrontierRecF4Claim_W p) : AboveFrontierGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right (mul_nonneg (by decide) hW)).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  refine ⟨w, input, hL G ΔF g w hδ c E rho pt ?_⟩
  have hsecond : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon := by
    simpa only [two_mul, ← add_assoc] using h.hhor
  exact ⟨h.set, input, start.trans (bound.le.trans h.late),
    (le_add_of_nonneg_right hW).trans hsecond, hsecond⟩

end AvailableChain.FGSA.Run
end
