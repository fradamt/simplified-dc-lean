module
public import AvailableChainFGSAClaims.Claims.Outage
public import AvailableChainFGSAClaims.Claims.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAClaims.Claims.Healing
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Shared.Healed
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowth
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

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

/-- Blueprint 22:1382–1384; FirstFinality plan §8. DC: INTENTIONAL GST form;
DC finalized (Generic/Claims.lean:39–44). H-time supplies one witness;
local liveness at tstar keeps its comparisons and uses the later GST deadline. -/
theorem fgsa_firstFinality_recFE (hH : HTimeClaim p)
    (hL : FinalityLivenessRecFEClaim_W p) : FirstFinalityRecFEClaim_W p := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    (le_add_of_nonneg_right hW).trans h.hhor
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have hstar := start.trans_lt bound
  have hdeadline : tstar p w + W_W p ΔF g ≤ E.t_GST + B_HF p ΔF G + W_W p ΔF g := by
    exact Int.add_le_add_right hstar.le _
  obtain ⟨U, hS, hF, haccept⟩ := hL G ΔF g w hδ c E rho ⟨tstar p w⟩
    ⟨h.set, input, le_rfl, hdeadline.trans h.hhor⟩
  refine ⟨w, input, hstar, U, hS, hF, ?_⟩
  intro x hx
  exact acceptsFinalBefore_mono_deadline p c E rho h.set.core.base.noRestart
    h.set.core.base.valid.toScheduleWellFormed hdeadline (haccept x hx)

/-- Blueprint 22:1382–1384; FirstFinality plan §8. DC: INTENTIONAL GST form;
DC finalized (Generic/Claims.lean:39–44). H-time supplies one witness;
local liveness at tstar keeps its comparisons and uses the later GST deadline. -/
theorem fgsa_firstFinality_recF4 (hH : HTimeClaim p)
    (hL : FinalityLivenessRecF4Claim_W p) : FirstFinalityRecF4Claim_W p := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    (le_add_of_nonneg_right hW).trans h.hhor
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have hstar := start.trans_lt bound
  have hdeadline : tstar p w + W_W p ΔF g ≤ E.t_GST + B_HF p ΔF G + W_W p ΔF g := by
    exact Int.add_le_add_right hstar.le _
  obtain ⟨U, hS, hF, haccept⟩ := hL G ΔF g w hδ c E rho ⟨tstar p w⟩
    ⟨h.set, input, le_rfl, hdeadline.trans h.hhor⟩
  refine ⟨w, input, hstar, U, hS, hF, ?_⟩
  intro x hx
  exact acceptsFinalBefore_mono_deadline p c E rho h.set.core.base.noRestart
    h.set.core.base.valid.toScheduleWellFormed hdeadline (haccept x hx)

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_finalityLivenessGST_recFE (hH : HTimeClaim p)
    (hL : FinalityLivenessRecFEClaim_W p) (hP : ProposalFinalRecFEClaim_W p)
    (hDC : LiveDCFromWindowsStatement p) : FinalityLivenessGSTClaim_W p .recFE := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have ht : tstar p w ≤ pt.t := start.trans (bound.le.trans h.late)
  have hlocal := hL G ΔF g w hδ c E rho pt ⟨h.set, input, ht, h.hhor⟩
  refine ⟨w, input, start.trans_lt bound, hlocal, ?_⟩
  intro hlong
  apply hDC c E rho G ΔF g pt.t h.set.core (input.wit.after_gst.trans ht) ?_ ?_ hlong
  · obtain ⟨U, hU, _, ha⟩ := hlocal
    exact ⟨U, hU, ha⟩
  · intro s X hp hts hsHor
    exact hP G ΔF g w hδ c E rho ⟨s, X⟩ ⟨h.set, input, hp, ht.trans hts, hsHor⟩

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). H-time and the local claim supply the result. -/
theorem fgsa_finalityLivenessGST_recF4 (hH : HTimeClaim p)
    (hL : FinalityLivenessRecF4Claim_W p) (hP : ProposalFinalRecF4Claim_W p)
    (hDC : LiveDCFromWindowsStatement p) : FinalityLivenessGSTClaim_W p .recF4 := by
  intro G ΔF g hδ V _ _ In c E rho pt h
  have hW := fgsa_gst_window_nonneg p ΔF g
  have hhor : E.t_GST + B_HF p ΔF G ≤ rho.horizon :=
    h.late.trans ((le_add_of_nonneg_right hW).trans h.hhor)
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨h.set.core, h.set.bound⟩, hhor⟩
  have ht : tstar p w ≤ pt.t := start.trans (bound.le.trans h.late)
  have hlocal := hL G ΔF g w hδ c E rho pt ⟨h.set, input, ht, h.hhor⟩
  refine ⟨w, input, start.trans_lt bound, hlocal, ?_⟩
  intro hlong
  apply hDC c E rho G ΔF g pt.t h.set.core (input.wit.after_gst.trans ht) ?_ ?_ hlong
  · obtain ⟨U, hU, _, ha⟩ := hlocal
    exact ⟨U, hU, ha⟩
  · intro s X hp hts hsHor
    exact hP G ΔF g w hδ c E rho ⟨s, X⟩ ⟨h.set, input, hp, ht.trans hts, hsHor⟩

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
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
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
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
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
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
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
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
  have hsecond : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon := by
    simpa only [two_mul, ← add_assoc] using h.hhor
  exact ⟨h.set, input, start.trans (bound.le.trans h.late),
    (le_add_of_nonneg_right hW).trans hsecond, hsecond⟩

/-- Blueprint 21 H.20–H.22; DC available/stableIncludedFast: INTENTIONAL GST output.
H-time supplies one healing witness. Gate service and suffix monotonicity
supply both public outputs at every later read within the horizon. -/
theorem fgsa_availableGST (hH : HTimeClaim p) : AvailableGSTClaim p := by
  intro G ΔF hδ V _ _ In c E rho hp
  have ht := hH G ΔF hδ c E rho () hp
  have healed := uniformHealing_of_hTimeConcl p c E rho G ΔF ht
  obtain ⟨w, input, hstar, hbound⟩ := ht
  refine ⟨w, input, hstar.trans_lt hbound, healed, ?_⟩
  intro pt hstart hprop hhor
  have hs := hp.set.base.valid.toScheduleWellFormed
  have hgate : E.t_GST + B_HF p ΔF G < SA.gateTime p.toParams pt.s := by
    change E.t_GST + B_HF p ΔF G < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    change E.t_GST + B_HF p ΔF G ≤ 4 * p.Δ * (pt.s : Time) at hstart
    exact hstart.trans_lt (lt_add_of_pos_right _ (mul_pos (by decide) p.deltaPos))
  have hcut : HealSuffix p c rho (E.t_GST + B_HF p ΔF G)
      (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) := by
    rw [HealSuffix_def]
    refine ⟨?_, List.length_filter_le _ _⟩
    rw [healStart_def]
    split
    · exact afterTicksIdx_mono rho hgate.le
    · change (rho.events.filter _).length ≤ (rho.events.filter _).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ he
      exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (Or.inl ((of_decide_eq_true he).trans_lt hgate)))
  have service := healed.2.2.2 pt.s pt.P hstart hhor hprop
  intro g hg t x ht hx
  have hij : afterTicksIdx rho (SA.gateTime p.toParams pt.s) ≤ timeIdx rho t :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans
      (V2.D.Engine.read_length_mono _ _ ht.1)
  have hlater : HealSuffix p c rho (E.t_GST + B_HF p ΔF G) (timeIdx rho t) :=
    ⟨hcut.1.trans hij, List.length_filter_le _ _⟩
  have hb : Block.Preceq pt.P
      (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) x) := by
    have hb := service (SA.gateTime p.toParams pt.s) x rfl hx
    change Block.Preceq pt.P
      ((fgsaInterface p c).stable (afterTicks E rho (SA.gateTime p.toParams pt.s) x)) at hb
    rw [afterTicks_eq_stateBefore E rho hs] at hb
    exact hb
  have hm := healed.2.1 _ _ x hcut hlater hij hx
  have hread : V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [S_at_def, V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [hread]
  exact Gen.Pure.block_preceq_trans hb hm

end AvailableChain.FGSA.Run
end

public section
namespace AvailableChain.FGSA.Run
variable {p : Params}

/-- Plan B1–B2; Blueprint 21 H.20–H.22: conditional GST growth uses one
H-time witness, recovery recurrence and awake proposers. The shared causal,
emission, healed-read and order lemmas supply both public outputs. -/
theorem fgsa_availableGrowthGST (hH : HTimeClaim p) : AvailableGrowthGSTClaim p := by
  intro G ΔF hδ V _ _ In c E rho t hp hlate hhor
  obtain ⟨w, input, hstar, available⟩ := fgsa_availableGST hH G ΔF hδ c E rho hp
  have hd := p.deltaPos
  have hgap := hp.set.gapPos
  have hzero : 0 ≤ tstar p w := by
    rw [tstar_def]
    change 0 ≤ 4 * p.Δ * (w.u : Time) + 6 * p.Δ
    positivity
  have ht : 0 ≤ t := hzero.trans (hstar.le.trans hlate)
  have hgst : E.t_GST ≤ t := input.wit.after_gst.trans (hstar.le.trans hlate)
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hG : 0 ≤ G := (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le).trans hgap
  have hwindow : t + G ≤ rho.horizon := (le_add_of_nonneg_right h6).trans hhor
  have htD : t ≤ t + G + 6 * p.Δ :=
    (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right h6)
  obtain ⟨s, hfuture, hupper, hh⟩ := hp.set.gap t hgst hwindow
  have hs := hp.set.base.valid.toScheduleWellFormed
  have ha := hp.set.awake _ hh.2 _ (hgst.trans hfuture.le) (hupper.trans hwindow)
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hp.set.base.delta hh ha (hupper.trans hwindow)
  have hgate : SA.gateTime p.toParams s ≤ t + G + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have hincl := available.2 ⟨s, B⟩ (hlate.trans hfuture.le) hprop (hgate.trans hhor)
  refine ⟨w, input, hstar, s, B, jointGrowthAt_of_inclusion
    (fun g x u => V2.D.outputAt E rho g x u)
    (fun g => g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed])
    (· ∈ rho.honest) (V2.D.proposalTime (fgsaInterface p c))
    (HonestProposal E rho (fgsaInterface p c)) s B t (t + G + 6 * p.Δ)
    hfuture hprop ?_ ?_ ?_⟩
  · intro g x hg hx
    exact fgsa_healed_output_mono E rho hs available.1 hlate htD g hg x hx
  · intro g x hg hx
    exact hincl g hg _ x ⟨hgate, hhor⟩ hx
  · intro g x hg _
    exact fgsa_output_noFuture_of_slot E rho hs ht hfuture hslot.ge g hg x

/-- WC plan §8 Job 4 and r2.1; DC safety projection with the same source witness.
Source cut coverage and continuation coverage discharge the live safety guard. -/
theorem weakContinuation_of_live {G : Time} (h : WeakContinuationLiveClaim p G) :
    WeakContinuationClaim p G := by
  intro V _ _ In c ΔF hδ E source hS
  obtain ⟨u, Q, iStar, cut, live⟩ := h c ΔF hδ E source hS
  refine ⟨u, Q, iStar, cut, ?_⟩
  intro E' rho hc
  exact (live E' rho hc).safety (cut.beforeEnd.le.trans hc.covered)

end AvailableChain.FGSA.Run
end
