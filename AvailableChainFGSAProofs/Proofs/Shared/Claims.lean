module
public import AvailableChainFGSAClaims.Claims.Outage
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
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
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
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
  refine ⟨w, input, start.trans_lt bound, hL G ΔF g w hδ c E rho pt ?_⟩
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
    refine ⟨?_, List.length_filter_le _ _⟩
    unfold healStart
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
      rw [V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [hread]
  exact Gen.Pure.block_preceq_trans hb hm

end AvailableChain.FGSA.Run
end

public section
namespace AvailableChain.FGSA.Run
variable {p : Params}

/-- Plan B1–B2: conditional GST growth uses one H-time witness, recovery
recurrence and awake proposers. The shared causal, emission and order proof
steps are local here because this existing module is append-only. -/
theorem fgsa_availableGrowthGST (hH : HTimeClaim p) : AvailableGrowthGSTClaim p := by
  intro G ΔF hδ V _ _ In c E rho t hp hlate hhor
  obtain ⟨w, input, hstar, available⟩ := fgsa_availableGST hH G ΔF hδ c E rho hp
  have hd := p.deltaPos
  have hgap := hp.set.gapPos
  have hzero : 0 ≤ tstar p w := by
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
  -- Plan A2: construct the actual application-bearing proposal once.
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let τ := V2.D.proposalTime (fgsaInterface p c) s
  have he : ((4 * s : Nat) : Time) * p.Δ = τ := by
    change ((4 * s : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int)
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hp.set.base.delta v hh.2
    (4 * s) (he ▸ hupper.trans hwindow)
  rw [he] at hi
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i v).st τ
  let raw := proposerVotes st s
  let sup := proposerSupport st s
  let H := getHead p st raw sup
  let rows := proposalRows p st H
  let B := Block.node H s (packBody (c.app (rho.input v τ)) rows)
  let m := Msg.proposal B (raw.filterMap liftHead?) (sup.filterMap liftHead?) rows
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩
  have hm : o ∈ (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v τ).2 := by
    apply (fgsa_emits_proposal E rho _ v τ s m).mpr
    refine ⟨ha, rfl, rfl, ?_⟩
    delta propose
    simp only [Nat.ne_of_gt hh.1, ↓reduceIte, Option.map_some]
    rfl
  have hprop : HonestProposal E rho (fgsaInterface p c) s B := by
    refine ⟨hh, o, ⟨i, hi, ?_⟩, rfl⟩
    rw [(V2.D.Run.step_tick_eq E rho hi).2]
    exact hm
  have hslot : B.slot = s := rfl
  have hgate : SA.gateTime p.toParams s ≤ t + G + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have hincl := available.2 ⟨s, B⟩ (hlate.trans hfuture.le) hprop (hgate.trans hhor)
  have hread : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x u, V2.D.outputAt E rho g x u = S_at p c E rho (timeIdx rho u) x := by
    intro g hg x u
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho u x).st.base.stableRecord = _ <;>
      rw [V2.D.Engine.readAt_eq_stateBefore hs u] <;> rfl
  have hcut : ∀ u, E.t_GST + B_HF p ΔF G ≤ u →
      HealSuffix p c rho (E.t_GST + B_HF p ΔF G) (timeIdx rho u) := by
    intro u hu
    refine ⟨?_, List.length_filter_le _ _⟩
    have hm := V2.D.Engine.read_length_mono (rho := rho) _ u hu
    unfold healStart
    split
    · exact (preIdx_le_afterTicksIdx E rho hs _).2.trans hm
    · exact hm
  refine ⟨w, input, hstar, s, B, hfuture, hprop, ?_⟩
  intro g hg
  refine ⟨?_, fun x hx => hincl g hg _ x ⟨hgate, hhor⟩ hx⟩
  intro x hx
  -- Plan A5: a stored ancestor cannot have a strictly future slot.
  have hn : ¬ Block.Preceq B (V2.D.outputAt E rho g x t) := by
    intro hb
    rw [hread g hg x t] at hb
    have inv := cstoreInv_stateBefore E rho (timeIdx rho t) x
    obtain ⟨S, hS, heS⟩ := (inv.baseTree _).mp inv.Smem
    change Block.Preceq B (V2.D.Run.stateBefore E rho (timeIdx rho t) x).st.base.stableRecord at hb
    rw [← heS] at hb
    obtain ⟨C, hC, hCB⟩ := eraseFG_ancestor_mem inv.fg.closed hS hb
    have hmem := (inv.baseTree B).mpr ⟨C, hC, hCB⟩
    have hbound := (fgsa_stateBefore_bounds E rho hs (timeIdx rho t) x).1 B hmem
    have hnow : (V2.D.Run.stateBefore E rho (timeIdx rho t) x).st.base.now ≤ t := by
      rcases V2.D.Engine.stateBefore_now_source (fgsaClock p c) (fgsa_hrestore_now p c)
        E rho (timeIdx rho t) x with hz | ⟨j, hj, hjt⟩
      · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (timeIdx rho t) x)] at hz
        exact hz.trans ht
      · rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (timeIdx rho t) x)] at hjt
        exact (V2.D.Engine.index_lt_read_length_iff hs t hjt).mp hj
    have hle : B.slot ≤ p.slotOf t := hbound.trans (Internal.slotOf_mono hnow)
    have hpos : 0 < 4 * p.Δ := mul_pos (by decide) p.deltaPos
    have hdiv : t / (4 * p.Δ) < (s : Time) := by
      apply (Int.ediv_lt_iff_lt_mul hpos).mpr
      change t < 4 * p.Δ * (s : Time) at hfuture
      simpa only [mul_comm] using hfuture
    have hlt : p.slotOf t < s := by
      unfold Params.slotOf
      exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hh.1)).mpr hdiv
    exact (not_lt_of_ge (hslot.ge.trans hle)) hlt
  have hmono : Block.Preceq (V2.D.outputAt E rho g x t)
      (V2.D.outputAt E rho g x (t + G + 6 * p.Δ)) := by
    rw [hread g hg x t, hread g hg x (t + G + 6 * p.Δ)]
    exact available.1.2.1 _ _ x (hcut t hlate) (hcut _ (hlate.trans htD))
      (V2.D.Engine.read_length_mono _ _ htD) hx
  -- Plan A4: the same deadline output is the common upper bound.
  have hle : Block.Preceq (V2.D.outputAt E rho g x t) B := by
    rcases Gen.Pure.block_preceq_total_of_common hmono (hincl g hg _ x ⟨hgate, hhor⟩ hx)
      with h | h
    · exact h
    · exact (hn h).elim
  have hne : V2.D.outputAt E rho g x t ≠ B := by
    intro heB
    apply hn
    rw [heB]
    exact Gen.Pure.block_preceq_refl B
  change (!decide (V2.D.outputAt E rho g x t = B) &&
    Block.preceq (V2.D.outputAt E rho g x t) B) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hne, hle⟩

end AvailableChain.FGSA.Run
end
