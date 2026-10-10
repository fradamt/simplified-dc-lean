module
public import AvailableChainFGSAProofs.Proofs.OutageContinuation.Export
public import AvailableChainFGSAProofs.Proofs.Outage.Export -- shake: keep (Outage claim boundary)
public import AvailableChainFGSAProofs.Proofs.Clean.Export -- shake: keep (Clean supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export
-- shake: keep (foundation supplier boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

private theorem clean_history_supplier (hcut : CleanCutClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀)
    (h : CleanCutPrem p c E rho pt ΔF) : CleanHistoryAt p c E rho pt.b₀ :=
  (hcut c E rho pt h).1

/-- Clean's enabled result extends to the inclusive public gate read. -/
private theorem clean_reader_gate_supplier
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (h : CleanPrem p c E rho () ΔF) :
    ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
      enabledGateAt p c E rho i x q →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧
        Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x) := by
  have hc := h.set.sleepPre.sleepPre
  have hq := h.set.pre.faultQ
  have hp : SourceDisciplinePrem p c E rho () := ⟨hc.base, hq⟩
  have hf := fgsa_fgFoundationClaim p c E rho () hp
  have hsrc := fgsa_srcFrameAboveClaim p c E rho () hp
  have hs := hc.base.valid.toScheduleWellFormed
  intro q i x hx hqhor hG
  have hi := (V2.D.Engine.index_lt_read_length_iff hs rho.horizon hG.1).mpr hqhor
  obtain ⟨C, hC, _, hCS⟩ := clean_gateOutput_body p c E rho rho.horizon hc hq
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩ hsrc
    (timeIdx rho rho.horizon) le_rfl
    (clean_invariant p c E rho hc hq
      ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩ hsrc _ le_rfl)
    i x q hi hx hG
  refine ⟨C, hC, block_preceq_trans hCS ?_⟩
  exact sExtends p c E rho hc hq
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩ hsrc x _ _
    (Nat.succ_le_of_lt ((V2.D.Engine.index_lt_read_length_iff hs _ hG.1).mpr le_rfl))
    (V2.D.Engine.read_length_mono _ _ hqhor)

/-- The cut claim supplies monotonicity at bounded confirmed public readers. -/
private theorem clean_reader_mono_supplier (hcut : CleanCutClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (h : CleanPrem p c E rho () ΔF) :
    ScopedMono (confirmedReader p c E rho)
      (fun t x => S_at p c E rho (timeIdx rho t) x)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon) := by
  have hg : (fgsaInterface p c).stable ∈
      [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] := by simp
  have hm := ((hcut c E rho ⟨rho.horizon⟩ ⟨h.set.sleepPre.sleepPre⟩).2.2.2.1 _ hg).2
  intro t u x ht hu htu hx hy
  simpa only [fgsa_outputAt_eq_S_at E rho h.set.pre.base.valid.toScheduleWellFormed _ hg]
    using hm t u x ht hu htu hx hy

/-- ROOT-DIGEST W2b. Blueprint 03 §4. The Clean claims supply the history projections.
Foundation Exports supply store, frame, and source discipline. -/
theorem fgsa_exactProposalClaim_of_clean
    (hcut : CleanCutClaim p) : ExactProposalClaim p := by
  exact outage_exactProposalClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hstrat := fun c E rho pt hb => (fgsa_fgFoundationClaim p c E rho pt hb).strat)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.2.2.1)

/-- ROOT-DIGEST W2b. Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen post-gate inclusion claim. -/
theorem fgsa_cleanInclusionPostGateClaim_of_clean
    (hcut : CleanCutClaim p) :
    CleanInclusionPostGateClaim p := by
  exact outage_cleanInclusionPostGateClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hstrat := fun c E rho pt hb => (fgsa_fgFoundationClaim p c E rho pt hb).strat)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.2.2.1)
    (hmono := by
      intro V _ _ In c E rho ΔF pt hc
      exact (cleanSafety_of_cut p hcut (by
        intro V _ _ In c E rho ΔF h
        have hc := h.sleepPre.sleepPre
        have hq := h.pre.faultQ
        have hp : SourceDisciplinePrem p c E rho () := ⟨hc.base, hq⟩
        have hf := fgsa_fgFoundationClaim p c E rho () hp
        have hf' : FGFoundation p c E rho :=
          ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩
        have hsrc := fgsa_srcFrameAboveClaim p c E rho () hp
        refine ⟨clean_sCompatible p c E rho hc hq hf' hsrc, ?_⟩
        intro i j x _ hj hij _
        exact sExtends p c E rho hc hq hf' hsrc x i j hij hj) c E rho (ΔF := ΔF) pt hc).2.1)

/-- ROOT-DIGEST W2b. Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen inclusion claim. -/
theorem fgsa_cleanInclusionClaim_of_clean
    (hcut : CleanCutClaim p) : CleanInclusionClaim p := by
  exact outage_cleanInclusionClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hstrat := fun c E rho pt hb => (fgsa_fgFoundationClaim p c E rho pt hb).strat)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.2.2.1)
    (hReaderGate := fun c E rho _ hc => clean_reader_gate_supplier p c E rho hc)
    (hReaderMono := fun c E rho _ hc => clean_reader_mono_supplier p hcut c E rho hc)

/-- ROOT-DIGEST W2b. Blueprint 03 §5. Clean supplies scoped output compatibility.
P-Ou supplies one confirmed gate witness and inclusion at each later confirmed reader. -/
theorem fgsa_cleanGrowthClaim_of_clean
    (hcut : CleanCutClaim p)
    (hWitness : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams s) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams s)) y))
    (hInclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon → ∀ u x g,
      SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon → confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Preceq B (V2.D.outputAt E rho g x u)) : CleanGrowthClaim p := by
  apply outage_cleanGrowthClaim_of p
  · intro V _ _ In c E rho ΔF hs s B hprop hgate u x g hu hup hx hg
    have ht := (hcut c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨hs.sleepPre.sleepPre⟩).2
    exact clean_growth_compatible_of_outputs E rho hs
      (fun g hg => (ht.2.2.1 g hg).1) hgate (hWitness c E rho ΔF hs s B hprop hgate)
      hu hup hx hg
  · exact hInclusion

/-- P15-CUT: P-Ar derives every in-cut prefix receipt from OutageSleep₂.
The earlyTime(q) <= b₀ guard stays in the public per-label predicate. -/
theorem fgsa_outagePrefixReceiptClaim : OutagePrefixReceiptDerivedClaim p :=
  arming_prefix_batch_receipt p

/-- ROOT-DIGEST W2b. Blueprint 03 §9. Foundation Exports supply the source facts.
One Clean cut result supplies all nine Clean inputs at b₀. -/
theorem fgsa_outageCompatClaim_of_clean
    (hcut : CleanCutClaim p) : OutageCompatClaim p := by
  intro V _ _ In c E rho fast pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hs := fgsa_sourceDisciplineBaseClaim p c E rho () hb
  exact outage_compat_body_of_cut p
    (hstore := (fgsa_activeViewAt p c E rho).1)
    (hframe := (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (hstrat := (fgsa_fgFoundationClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩).strat)
    (htsrc := hs.1) (hnamed := hs.2.2)
    (hcut := hcut c E rho (ΔF := ΔF) ⟨pt.b₀⟩ ⟨h.set.sleepPre⟩) h

/-- ROOT-DIGEST W2b. Blueprint 03 §9.1. The fast claim uses the P1 part of the cut wrapper. -/
theorem fgsa_fastP1Claim_of_clean
    (hcut : CleanCutClaim p) : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hs := fgsa_sourceDisciplineBaseClaim p c E rho () hb
  exact (outage_compat_body_of_cut p
    (hstore := (fgsa_activeViewAt p c E rho).1)
    (hframe := (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (hstrat := (fgsa_fgFoundationClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩).strat)
    (htsrc := hs.1) (hnamed := hs.2.2)
    (hcut := hcut c E rho (ΔF := ΔF) ⟨pt.b₀⟩ ⟨h.set.sleepPre⟩) h).1

/-- ROOT-DIGEST W2b. Blueprint 03 §9.2. The slow claim also keeps the pending-gate lease clause. -/
theorem fgsa_slowP1Claim_of_clean
    (hcut : CleanCutClaim p) : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hs := fgsa_sourceDisciplineBaseClaim p c E rho () hb
  exact outage_compat_body_of_cut p
    (hstore := (fgsa_activeViewAt p c E rho).1)
    (hframe := (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (hstrat := (fgsa_fgFoundationClaim p c E rho () ⟨h.set.pre.base, h.set.faultQ⟩).strat)
    (htsrc := hs.1) (hnamed := hs.2.2)
    (hcut := hcut c E rho (ΔF := ΔF) ⟨pt.b₀⟩ ⟨h.set.sleepPre⟩) h

end AvailableChain.FGSA.Run
end
