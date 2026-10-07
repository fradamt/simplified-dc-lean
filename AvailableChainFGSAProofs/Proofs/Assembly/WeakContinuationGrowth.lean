module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep (companion components)
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Export -- shake: keep (permitted WC reuse route)

public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (continuation producers)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Reuse the exact one-quorum causal theorem through the existing lane Export.
Assembly is the permitted home for cross-lane theorem composition. -/
theorem wcg_finalityTargetEarlier [Fintype V] :
    WCFinalityTargetEarlierStatement p c E rho := wc_finalityTargetEarlier

/-- Reuse the existing invariant-to-safety and safety/inclusion-to-growth proofs.
This is an internal assembly step. Its invariant and inclusion producers remain
open; they are not premises of WeakContinuationGrowthClaim. -/
theorem wcg_live_of_invariant_inclusion {ΔF : Time}
    {w : HealingWitness} {iStar : Nat}
    (hb : Base₂ p c E rho) (hs : WCSeed p c E rho w iStar)
    (hi : ∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i)
    (hf : ∀ i x y, iStar ≤ i → i ≤ rho.events.length →
      x ∈ rho.honest → y ∈ rho.honest →
      Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y))
    (hincl : ∀ pt : PtSP, w.u + 2 ≤ pt.s →
      HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
      SA.gateTime p.toParams pt.s ≤ rho.horizon → ServedFromGateAt p c E rho pt) :
    WeakContinuationLiveAt₂ p c E rho w.u w.QStar iStar ΔF := by
  obtain ⟨hc, hm, hseed, ho⟩ := wc_seededSafety hb.valid.toScheduleWellFormed hs hi
  have hsafe : SSafeFromCut₂ p c E rho iStar w.QStar ΔF := ⟨hc, hm, hseed, hf, ho⟩
  exact ⟨fun _ => hsafe, fun _ => hincl,
    wc_growth_of_safety_inclusion ΔF w.u w.QStar iStar hb hs.cut hsafe hincl⟩

end AvailableChain.FGSA.Run

namespace AvailableChain.FGSA.Run
open SimplexFG KitFG Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

omit [DecidableEq V] [Fintype V] in
private theorem wcg_cut_le_laterTick
    (hs : V2.D.ScheduleWellFormed E rho) {a t : Time} {j : Nat} {x : V}
    (he : rho.events[j]? = some (.tick x t)) (hat : a < t) :
    afterTicksIdx rho a ≤ j := by
  refine (preIdx_le_afterTicksIdx E rho hs a).2.trans ?_
  change (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤ j
  have hbound : a ≤ t - 1 := by
    simp only [Time] at hat ⊢
    omega
  have hmono := V2.D.Engine.read_length_mono (rho := rho) a (t - 1) hbound
  have hidx := (V2.D.Engine.index_lt_read_length_iff hs (t - 1) he).not.mpr
    (by simp : ¬ t ≤ t - 1)
  exact hmono.trans (Nat.le_of_not_lt hidx)


omit [Fintype V] in
private theorem wcg_comparisonFrame
    (hs : V2.D.ScheduleWellFormed E rho) (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (hfl : ∀ i x phase st WStar (Bfg : FGBlock (Fin p.n)),
      WCDutyInput p c E rho i x phase st → x ∈ rho.honest → iStar ≤ i →
      WStar ∈ st.fg.TF → eraseFG WStar = w.CStar → (heightView p WStar).h = w.M + 1 →
      Block.Preceq w.QStar (eraseFG Bfg) →
      WCUsableHighSourcesBelow p c E rho w i x st (eraseFG Bfg) →
      (∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
        Block.Preceq row.1 (eraseFG Bfg)) →
      ∀ view, WCDutyView p st phase view → view ⊆ st.fg.TF →
        WCFrameLiveBelow p st phase Bfg view)
    (s : Slot) (D : Block) (hstart : w.u + 2 ≤ s) (hseedD : Block.Preceq w.QStar D)
    (hmax : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r ≤ s - 2 → Block.Preceq B D)
    (hprev : ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y (s - 1) D)
    (hnr : V2.D.NoRestart rho) {i : Nat} {x : V} {phase : WCDutyPhase}
    {st : State p.n} {t : Time} (hduty : WCDutyInput p c E rho i x phase st)
    (hx : x ∈ rho.honest) (he : rho.events[i]? = some (.tick x t))
    (hst : st = clock p (storeAt p c E rho i x) t)
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
    (view : Finset (FGBlock (Fin p.n))) (hv : WCDutyView p st phase view)
    (hsub : view ⊆ st.fg.TF) :
    WCFrameBelow p st D ∧ Block.Preceq (liveRoot p st) D := by
  have hspos : 0 < s := by simp only [Slot] at hstart ⊢; omega
  have hcutTime : SA.gateTime p.toParams w.u < t := by
    have hcast : (w.u : Time) + 2 ≤ (s : Time) := by exact_mod_cast hstart
    have hd := p.deltaPos
    rcases ht with rfl | rfl
    · change 4 * p.Δ * (w.u : Time) + 6 * p.Δ < 4 * p.Δ * (s : Time)
      nlinarith
    · change 4 * p.Δ * (w.u : Time) + 6 * p.Δ < 4 * p.Δ * (s : Time) + p.Δ
      nlinarith
  have hcut : iStar ≤ i := hseed.cut ▸ wcg_cut_le_laterTick hs he hcutTime
  have hiN := hduty.within.le
  obtain ⟨WStar, hW, hh, hcarrier⟩ := hi.carrier
  have hcarrier' : WStar ∈ st.fg.TF := by
    rw [hst, clock_fg]
    exact hcarrier i x hcut hiN hx
  have hprevTime : SA.voteTime p.toParams (s - 1) < t := by
    have hlabel : s - 1 + 1 = s := by simp only [Slot] at hspos ⊢; omega
    have hcast : ((s - 1 : Nat) : Time) + 1 = (s : Time) := by exact_mod_cast hlabel
    have hd := p.deltaPos
    rcases ht with rfl | rfl
    · change 4 * p.Δ * ((s - 1 : Nat) : Time) + p.Δ < 4 * p.Δ * (s : Time)
      nlinarith
    · change 4 * p.Δ * ((s - 1 : Nat) : Time) + p.Δ < 4 * p.Δ * (s : Time) + p.Δ
      nlinarith
  obtain ⟨k, hk⟩ := hprev x hx
  have hpath := wc_headRead_laterPath hs hnr hk he hprevTime
  obtain ⟨Bfg, _, hBD⟩ :=
    ((cstoreInv_stateBefore E rho i x).baseTree D).mp (by
      have hm := (hpath D (block_preceq_refl D)).1
      rw [clock_base_blocks] at hm
      exact hm)
  have hinputs := wc_comparisonInputs hs hi s D hspos hseedD hmax hiN hcut hx he ht
  have hhigh : WCUsableHighSourcesBelow p c E rho w i x st (eraseFG Bfg) := by
    rw [hBD, hst]
    exact hinputs.1
  have htargets : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Preceq row.1 (eraseFG Bfg) := by
    rw [hBD, hst]
    exact hinputs.2
  have hf := hfl i x phase st WStar Bfg hduty hx hcut hcarrier' hW hh
    (hBD ▸ hseedD) hhigh htargets view hv hsub
  exact ⟨hBD ▸ hf.frame, hBD ▸ hf.startBelow⟩

/-- WC J3, plan §6.9; DC first eligible proposal: join the finite pivot, paths and walks.
The only lane producer premise is the reviewed live-frame Statement. -/
theorem wcg_proposalPivot (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframeLive : WCGSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCGProposalPivotStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have hs := hvalid.toScheduleWellFormed
  have hi := hinv rho.events.length ⟨hseed.within, le_rfl⟩
  have hfl := hframeLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ
    haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc
    hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed
  obtain ⟨D, hmember, hQD, hmax⟩ := wc_historyMax hi (pt.s - 2)
  have hprev := wc_history_previousHeads hs hdelta hseed hi pt.s D hstart hgate hmember
  have hs2 : 2 ≤ pt.s := by simp only [Slot] at hstart ⊢; omega
  have hFP : ∀ i x st, WCDutyInput p c E rho i x (.proposal pt.s) st →
      x = V2.D.proposerOf rho (fgsaInterface p c) pt.s →
      WCFrameBelow p st D ∧ Block.Preceq (liveRoot p st) D := by
    intro i x st hduty hx
    subst x
    obtain ⟨he, hst⟩ := wc_proposalInput hduty
    exact wcg_comparisonFrame hs hseed hi hfl pt.s D hstart hQD hmax hprev hnr hduty
      hprop.1.2 he hst (Or.inl rfl) st.fg.TF
      ⟨Or.inr ⟨⟨pt.s, Or.inl rfl⟩, rfl⟩⟩ (fun _ h => h)
  have hFH : ∀ i x st, x ∈ rho.honest → WCDutyInput p c E rho i x (.head pt.s) st →
      WCFrameBelow p st D ∧ Block.Preceq (liveRoot p st) D := by
    intro i x st hx hduty
    obtain ⟨he, hst⟩ := wc_headInput hduty
    exact wcg_comparisonFrame hs hseed hi hfl pt.s D hstart hQD hmax hprev hnr hduty
      hx he hst (Or.inr rfl) (voterBlocks p st pt.s) ⟨Or.inl ⟨pt.s, rfl, rfl⟩⟩
      (fun _ h => (Finset.mem_filter.mp h).1)
  have hPP : ∀ i x st, WCDutyInput p c E rho i x (.proposal pt.s) st →
      x = V2.D.proposerOf rho (fgsaInterface p c) pt.s →
      ∃ Dfg ∈ fullTree p st, eraseFG Dfg = D ∧
        ∀ A, Block.Preceq A D → A ∈ st.base.blocks ∧
          GridCO.stampBlock st.base A < SA.proposalTime p.toParams pt.s := by
    intro i x st hduty hx
    obtain ⟨k, hk⟩ := hprev x (hx ▸ hprop.1.2)
    exact wc_proposalPath_of_previous hs hnr hs2 hduty hk (hFP i x st hduty hx).1
  have hHP : ∀ i x st, x ∈ rho.honest → WCDutyInput p c E rho i x (.head pt.s) st →
      ∃ Dfg ∈ KitFG.storeFrameView (heightView p) st.fg (voterBlocks p st pt.s),
        eraseFG Dfg = D ∧ ∀ A, Block.Preceq A D → A ∈ st.base.blocks ∧
          GridCO.stampBlock st.base A < SA.freezeTime p.toParams (pt.s - 1) := by
    intro i x st hx hduty
    obtain ⟨k, hk⟩ := hprev x hx
    exact wc_headPath_of_previous hs hnr hs2 hduty hk (hFH i x st hx hduty).1
  obtain ⟨q, hsq⟩ : ∃ q : Slot, pt.s = q + 2 :=
    ⟨pt.s - 2, by simp only [Slot] at hs2 ⊢; omega⟩
  have hprevLabel : pt.s - 1 = q + 1 := by rw [hsq]; simp only [Slot]; omega
  have huq : w.u ≤ q := by simp only [Slot] at hstart hsq ⊢; omega
  have hGST : E.t_GST ≤ SA.voteTime p.toParams (q + 1) := by
    refine hseed.firstVoteAfterGST.trans ?_
    change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * ((q + 1 : Nat) : Time) + p.Δ
    have hcast : (w.u : Time) ≤ q := Nat.cast_le.mpr huq
    push_cast
    nlinarith [p.deltaPos]
  have hhor : SA.voteTime p.toParams (q + 2) ≤ rho.horizon := by
    refine le_trans ?_ hgate
    rw [hsq]
    change 4 * p.Δ * ((q + 2 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * ((q + 2 : Nat) : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hpartPrev := hpart (q + 1) (by simp only [Slot] at huq ⊢; omega) (by
    refine le_trans ?_ hhor
    change 4 * p.Δ * ((q + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * ((q + 2 : Nat) : Time) + p.Δ
    push_cast
    nlinarith [p.deltaPos])
  have hprevQ : ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y (q + 1) D := by
    simpa only [hprevLabel] using hprev
  have hheadWalk : ∀ x ∈ rho.honest, ∀ H,
      headAtLabel p c E rho x pt.s = some H → Block.Preceq D H := by
    intro x hx H hH
    change (postClock E rho x (SA.voteTime p.toParams pt.s)).map _ = some H at hH
    rw [postClock_def, preTick_def] at hH
    cases hidx : V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams pt.s) with
    | none => simp only [hidx, Option.map_none, reduceCtorEq] at hH
    | some i =>
      simp only [hidx, Option.map_some, Option.some.injEq] at hH
      have he := V2.D.Run.tickIdx?_spec hidx
      let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams pt.s)
      have hduty : WCDutyInput p c E rho i x (.head pt.s) st :=
        ⟨(List.getElem?_eq_some_iff.mp he).1,
          ⟨_, he, Or.inr (Or.inl ⟨pt.s, rfl, rfl, rfl⟩)⟩⟩
      obtain ⟨hf, hlive⟩ := hFH i x st hx hduty
      obtain ⟨Dfg, hm, hD, hpath⟩ := hHP i x st hx hduty
      have hInv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x)
        (SA.voteTime p.toParams pt.s)
      have hcounts := wc_headCounts hvalid hnr hdelta hcstar hroots hmono ΔF hsync q D
        hGST hpartPrev hhor hprevQ hx (hsq ▸ he) (hsq ▸ hf)
      have hcountsS : ∀ L, Block.Preceq L D → RetainedTargetScores p st pt.s L ∧
          ∀ B, Block.compatible L B = false →
            RetainedWalk.ts p st pt.s B < RetainedWalk.ts p st pt.s L := by
        simpa only [← hsq] using hcounts
      have hclosed : ∀ A, FGBlock.Preceq A Dfg → A ∈ voterBlocks p st pt.s := by
        intro A hAD
        obtain ⟨B, hB, hBA⟩ := eraseFG_ancestor_mem hInv.fg.closed
          ((Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1) (eraseFG_preceq hAD)
        have hA : A ∈ st.fg.TF := (eraseFG_injective hBA) ▸ hB
        exact Finset.mem_filter.mpr ⟨hA, Bool.or_eq_true_iff.mpr (Or.inl
          (decide_eq_true (hpath (eraseFG A) (hD ▸ eraseFG_preceq hAD)).2))⟩
      have hw := fgsa_headInTree_covers_of_transfer p st _ _ _ D
        (block_compatible_of_common hlive (block_preceq_refl D))
        (wc_frameAncestry hInv hf hD (voterBlocks p st pt.s)
          (fun _ h => (Finset.mem_filter.mp h).1) (Finset.mem_filter.mp hm).1 hclosed)
        (hcountsS D (block_preceq_refl D)).1.majority
        (hcountsS D (block_preceq_refl D)).2
      have hsne : pt.s ≠ 0 := by simp only [Slot] at hs2 ⊢; omega
      have hread : headVote p st pt.s = H := hH
      change (if pt.s = 0 then .genesis else headInTree p st
        (erasedList st (KitFG.storeFrameView (heightView p) st.fg (voterBlocks p st pt.s)))
        (headVotes p st pt.s) (headSupport p st pt.s)) = H at hread
      rw [ite_eq_right hsne] at hread
      exact hread ▸ hw
  obtain ⟨ip, N, hN, hip, hem, _⟩ := proposal_read_named p c E rho hs hprop
  let src := clock p (storeAt p c E rho ip
    (V2.D.proposerOf rho (fgsaInterface p c) pt.s)) (SA.proposalTime p.toParams pt.s)
  have hdp : WCDutyInput p c E rho ip
      (V2.D.proposerOf rho (fgsaInterface p c) pt.s) (.proposal pt.s) src :=
    ⟨(List.getElem?_eq_some_iff.mp hip).1, ⟨_, hip, Or.inl ⟨pt.s, rfl, rfl, rfl⟩⟩⟩
  obtain ⟨hfs, hlas⟩ := hFP _ _ src hdp rfl
  obtain ⟨Dfg, hDsrc, hD, _⟩ := hPP _ _ src hdp rfl
  have hInv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip
    (V2.D.proposerOf rho (fgsaInterface p c) pt.s)) (SA.proposalTime p.toParams pt.s)
  have hcounts := wc_proposalCounts hvalid hnr hdelta hcstar hroots hmono ΔF hsync q D
    hGST hpartPrev hhor hprevQ hprop.1.2
    (by simpa only [← hsq] using hip) (by simpa only [← hsq] using hfs)
  have hcountsS : ∀ L, Block.Preceq L D →
      GridCO.voterCount (proposerVotes src pt.s) < 2 * RetainedWalk.ss src pt.s L ∧
      ∀ B, Block.compatible L B = false →
        RetainedWalk.ss src pt.s B < RetainedWalk.ss src pt.s L := by
    simpa only [← hsq] using hcounts
  have hclosed : ∀ A, FGBlock.Preceq A Dfg → A ∈ src.fg.TF := by
    intro A hAD
    obtain ⟨B, hB, hBA⟩ := eraseFG_ancestor_mem hInv.fg.closed
      (Finset.mem_filter.mp hDsrc).1 (eraseFG_preceq hAD)
    exact (eraseFG_injective hBA) ▸ hB
  have hwalk := fgsa_headInTree_covers_of_transfer p src _ _ _ D
    (block_compatible_of_common hlas (block_preceq_refl D))
    (wc_frameAncestry hInv hfs hD src.fg.TF (fun _ h => h)
      (Finset.mem_filter.mp hDsrc).1 hclosed)
    (hcountsS D (block_preceq_refl D)).1 (hcountsS D (block_preceq_refl D)).2
  have hem' := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hem'
  have hp := (fgsa_emits_proposal E rho _ _ _ pt.s _).mp hem'
  have hparent := (fgsa_walkRun_proposal_parent p src pt.s _ N hp.2.2.2).2.2
  have hDP : Block.Preceq D pt.P.parent := by rw [← hN, hparent]; exact hwalk
  exact ⟨D, hmember, hQD, hmax, hFP, hFH, hprev, hPP, hHP, hheadWalk, hDP⟩

omit [Fintype V] in
private theorem wcg_proposalWindows (hseed : WCSeed p c E rho w iStar)
    (s : Slot) (hstart : w.u + 2 ≤ s)
    (hgate : SA.gateTime p.toParams s ≤ rho.horizon) :
    E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ ∧
      SA.voteTime p.toParams s ≤ rho.horizon := by
  have hd := p.deltaPos
  have hcast : (w.u : Time) + 2 ≤ (s : Time) := by exact_mod_cast hstart
  constructor
  · refine hseed.firstVoteAfterGST.trans ?_
    change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (s : Time) - p.Δ
    push_cast
    nlinarith
  · refine le_trans ?_ hgate
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith

/-- WC J3, plan §6.10; DC exact proposal: the retained suffix and endpoint give P.
The proof matches the reviewed exact-adoption Statement. -/
theorem wcg_exactProposal (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCGExactProposalStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot hadmission
  obtain ⟨ip, N, Dfg, hN, hip, hem, hreads⟩ := wc_retainedReads hvalid hnr hdelta
    hcstar hroots hmono ΔF hsync hpart hseed pt D hstart hprop hgate hpivot
  obtain ⟨hGST, hhor⟩ := wcg_proposalWindows hseed pt.s hstart hgate
  have htime : SA.proposalTime p.toParams pt.s - p.Δ + E.Δ ≤
      SA.proposalTime p.toParams pt.s := by rw [hdelta]; exact le_of_eq (sub_add_cancel _ _)
  have hpv : SA.proposalTime p.toParams pt.s ≤ SA.voteTime p.toParams pt.s := by
    change 4 * p.Δ * (pt.s : Time) ≤ 4 * p.Δ * (pt.s : Time) + p.Δ
    linarith [p.deltaPos]
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.proposalTime p.toParams pt.s - p.Δ) (SA.proposalTime p.toParams pt.s)
    hsync (fgsaDelay_nonrow E.Δ ΔF) hGST htime (hpv.trans hhor)
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.proposalTime p.toParams pt.s - p.Δ) (SA.voteTime p.toParams pt.s)
    hsync (fgsaDelay_nonrow E.Δ ΔF) hGST (htime.trans hpv) hhor
  have hg := fgsa_retainedExactHead_geometry_on_run E rho hvalid hnr hdelta pt.s
    hwalk hscore hprop.1.2 hip rfl N hem Dfg hreads hroots
  simpa only [hN] using
    exactService_head_of_retained_proposal E rho hvalid hdelta pt.s hip N hem Dfg hg hhor

omit [Fintype V] in
/-- WC J3, plan §6.10; DC named receipt: decode preserves the complete signed body. -/
private theorem wcg_blockObject {o : Obj p} {B : Block} (h : blockOf? p o = some B) :
    ∃ s N, o = ofWire p ⟨.proposer s, .proposal N⟩ ∧ N.erase = B := by
  change (match (toWire p o).decode with
    | some (.block _ N) => some N.erase
    | _ => none) = some B at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i s N
    refine ⟨s, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- WC J3, plan §6.10; DC full admission: retain the exact emitted named proposal.
The delivery and stamp are strict before the HEAD tick, also for sleeping readers. -/
theorem wcg_proposalAdmission (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCGProposalAdmissionStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot x hx
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨ip, N, hN, hip, hem, _⟩ := proposal_read_named p c E rho hs hprop
  obtain ⟨hGST, hhor⟩ := wcg_proposalWindows hseed pt.s hstart hgate
  have hGSTp : E.t_GST ≤ SA.proposalTime p.toParams pt.s :=
    hGST.trans (sub_le_self _ p.deltaPos.le)
  let o : Obj p := ofWire p ⟨.proposer pt.s, .proposal N⟩
  have htrigger : Gen.V2.Duty.Trigger E rho o (SA.proposalTime p.toParams pt.s) :=
    Or.inl ⟨_, hprop.1.2, ip, hip, hem⟩
  let dl := fun t => max t E.t_GST + E.Δ
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
    (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  have hdeadline : dl (SA.proposalTime p.toParams pt.s) =
      SA.voteTime p.toParams pt.s := by
    dsimp only [dl]
    rw [max_eq_left hGSTp, hdelta]
    rfl
  have hvt : ((4 * pt.s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams pt.s := by
    push_cast
    change (4 * (pt.s : Time) + 1) * p.Δ = 4 * p.Δ * (pt.s : Time) + p.Δ
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hs hdelta x hx (4 * pt.s + 1)
    (hvt ▸ hhor)
  rw [hvt] at hih
  let st := clock p (storeAt p c E rho ih x) (SA.voteTime p.toParams pt.s)
  have hduty : WCDutyInput p c E rho ih x (.head pt.s) st :=
    ⟨(List.getElem?_eq_some_iff.mp hih).1,
      ⟨_, hih, Or.inr (Or.inl ⟨pt.s, rfl, rfl, rfl⟩)⟩⟩
  have hF := block_preceq_trans (hpivot.headFrame ih x st hx hduty).1.finalRoot
    (block_preceq_trans (hpivot.headFrame ih x st hx hduty).1.rootBelow hpivot.parent)
  have hpar : Block.Preceq pt.P.parent pt.P := by
    cases pt.P <;> first | exact block_preceq_refl _ |
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
  have hcompat : Block.Compatible N.erase
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams pt.s) x).st.fg.F) := by
    have hb : Block.Preceq (eraseFG (rho.stateBefore E ih x).st.fg.F) pt.P := by
      change Block.Preceq (eraseFG (storeAt p c E rho ih x).fg.F) pt.P
      simpa only [st, clock_fg] using block_preceq_trans hF hpar
    rw [fgsa_preTick_eq_timeRead E rho hs hnr hih] at hb
    rw [hN]
    exact block_compatible_of_common (block_preceq_refl _) hb
  obtain ⟨Y, hY, hYB⟩ := fgsa_proposal_receipt E rho hroots hdelta hvalid hnr dl
    rho.horizon pt.s N (SA.proposalTime p.toParams pt.s) x hD htrigger hx
    (hdeadline.symm ▸ hhor) (by rw [hdeadline]; exact lt_add_of_pos_right _ p.deltaPos)
    (hdeadline.symm ▸ hcompat)
  rw [hdeadline] at hY
  let k := V2.D.Run.idxBefore rho (SA.voteTime p.toParams pt.s)
  have hstored : N.erase ∈ (storeAt p c E rho k x).base.blocks := by
    apply ((cstoreInv_stateBefore E rho k x).baseTree _).mpr
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact ⟨Y, hY, hYB⟩
  have hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho
      (SA.voteTime p.toParams pt.s) x) o = false := by
    change excludesS p _ o = false
    dsimp only [excludesS, o]
    rw [toWire_ofWire]
    change (blockExcluded _ N.erase || invalidForParent p _ N) = false
    have hc : activeCompatible (V2.D.Run.stateBeforeTime E rho
        (SA.voteTime p.toParams pt.s) x).st N.erase = true := by
      exact hcompat
    rw [blockExcluded, hc, Bool.not_true, Bool.false_or]
    exact fgsa_trigger_invalid_false E rho o _ pt.s N htrigger rfl _
  have hscope := proposal_trigger_in_scope E rho o pt.s N rfl dl rho.horizon
    (SA.proposalTime p.toParams pt.s) x hD htrigger hx
    (hdeadline.symm ▸ hhor) (hdeadline.symm ▸ hNX)
  have hm := hstored
  change _ ∈ (rho.stateBefore E k x).st.base.blocks at hm
  rw [← (metaInv_stateBefore E rho k x).stampKeys] at hm
  obtain ⟨⟨B, stamp⟩, hm, hB⟩ := List.mem_map.mp hm
  dsimp only at hB
  subst B
  have hmEmit := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmEmit
  have hp := (fgsa_emits_proposal E rho _ _ _ pt.s _).mp hmEmit
  have hslot := (fgsa_scoreRun_proposal_pools p _ pt.s _ N hp.2.2.2).1
  have hne : N.erase ≠ .genesis := by
    intro he
    have hzero : N.erase.slot = 0 := he ▸ rfl
    simp only [Slot] at hslot hstart hzero
    omega
  rcases fgsa_block_stamp_source E rho k x N.erase stamp hm with hg |
    ⟨j, hj, t, o', ho', ha, _⟩
  · exact (hne hg.1).elim
  obtain ⟨s', M, rfl, hM⟩ := wcg_blockObject ho'
  have hdecode : (toWire p (ofWire p ⟨.proposer s', .proposal M⟩)).decode =
      some (.block s' M) := by rw [toWire_ofWire]; rfl
  obtain ⟨parent, he, hh⟩ := ha.1
  have heparent := proposal_handlesS_direct _ parent _ s' M hdecode hh
  subst parent
  have hMscope := proposal_handle_in_scope E rho _ s' M rfl j x t ha.1
  have hMN := namedScope_erase_injective E rho hroots hMscope hscope hM
  subst M
  have hwf := hvalid.wire j x _ t he
  change wellFormed p (toWire p (ofWire p ⟨.proposer s', .proposal N⟩)) = true at hwf
  rw [toWire_ofWire] at hwf
  change (N.erase != .genesis && s' == N.erase.slot && _ && _ && _ && _ && _) = true at hwf
  have h6 := (Bool.and_eq_true_iff.mp hwf).1
  have h5 := (Bool.and_eq_true_iff.mp h6).1
  have h4 := (Bool.and_eq_true_iff.mp h5).1
  have h3 := (Bool.and_eq_true_iff.mp h4).1
  have h2 := (Bool.and_eq_true_iff.mp h3).1
  have hlabel : s' = pt.s :=
    (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h2).2).trans hslot
  subst s'
  have hbefore := (Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hj
  refine ⟨⟨N, j, _, t, rfl, hN, he, hbefore, Or.inl ha,
    ⟨_, ip, rfl, hip, hem⟩, ?_⟩⟩
  intro i st' hd
  obtain ⟨hi, rfl⟩ := wc_headInput hd
  have hki : k ≤ i := by
    by_contra hn
    have hc := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp (Nat.lt_of_not_ge hn)
    exact lt_irrefl _ hc
  have hc := fgsa_store_cumulative p c E rho hnr hki x
  have hmem := hc.2.1.subset hstored
  obtain ⟨M, hM, hMB⟩ := (namedBodies_erase_domain p _ (cstoreInv_stateBefore E rho i x)
    (metaInv_stateBefore E rho i x) N.erase).mp hmem
  have hMN := namedScope_erase_injective E rho hroots
    (namedScope_held E rho hx i hM) hscope hMB
  have hpath : ∀ A, Block.Preceq A pt.P → A ∈ (storeAt p c E rho i x).base.blocks := by
    intro A hA
    obtain ⟨W, hW, hWB⟩ := ((cstoreInv_stateBefore E rho i x).baseTree _).mp hmem
    obtain ⟨Af, hAf, hAfA⟩ := eraseFG_ancestor_mem
      (cstoreInv_stateBefore E rho i x).fg.closed hW (hWB ▸ hN.symm ▸ hA)
    exact ((cstoreInv_stateBefore E rho i x).baseTree A).mpr ⟨Af, hAf, hAfA⟩
  refine ⟨hj.trans_le hki, ?_, ?_, ?_⟩
  · rw [clock_namedBodies]
    exact hMN ▸ hM
  · intro A hA
    rw [clock_base_blocks]
    exact hpath A hA
  · have ht : 0 < SA.voteTime p.toParams pt.s := by
      change 0 < 4 * p.Δ * (pt.s : Time) + p.Δ
      nlinarith [p.deltaPos, Nat.cast_nonneg (α := Int) pt.s]
    rw [← hN]
    have hstamp := fgsa_gateReceipt_block_stamp_lt E rho hs hnr hi ht N.erase hmem
    have hkeys : N.erase ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
      change N.erase ∈ (rho.stateBefore E i x).st.base.blockStamp.map Prod.fst
      rw [(metaInv_stateBefore E rho i x).stampKeys]
      exact hmem
    rw [inclusion_stampBlock_of_prefix (by rw [(clock_cumulative p _ _).2.2.1]) hkeys]
    exact hstamp

omit [Fintype V] in
private theorem wcg_gate_after_cut (hs : V2.D.ScheduleWellFormed E rho)
    (hseed : WCSeed p c E rho w iStar) {i : Nat} {x : V} {s : Slot}
    (he : IsGateTick p c rho i x s) (hstart : w.u < s) : iStar ≤ i := by
  have ht : SA.gateTime p.toParams w.u < SA.gateTime p.toParams s := by
    have hc : (w.u : Time) < s := Nat.cast_lt.mpr hstart
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ < 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  rw [hseed.cut]
  refine (preIdx_le_afterTicksIdx E rho hs _).2.trans ?_
  have hm := V2.D.Engine.read_length_mono (rho := rho)
    (SA.gateTime p.toParams w.u) (SA.gateTime p.toParams s - 1) (by
      simp only [Time] at ht ⊢; omega)
  exact hm.trans (Nat.le_of_not_lt
    ((V2.D.Engine.index_lt_read_length_iff hs (SA.gateTime p.toParams s - 1) he).not.mpr (by
      change ¬ SA.gateTime p.toParams s ≤ SA.gateTime p.toParams s - 1
      exact not_le_of_gt (sub_lt_self _ (by decide : (0 : Time) < 1)))))

/-- WC J3, plan §6.11; DC six-Delta inclusion: serve both getters at every later read.
The sole producer premise is the reviewed live-frame Statement. -/
theorem wcg_inclusion6 (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframeLive : WCGSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCGInclusion6Statement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have hs := hvalid.toScheduleWellFormed
  have hi := hinv rho.events.length ⟨hseed.within, le_rfl⟩
  obtain ⟨D, hpivot⟩ := wcg_proposalPivot ΔF w iStar hframeLive
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have had := wcg_proposalAdmission ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot
  have hhead := wcg_exactProposal ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot had
  obtain ⟨hQP, hprior⟩ := wc_prior_below_proposal hs hi pt D hpivot hhead _ hprop.1.2
  have hfl := hframeLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ
    haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc
    hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed
  have hGST : E.t_GST ≤ SA.voteTime p.toParams pt.s := by
    refine hseed.firstVoteAfterGST.trans ?_
    have hc : (w.u : Time) + 2 ≤ pt.s := by exact_mod_cast hstart
    change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (pt.s : Time) + p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have hvg : SA.voteTime p.toParams pt.s + E.Δ ≤ SA.gateTime p.toParams pt.s := by
    rw [hdelta]
    change 4 * p.Δ * (pt.s : Time) + p.Δ + p.Δ ≤
      4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.voteTime p.toParams pt.s) (SA.gateTime p.toParams pt.s)
    hsync (fgsaDelay_nonrow E.Δ ΔF) hGST hvg hgate
  have hpartS := hpart pt.s (by simp only [Slot] at hstart ⊢; omega)
    ((le_add_of_nonneg_right (hdelta ▸ p.deltaPos.le)).trans (hvg.trans hgate))
  have hgates := wc_proposal_gates hvalid hnr hdelta hcstar hroots hseed hi pt
    hstart hgate hhead had hQP hprior hfl hSync hpartS
  intro g hg t x ht hx
  have hgt : ((4 * pt.s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams pt.s := by
    push_cast
    change (4 * (pt.s : Time) + 6) * p.Δ = 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    ring
  obtain ⟨i, he, _⟩ := fgsa_tick_total E rho hs hdelta x hx (4 * pt.s + 6) (hgt ▸ hgate)
  rw [hgt] at he
  have hcut := wcg_gate_after_cut hs hseed he (by simp only [Slot] at hstart ⊢; omega)
  have hread : i + 1 ≤ timeIdx rho t :=
    (V2.D.Engine.index_lt_read_length_iff hs t he).mpr ht.1
  have hout := (hgates i x hx he).2
  have hm := wc_suffix_mono hi (hcut.trans (Nat.le_succ i)) hread
    (List.length_filter_le _ _) hx
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [fgsa_outputAt_eq_S_at E rho hs g hg x t]
  exact block_preceq_trans hout hm


/-- The companion live frame discharges the only separate inclusion producer. -/
theorem wcg_inclusion6_proved (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCGInclusion6Statement p c E rho ΔF w iStar :=
  wcg_inclusion6 ΔF w iStar wcg_seededFrameLive

end AvailableChain.FGSA.Run

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §8 Job 4; DC bounded weak continuation: join the actual lane producers.
The separate [L] premises and one replayed seed give safety, inclusion, and growth. -/
theorem wcg_seededLiveAt (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExact p c E rho)
  (_hmeta : RFrame p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → WeakContinuationLiveAt₂ p c E rho w.u w.QStar iStar ΔF := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed
  have hi := wcg_seededInduction wc_finalityTargetEarlier hvalid hlinked hcstar hnr hdelta
    hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed
  have hf := wcg_finalBelow wc_finalityTargetEarlier hvalid hlinked hcstar hnr hdelta hroots
    hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed hi
  have hincl := wcg_inclusion6_proved ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync
    hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hseed hi
  exact wcg_live_of_invariant_inclusion
    ⟨hvalid, hlinked, hcstar, hnr, hdelta, hroots⟩ hseed hi
    (fun i x y hlo hhi hx hy => hf i x y ⟨hlo, hhi⟩ hx hy) hincl

end AvailableChain.FGSA.Run

namespace AvailableChain.FGSA.Run
open SimplexFG KitFG
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [Fintype V] in
/-- WC J1; DC named scope: every honest-holder row has its original action index.
Rejected delivered proposals count. Emitted-only proposals do not supply scope. -/
theorem wcg_scopedRowOrigins (hv : V2.D.ExecutionValid E rho)
    (D : FGBlock (Fin p.n)) (hD : RootBlockInRun p c E rho (eraseFG D))
    (a : Row (Fin p.n)) (ha : a ∈ chainRows D)
    (hh : rho.seatOf (.base .fg) a.signer ∈ rho.honest) :
    ∃ j r wire, HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer := by
  obtain ⟨N, ⟨M, hM, hNM⟩, hN⟩ := hD
  have hDM : Block.Preceq (eraseFG D) M.erase := by
    rw [← hN]
    exact named_preceq_erase hNM
  have carriage : FinalityCarriage p c E rho (chainRows D) := by
    rcases hM with ⟨x, o, t, hd, ho⟩ | ⟨x, hx, i, hm⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hd
      exact delivered_runBlock_carriage p c E rho hv j x o t hj M ho D hDM
    · have hr := namedOrigin_reachable E rho i x
      have hb := ((reachable_named_store p hr).2.1 M.erase).mpr ⟨M, hm, rfl⟩
      obtain ⟨W, hW, he⟩ := (cstoreInv_stateBefore E rho i x).baseTree M.erase |>.mp hb
      have hDW : FGBlock.Preceq D W := eraseFG_preceq_iff.mp (he ▸ hDM)
      have hstored := KitFG.ancestor_closed_of_parent_closed _
        (cstoreInv_stateBefore E rho i x).fg.closed W hW D hDW
      rw [FinalityCarriage_def]
      exact held_chain_row_origin p c E rho hv.toUnforgeableSignatures i x D ⟨hx, hstored⟩
  rw [FinalityCarriage_def] at carriage
  obtain ⟨wire, _, hd, auth, origin⟩ := carriage a ha
  have signer : RowSigner p c rho wire (rho.seatOf (.base .fg) a.signer) :=
    ⟨a.signer, auth, rfl⟩
  obtain ⟨j, t, hj, hem⟩ := origin _ signer hh
  obtain ⟨au, body⟩ := wire
  dsimp only at auth
  subst au
  obtain ⟨_, _, r, ht, _⟩ := (fgsa_emitsAt_row E rho j _ t hj a.signer body).mp hem
  exact ⟨j, r, ⟨.seat .fg a.signer, body⟩, ⟨hh, ht ▸ hj, hem⟩, hd, rfl⟩

/-- WC J1; DC premise discharge: supply every separate lane input to its consumer.
The consumer telescope is the literal [L] expansion; no foundation bundle is passed. -/
theorem wcg_dischargeL {ΔF : Time} {w : HealingWitness} {Result : Prop}
    (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hdeltaF : E.Δ ≤ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (haccountable : FinalitySlashableBound p c E rho)
    (hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
    (consume : ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExact p c E rho)
  (_hmeta : RFrame p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J), Result) : Result := by
  have hs := hb.valid.toScheduleWellFormed
  have hstore := fgsa_rStore p c E rho
  apply consume hb.valid hb.linked hb.cstar hb.noRestart hb.delta hb.idealization
    hsync hdeltaF hq haccountable hpart
    hstore (fgsa_rStoreCumul p c E rho) (fgsa_rMono p c E rho)
    (fgsa_rActive p c E rho) (fgsa_rFrameExact p c E rho) (fgsa_rFrame p c E rho)
    (fgsa_rRec p c E rho) (fgsa_rGeo p c E rho) (fgsa_rCert p c E rho)
    (sourceDiscipline_tSrc p c E rho hs) (sourceDiscipline_labelBound p c E rho hs)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (fgsa_clientSafeAll p c E rho hb.linked)
  · intro j x r a e ha he
    exact sourceDiscipline_emittedName p c E rho hs ha he
  · intro i x row hr
    exact storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
  · exact fgsa_leaseOrigins_lastWrite p c E rho hs
  · exact fgsa_leaseOrigins_fastWrites p c E rho hs
  · exact fgsa_leaseOrigins_ancestorDeadlines p c E rho
  · exact held_chain_row_origin_before p c E rho hb.valid.toUnforgeableSignatures hs
  · exact wcg_scopedRowOrigins hb.valid
  · intro j z r a u ha hsign hd fp hf
    exact cap_finality_head p c E rho ha hsign hd fp hf


/-- Discharge all internal producers from the continuation regime and a seed.
No invariant, service, or inclusion proof is required from this caller. -/
theorem wcg_liveOfSeed {ΔF : Time} {w : HealingWitness} {iStar : Nat}
    (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hdeltaF : E.Δ ≤ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (ha : FinalitySlashableBound p c E rho)
    (hp : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
    (hs : WCSeed p c E rho w iStar) :
    WeakContinuationLiveAt₂ p c E rho w.u w.QStar iStar ΔF := by
  apply wcg_dischargeL hb hsync hdeltaF hq ha hp
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
  exact wcg_seededLiveAt ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs

end AvailableChain.FGSA.Run

namespace AvailableChain.FGSA.Run
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] [Fintype V] in
/-- Vote times after the seed's first vote stay after GST. -/
private theorem vote_after_first {w : HealingWitness} {s : Slot}
    (hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1)) (hs : w.u + 1 ≤ s) :
    E.t_GST ≤ SA.voteTime p.toParams s := by
  have hcast : ((w.u + 1 : Nat) : Time) ≤ (s : Time) := Int.ofNat_le.mpr hs
  change E.t_GST ≤ 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ at hfirst
  change E.t_GST ≤ 4 * p.Δ * (s : Time) + p.Δ
  nlinarith [p.deltaPos]

/-- The source's one-third bound supplies the public slashing premise. -/
private theorem source_accountable {G ΔF : Time}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF) :
    FinalitySlashableBound p c E rho := by
  have h := fgsa_slashableBound_of_base p c E rho hS.base hS.fault
  rw [FinalitySlashableBound_def]
  rw [FGSASlashableBound_def] at h
  intro K W hK hW
  rw [FinalityBlock_def] at hK hW
  exact h K W (by rwa [FinalityRunBlock_def]) (by rwa [FinalityRunBlock_def])

/-- Strong-source full participation supplies every covered vote majority. -/
private theorem source_votePart {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1)) :
    ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card := by
  intro s hs hhor
  have hg := vote_after_first hfirst hs
  have hall : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun x hx => hS.awake x hx _ hg hhor)
  rw [hall]
  have hn := card_eq_n_of_linked hS.base.linked
  have hcard : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hh := Finset.card_le_univ rho.honest
    omega
  have hf := hS.fault
  have hp := p.nPos
  omega


/-- The selected strong source has the live result for its own seed. -/
theorem wcg_sourceLive {G ΔF : Time} {w : HealingWitness} {iSource : Nat}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hseed : WCSeed p c E rho w iSource) :
    WeakContinuationLiveAt₂ p c E rho w.u w.QStar iSource ΔF :=
  wcg_liveOfSeed hS.base hS.sync hS.deltaF (fgsa_faultQ_of_count p hS.fault)
    (source_accountable hS) (source_votePart hS hseed.firstVoteAfterGST) hseed

/-- A nonempty growth continuation supplies the entire vote participation
interval from the source seed's first vote onward. -/
theorem wcg_nonemptyLive {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {G ΔF : Time} {w : HealingWitness} {i : Nat}
    (hS : StrongRecoverySearchPrefix₂ p c E₀ source G ΔF)
    (hc : CleanGrowthContinuation₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon) (hseed : WCSeed p c E rho w i) :
    WeakContinuationLiveAt₂ p c E rho w.u w.QStar i ΔF := by
  apply wcg_liveOfSeed hc.base hc.sync hc.deltaF (wcg_suffix_faultQ hc hne)
    hc.accountable _ hseed
  intro s hs hhor
  have hg := vote_after_first hseed.firstVoteAfterGST hs
  by_cases ht : source.horizon < SA.voteTime p.toParams s
  · exact hc.participation _ ht hhor
  have ht' := le_of_not_gt ht
  have hall : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    apply Finset.filter_eq_self.mpr
    intro x hx
    rw [hc.agrees.awake x hx _ ht']
    exact hS.awake x (hc.agrees.honest hx) _ (hc.agrees.gst ▸ hg) ht'
  rw [hall]
  have hp := hc.participation rho.horizon hne le_rfl
  have hcard : (Gen.V2.Duty.awakeHonest E rho rho.horizon).card ≤ rho.honest.card := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.card_filter_le _ _
  exact hp.trans_le hcard
end AvailableChain.FGSA.Run


namespace AvailableChain.FGSA.Run
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Empty-suffix safety, inclusion, and growth use only the strong source
and retained local agreement. No continuation participation bound is needed. -/
theorem wcg_emptyLive {G ΔF : Time} {w : HealingWitness} {iSource : Nat}
    (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanGrowthContinuation₂ p c E source E' rho ΔF)
    (hend : rho.horizon = source.horizon) (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon) :
    WeakContinuationLiveAt₂ p c E' rho w.u w.QStar
      (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF := by
  apply wcg_empty_live_of_finalBelow hc.agrees hc.base hS.base.valid.toScheduleWellFormed
    hS.base.noRestart hend hseed hgate (wcg_sourceLive hS hseed)
  apply wcg_dischargeL hS.base hS.sync hS.deltaF (fgsa_faultQ_of_count p hS.fault)
    (source_accountable hS) (source_votePart hS hseed.firstVoteAfterGST)
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
  have hinv := (wcg_seededInduction wcg_finalityTargetEarlier) hvalid hlinked hcstar hnr hdelta
    hroots hsync hdeltaF hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta
    hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines
    hheldRows hscopeRows hfinalHead hseed
  exact wcg_empty_finalBelow hc.agrees hvalid.toScheduleWellFormed
    hc.base.valid.toScheduleWellFormed hend hseed hinv
    (wcg_finalityTargetEarlier hvalid hlinked hfaultQ hroots hheldRows hfinalHead hqc hemitted)
    (wcg_service4 hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable
      hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
      hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead hseed hinv)
end AvailableChain.FGSA.Run

end
