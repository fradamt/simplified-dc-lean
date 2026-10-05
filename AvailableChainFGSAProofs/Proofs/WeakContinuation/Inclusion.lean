module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.ExactProposal
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

/-! WC J3, plan §6.11; DC persistent proposal inclusion.
Earlier labels use retrospective transfer. Gates at one time use event induction. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC J3, plan §6.11; DC pending result: exact HEAD bounds label s−1. -/
theorem wc_prior_below_proposal
    (hs : V2.D.ScheduleWellFormed E rho)
    (hi : WCInv p c E rho w iStar rho.events.length) (pt : PtSP) (D : Block)
    (hpivot : WCProposalPivot p c E rho w iStar pt D)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y pt.s = some pt.P)
    (y : V) (hy : y ∈ rho.honest) :
    Block.Preceq w.QStar pt.P ∧
      ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
        r < pt.s → Block.Preceq B pt.P := by
  have hDP := hpivot.headWalk y hy pt.P (hhead y hy)
  refine ⟨block_preceq_trans hpivot.greatestSeed hDP, ?_⟩
  intro j x r B hB hr
  by_cases hprev : r + 1 = pt.s
  · obtain ⟨k, _, hk⟩ := hi.retrospective j x r B hB y hy
    have he : headAtIdx p c E rho k (r + 1) = pt.P := by
      have hh := hhead y hy
      rw [← hprev] at hh
      change (postClock E rho y (SA.voteTime p.toParams (r + 1))).map _ = _ at hh
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk.event] at hh
      dsimp only [headAtIdx]
      rw [hk.event]
      exact Option.some.inj hh
    exact he ▸ hk.covers
  · have hle : r ≤ pt.s - 2 := by simp only [Slot] at hr hprev ⊢; omega
    exact block_preceq_trans (hpivot.greatest j x r B hB hle) hDP

/-- WC J3, plan §6.11; DC cut order: every later gate input is after the seed. -/
private theorem wc_gate_after_cut (hs : V2.D.ScheduleWellFormed E rho)
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

/-- WC J3, plan §6.11; DC admitted path: the complete proposal remains at its gate. -/
private theorem wc_admitted_at_gate (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ) (pt : PtSP)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (he : IsGateTick p c rho i x pt.s)
    (had : WCProposalAdmittedBeforeVote p c E rho x pt) :
    ∃ Bfg ∈ (storeAt p c E rho i x).fg.TF, eraseFG Bfg = pt.P := by
  have hvg : SA.voteTime p.toParams pt.s < SA.gateTime p.toParams pt.s := by
    change 4 * p.Δ * (pt.s : Time) + p.Δ < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hvt : ((4 * pt.s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams pt.s := by
    push_cast
    change (4 * (pt.s : Time) + 1) * p.Δ = 4 * p.Δ * (pt.s : Time) + p.Δ
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hdelta x hx (4 * pt.s + 1)
    (hvt ▸ hvg.le.trans hgate)
  rw [hvt] at hk
  have hd : WCDutyInput p c E rho k x (.head pt.s)
      (clock p (storeAt p c E rho k x) (SA.voteTime p.toParams pt.s)) :=
    ⟨(List.getElem?_eq_some_iff.mp hk).1,
      ⟨_, hk, Or.inr (Or.inl ⟨pt.s, rfl, rfl, rfl⟩)⟩⟩
  obtain ⟨N, j, o, t, _, _, _, _, _, _, hkeep⟩ := had.admission
  have hm := (hkeep k _ hd).2.2.1 pt.P (block_preceq_refl _)
  rw [clock_base_blocks] at hm
  have hki := V2.D.Engine.eventIndex_lt_of_time_lt hs hk he hvg
  exact ((cstoreInv_stateBefore E rho i x).baseTree pt.P).mp
    ((fgsa_store_cumulative p c E rho hnr hki.le x).2.1.subset hm)

/-- WC J3, plan §6.11; DC live guard: every lease left by the clock is live. -/
private theorem wc_clockPre_live (st : State p.n) (t : Time) (row : Block × Nat × Time)
    (h : row ∈ (clockPre p st t).base.obligations) : t < row.2.2 := by
  obtain ⟨K, g, d⟩ := row
  unfold clockPre at h
  dsimp only at h
  split_ifs at h <;>
    first
    | exact of_decide_eq_true (List.mem_filter.mp h).2
    | exact of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp h).1).2

/-- WC J3, plan §6.11; DC exact gate: advance and normalization preserve the candidate. -/
private theorem wc_gate_output
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot} {P : Block}
    (ht : IsGateTick p c rho i x s) (hraw : (fgsaAC E rho).raw i s x = some P)
    (hguard : ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) P)
    (hF : Block.Preceq ((fgsaAC E rho).anchor i x) P) :
    Block.Preceq P (S_at p c E rho (i + 1) x) := by
  have hf : (fgsaAC E rho).saved i x s = none := fgsa_gate_fresh E rho hs ht
  rcases (fgsaAC_gate_write E rho i s x ht).effects with hskip | hrun
  · obtain ⟨⟨result, hr⟩, _⟩ := hskip
    rw [hf] at hr
    cases hr
  · have hP : Block.Preceq P (GridCO.advance ((fgsaAC E rho).output i x) P) := by
      unfold GridCO.advance
      split
      · assumption
      · exact block_preceq_refl _
    change Block.Preceq P ((fgsaAC E rho).output (i + 1) x)
    rw [(hrun.accept P hraw hguard).1, Gen.AC.normalizeOutput_def]
    have hb : Block.preceq ((fgsaAC E rho).anchor i x)
        (GridCO.advance ((fgsaAC E rho).output i x) P) = true :=
      block_preceq_trans hF hP
    rw [hb, ite_eq_left rfl]
    exact hP

/-- WC J3, plan §6.11; DC gate event induction: earlier same-time results are exact.
Only the reviewed frame conclusion is supplied to this local construction. -/
theorem wc_proposal_gates [Fintype V]
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (pt : PtSP) (hstart : w.u + 2 ≤ pt.s)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y pt.s = some pt.P)
    (had : ∀ y ∈ rho.honest, WCProposalAdmittedBeforeVote p c E rho y pt)
    (hQP : Block.Preceq w.QStar pt.P)
    (hprior : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r < pt.s → Block.Preceq B pt.P)
    (hfl : ∀ i x phase st WStar (Bfg : FGBlock (Fin p.n)),
      WCDutyInput p c E rho i x phase st → x ∈ rho.honest → iStar ≤ i →
      WStar ∈ st.fg.TF → eraseFG WStar = w.CStar → (heightView p WStar).h = w.M + 1 →
      Block.Preceq w.QStar (eraseFG Bfg) →
      WCUsableHighSourcesBelow p c E rho w i x st (eraseFG Bfg) →
      (∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
        Block.Preceq row.1 (eraseFG Bfg)) →
      ∀ view, WCDutyView p st phase view → view ⊆ st.fg.TF →
        WCFrameLiveBelow p st phase Bfg view)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams pt.s) (SA.gateTime p.toParams pt.s))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams pt.s)).card) :
    ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x pt.s →
      gateResultAt p c E rho i = some (some pt.P) ∧
        Block.Preceq pt.P (S_at p c E rho (i + 1) x) := by
  have hs := hvalid.toScheduleWellFormed
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro x hx ht
    have hiN := (List.getElem?_eq_some_iff.mp ht).1
    have hcut := wc_gate_after_cut hs hseed ht (by simp only [Slot] at hstart ⊢; omega)
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams pt.s)
    have hhistory : ∀ j y r B, WCResult p c E rho w iStar i j y r B →
        Block.Preceq B pt.P := by
      intro j y r B hB
      have hBN : WCResult p c E rho w iStar rho.events.length j y r B :=
        { hB with completed := hB.completed.trans hiN }
      have htime : SA.gateTime p.toParams r ≤ SA.gateTime p.toParams pt.s := by
        by_contra hn
        have hj := V2.D.Engine.eventIndex_lt_of_time_lt hs ht hB.event (lt_of_not_ge hn)
        exact (Nat.not_lt_of_ge hB.completed.le hj).elim
      have hle : r ≤ pt.s := by
        change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
          4 * p.Δ * (pt.s : Time) + 6 * p.Δ at htime
        have hc : (r : Time) ≤ pt.s := by nlinarith [p.deltaPos]
        exact_mod_cast hc
      rcases lt_or_eq_of_le hle with hr | rfl
      · exact hprior j y r B hBN hr
      · have heq := (ih j hB.completed y hB.honest hB.event).1
        have hBP := Option.some.inj (Option.some.inj (hB.value.symm.trans heq))
        exact hBP ▸ block_preceq_refl B
    have hhigh : WCUsableHighSourcesBelow p c E rho w i x pre pt.P := by
      refine ⟨hx, ?_⟩
      intro a _ j y r wire e K hji hrow _ hentry hheight hsource
      by_cases hjcut : j < iStar
      · obtain ⟨C, hC, _, hCQ⟩ := hi.preCutHigh j y r wire e hjcut hrow hentry hheight
        have he := Option.some.inj (Option.some.inj (hC.symm.trans hsource))
        exact block_preceq_trans (he ▸ hCQ) hQP
      · obtain ⟨B, hB, hKB⟩ := hi.suffixSources j y r K (Nat.le_of_not_lt hjcut)
          (hji.trans hiN) hrow.1 hrow.2.1 hsource
        exact block_preceq_trans hKB (hhistory j y (r * p.R) B
          { hB with completed := hji })
    have htargets : ∀ row ∈ pre.base.obligations, pre.base.now < row.2.2 →
        Block.Preceq row.1 pt.P := by
      intro row hrow hlive
      have hm := (clockPre_obligations_sublist p _ _).subset hrow
      have hnow : (storeAt p c E rho i x).base.now < row.2.2 := by
        have hpos : 0 < SA.gateTime p.toParams pt.s := by
          change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
          nlinarith [p.deltaPos, Nat.cast_nonneg (α := Int) pt.s]
        have hbefore := fgsa_preTick_now_lt E rho hs ht hpos
        rw [show pre.base.now = SA.gateTime p.toParams pt.s from
          (Internal.clockPre_vn _ _).2] at hlive
        exact hbefore.trans hlive
      rcases (hi.liveTargets i x row hcut hiN.le hx hm hnow).origin with hQ |
        ⟨j, y, r, B, hB, hRB⟩
      · exact block_preceq_trans hQ hQP
      · exact block_preceq_trans hRB (hhistory j y r B hB)
    obtain ⟨Bfg, _, hBP⟩ := wc_admitted_at_gate hs hnr hdelta pt hgate hx ht (had x hx)
    obtain ⟨WStar, hW, hheight, hcarrier⟩ := hi.carrier
    have hduty : WCDutyInput p c E rho i x (.gate pt.s) pre :=
      ⟨hiN, ⟨_, ht, Or.inr (Or.inr (Or.inl ⟨pt.s, rfl, rfl, rfl⟩))⟩⟩
    have hf := hfl i x (.gate pt.s) pre WStar Bfg hduty hx hcut
      (by rw [clockPre_fg]; exact hcarrier i x hcut hiN.le hx) hW hheight
      (hBP ▸ hQP) (hBP ▸ hhigh) (hBP ▸ htargets) pre.fg.TF
      ⟨Or.inr ⟨⟨pt.s, Or.inr (Or.inl rfl)⟩, rfl⟩⟩ (fun _ h => h)
    have hF : Block.Preceq (eraseFG pre.fg.F) pt.P := by
      rw [← hBP]
      exact block_preceq_trans hf.frame.finalRoot hf.frame.rootBelow
    have hgeom : GateReceiptGeometry E rho pre pt.s pt.P := by
      constructor
      · intro q hy _ K he
        rw [exactService_emitted_head E rho hs pt.s pt.P hhead q hy K _ he]
        exact hF
      · intro q hy _ K he
        rw [exactService_emitted_head E rho hs pt.s pt.P hhead q hy K _ he]
        exact block_preceq_refl _
    obtain ⟨H, hH, hbatch⟩ := inclusion_head_seats E rho hcstar pt.s ⟨hpart⟩
    obtain ⟨hr, _, _, _⟩ := exactService_gate_raw_of_head E rho hvalid hnr hdelta hcstar
      pt.s pt.P hhead hSync ht hgeom H hH hbatch hroots
    have hv : { actView pre with early := (storeAt p c E rho i x).base.early } =
        (fgsaAC E rho).gateView i x pt.s :=
      fgsa_clockPre_gateView p (storeAt p c E rho i x) pt.s
    have hrawEq : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F)
        (actView pre) pt.s = (fgsaAC E rho).raw i pt.s x := by
      dsimp only [pre]
      rw [clockPre_fg]
      have heq := congrArg (fun v => SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho i x).fg.F) v pt.s) hv
      exact heq
    have hraw := hrawEq.symm.trans hr
    have hguard : ∀ lease ∈ ((fgsaAC E rho).gateView i x pt.s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) pt.P := by
      intro lease hl
      have hobl := congrArg GridCO.State.obligations hv
      rw [← hobl] at hl
      have hrow : lease ∈ pre.base.obligations := hl
      have hlive : pre.base.now < lease.2.2 := by
        rw [show pre.base.now = SA.gateTime p.toParams pt.s from
          (Internal.clockPre_vn _ _).2]
        exact wc_clockPre_live _ _ lease hrow
      exact Bool.or_eq_true_iff.mpr (Or.inl (htargets lease hrow hlive))
    have hanchor : Block.Preceq ((fgsaAC E rho).anchor i x) pt.P := by
      change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) pt.P
      simpa only [pre, clockPre_fg] using hF
    refine ⟨?_, wc_gate_output hs ht hraw hguard hanchor⟩
    rw [gateResultAt_eq_gateResult p c E rho hs ht, gateResult_def, gateIn_def,
      preTick_def, fgsa_tickIdx_of_event p c E rho hs ht]
    exact congrArg some hr

/-- WC J3, plan §6.11; DC persistence: compose the finite suffix transitions. -/
theorem wc_suffix_mono (hi : WCInv p c E rho w iStar rho.events.length)
    {i j : Nat} {x : V} (hcut : iStar ≤ i) (hij : i ≤ j)
    (hjN : j ≤ rho.events.length) (hx : x ∈ rho.honest) :
    Block.Preceq (S_at p c E rho i x) (S_at p c E rho j x) := by
  induction j, hij using Nat.le_induction with
  | base => exact block_preceq_refl _
  | succ j hij ih =>
    exact block_preceq_trans (ih (Nat.le_succ j |>.trans hjN))
      (hi.transitions j x (hcut.trans hij) (Nat.lt_of_succ_le hjN) hx)

/-- WC J3, plan §6.11; DC six-Delta inclusion: serve both getters at every later read.
The sole producer premise is the reviewed live-frame Statement. -/
theorem wc_inclusion6 [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframeLive : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCInclusion6Statement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have hs := hvalid.toScheduleWellFormed
  have hi := hinv rho.events.length ⟨hseed.within, le_rfl⟩
  obtain ⟨D, hpivot⟩ := wc_proposalPivot ΔF w iStar hframeLive
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have had := wc_proposalAdmission ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot
  have hhead := wc_exactProposal ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot had
  obtain ⟨hQP, hprior⟩ := wc_prior_below_proposal hs hi pt D hpivot hhead _ hprop.1.2
  have hfl := hframeLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault
    hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc
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
  have hcut := wc_gate_after_cut hs hseed he (by simp only [Slot] at hstart ⊢; omega)
  have hread : i + 1 ≤ timeIdx rho t :=
    (V2.D.Engine.index_lt_read_length_iff hs t he).mpr ht.1
  have hout := (hgates i x hx he).2
  have hm := wc_suffix_mono hi (hcut.trans (Nat.le_succ i)) hread
    (List.length_filter_le _ _) hx
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [fgsa_outputAt_eq_S_at E rho hs g hg x t]
  exact block_preceq_trans hout hm

end AvailableChain.FGSA.Run
end
