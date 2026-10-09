module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationGate
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationInduction
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingCover
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingMain

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

section History

variable [Fintype V]
variable (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho) (hdelta : E.Δ = p.Δ)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hstrat : RStrat p c E rho) (htsrc : TSrc p c E rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include hvalid hnr hcstar hdelta hstore hframe hstrat htsrc hroots hnamed in
/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; event induction carries original
source history to the regression relay cut. All new gates use labels below s.
Old labels use the pre-expiry history. Restored labels use earlier HEADs.
Neither carrier receipt nor future F compatibility is an input. -/
theorem outageV_history_through_relay
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (B : FGBlock (Fin p.n)) (j r s : Slot) (hr : r ≤ j + p.k)
    (hGST : ∀ q, r ≤ q → q < s → E.t_GST ≤ SA.voteTime p.toParams q)
    (hpart : ∀ q, r ≤ q → q < s → (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams q)).card)
    (hheads : ∀ q, r ≤ q → q < s → ∀ k y,
      rho.events[k]? = some (.tick y (SA.voteTime p.toParams q)) →
      Block.Compatible
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams q)) q) (eraseFG B))
    (hold : OutageSourceHistory p c E rho (eraseFG B)
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p)))
    {I : Nat} (hseed : OutageSourceHistory p c E rho (eraseFG B) I)
    {i : Nat} (hI : I ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)) :
    OutageSourceHistory p c E rho (eraseFG B) i ∧
      ∀ x ∈ rho.honest, Block.Compatible (eraseFG B) (F_at p c E rho i x) := by
  have hs := hvalid.toScheduleWellFormed
  have hhist : OutageSourceHistory p c E rho (eraseFG B) i := by
    induction i, hI using Nat.le_induction with
    | base => exact hseed
    | succ i hI ih =>
      have hic : i < V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) := by omega
      have hist := ih hic.le
      constructor
      intro k x a C hk hx htick hC
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | hki
      · exact hist.history k x a C hki hx htick hC
      · subst k
        have hat : p.actionTime a < SA.voteTime p.toParams s + p.Δ :=
          (Gen.V2.Duty.index_lt_idxBefore_iff hs htick _).mp hic
        have hgate : IsGateTick p c rho i x (a * p.R) := by
          change rho.events[i]? = some (.tick x (SA.gateTime p.toParams (a * p.R)))
          rwa [← fgsa_action_gate_time]
        have has : a * p.R < s := outageV_gate_through_relay p s (a * p.R)
          (by rw [← fgsa_action_gate_time]; exact hat.le)
        by_cases har : a * p.R < r
        · have haold := outageV_old_gate_before_expiry p j r (a * p.R) hr har
          rw [← fgsa_action_gate_time] at haold
          exact hold.history i x a C
            ((Gen.V2.Duty.index_lt_idxBefore_iff hs htick _).mpr haold) hx htick hC
        · have hra : r ≤ a * p.R := Nat.le_of_not_gt har
          have hnames := outage_named_of_source_history (hroots := hroots) rfl hist hnamed
          have hf := (cpCompat_of_scopedFrame p c E rho hstore hframe hstrat
            i x B hx hnames.history).2.1
          have hfB : Block.Compatible (F_at p c E rho i x) (eraseFG B) :=
            Bool.or_eq_true_iff.mpr (hf.imp eraseFG_preceq eraseFG_preceq)
          apply outageV_source_compatible htsrc hx hC
          intro G hG
          have hgread := arming_gateResult_tick hs hgate
          rw [hG] at hgread
          have hg := Option.some.inj hgread.symm
          exact outageV_restored_gate hvalid hnr hdelta hcstar hroots hsync hgate
            (hGST _ hra has) (hpart _ hra has) (hheads _ hra has) hfB hg
  refine ⟨hhist, ?_⟩
  intro x hx
  have hnames := outage_named_of_source_history (hroots := hroots) rfl hhist hnamed
  have hf := (cpCompat_of_scopedFrame p c E rho hstore hframe hstrat
    i x B hx hnames.history).2.1
  exact Bool.or_eq_true_iff.mpr (Or.symm (hf.imp eraseFG_preceq eraseFG_preceq))

include hvalid hnr hcstar hdelta hstore hframe hstrat htsrc hroots hnamed in
/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; a contested regression supplies
one exact carrier to every honest receiver by the causal relay cut.
The F exclusion fact is derived from earlier-label gates and source history. -/
theorem outageV_contest_relay
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (B : FGBlock (Fin p.n)) (j r s : Slot) (hr : r ≤ j + p.k)
    (hGST : ∀ q, r ≤ q → q < s → E.t_GST ≤ SA.voteTime p.toParams q)
    (hpart : ∀ q, r ≤ q → q < s → (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams q)).card)
    (hheads : ∀ q, r ≤ q → q < s → ∀ k y,
      rho.events[k]? = some (.tick y (SA.voteTime p.toParams q)) →
      Block.Compatible
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams q)) q) (eraseFG B))
    (hold : OutageSourceHistory p c E rho (eraseFG B)
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p)))
    {I : Nat} (hseed : OutageSourceHistory p c E rho (eraseFG B) I)
    {k : Nat} {y : V} (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hIk : I ≤ k) (hGSTs : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (hcontest : (controls p (clock p (storeAt p c E rho k y)
      (SA.voteTime p.toParams s))).contest = true) :
    ∃ P : FGBlock (Fin p.n), FGBlock.Preceq B (heightView p P).J ∧
      (heightView p P).h_j ≠ 0 ∧ ∀ x ∈ rho.honest,
      let dst := (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s + p.Δ) x).st
      Block.Preceq (eraseFG B) (eraseFG dst.fg.F) ∨
        P ∈ dst.fg.TF ∧ (heightView p P).h_j ≤ dst.fg.h_j := by
  have hs := hvalid.toScheduleWellFormed
  have hy := hs.honest_only _ (List.mem_of_getElem? hk)
  have hkD : k < V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr (lt_add_of_pos_right _ p.deltaPos)
  have hh := fun i => outageV_history_through_relay (i := i)
    hvalid hnr hcstar hdelta hstore hframe hstrat
    htsrc hroots hnamed hsync B j r s hr hGST hpart hheads hold hseed
  have hist := (hh k hIk hkD.le).1
  have hnames := outage_named_of_source_history (hroots := hroots) rfl hist hnamed
  change (KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg).contest = true at hcontest
  rw [clock_fg] at hcontest
  have hc := (cpCompat_of_scopedFrame p c E rho hstore hframe hstrat
    k y B hy hnames.history).2.2.2.2 hcontest
  obtain ⟨hnz, P, hP, hj, hJ, _⟩ := outageV_contest_carrier p (storeAt p c E rho k y)
    (hstore k y hy).1 hcontest
  have hBJ : FGBlock.Preceq B (heightView p P).J := hJ.symm ▸ hc.1
  have hBP : FGBlock.Preceq B P := preceq_trans hBJ
    (preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry P)
      ((fgCertificateLaws p).height.entry_preceq P))
  refine ⟨P, hBJ, hj.symm ▸ hnz, ?_⟩
  intro x hx
  exact outageV_regression_receipt hvalid hnr hdelta hsync hroots hk hx hy hP hBP hBJ
    hGSTs hhor ((hh _ (hIk.trans hkD.le) le_rfl).2 x hx)

include hvalid hnr hcstar hdelta hstore hframe hstrat htsrc hroots hnamed in
/-- OUTPUT-DIRECT §§8–10. DC: INTENTIONAL; after the expiry cut, earlier
compatible HEAD labels suffice for a joint source and output event induction.
Current gate results control writes. Old saved results need no premise.
Deliveries use successor F from the original source history. -/
theorem outageV_events_through_relay
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (B : FGBlock (Fin p.n)) (j r s : Slot) (hr : r ≤ j + p.k)
    (hGST : ∀ q, r ≤ q → q < s → E.t_GST ≤ SA.voteTime p.toParams q)
    (hpart : ∀ q, r ≤ q → q < s → (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams q)).card)
    (hheads : ∀ q, r ≤ q → q < s → ∀ k y,
      rho.events[k]? = some (.tick y (SA.voteTime p.toParams q)) →
      Block.Compatible
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams q)) q) (eraseFG B))
    (hseed : OutageSourceHistory p c E rho (eraseFG B)
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p)))
    (hSseed : ∀ x ∈ rho.honest, Block.Preceq (eraseFG B)
      (S_at p c E rho (V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p)) x))
    {i : Nat} (hI : V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p) ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)) :
    OutageSourceHistory p c E rho (eraseFG B) i ∧
      ∀ x ∈ rho.honest, Block.Preceq (eraseFG B) (S_at p c E rho i x) ∧
        Block.Compatible (eraseFG B) (F_at p c E rho i x) := by
  have hs := hvalid.toScheduleWellFormed
  have hist := fun i => outageV_history_through_relay (i := i)
    hvalid hnr hcstar hdelta hstore hframe hstrat htsrc hroots hnamed hsync B j r s hr
    hGST hpart hheads hseed hseed
  have hS : ∀ x ∈ rho.honest, Block.Preceq (eraseFG B) (S_at p c E rho i x) := by
    induction i, hI using Nat.le_induction with
    | base => exact hSseed
    | succ i hI ih =>
      have hic : i < V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) := by omega
      have hSi := ih hic.le
      intro x hx
      rcases fgsaAC_output_step E rho i x with he | ⟨q, hgate⟩ |
          ⟨o, t, b, _, _, _, hn⟩ | ⟨t, hre, _⟩
      · change S_at p c E rho (i + 1) x = S_at p c E rho i x at he
        rw [he]
        exact hSi x hx
      · have ht : SA.gateTime p.toParams q < SA.voteTime p.toParams s + p.Δ :=
          (Gen.V2.Duty.index_lt_idxBefore_iff hs hgate _).mp hic
        have hqs := outageV_gate_through_relay p s q ht.le
        have hrq : r ≤ q := by
          by_contra hn
          have hqold := outageV_old_gate_before_expiry p j r q hr (Nat.lt_of_not_ge hn)
          have hidx := (Gen.V2.Duty.index_lt_idxBefore_iff hs hgate _).mpr hqold
          omega
        have hf : Block.Compatible (F_at p c E rho i x) (eraseFG B) := by
          change Block.compatible _ _ = true
          rw [block_compatible_comm]
          exact (hist i hI hic.le).2 x hx
        have hpost : storeAt p c E rho (i + 1) x =
            clock p (storeAt p c E rho i x) (SA.gateTime p.toParams q) := by
          change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
          rw [(V2.D.Run.step_tick_eq E rho hgate).1]
          exact tick_st (c := c) E rho _ x _
        change Block.Preceq _ (storeAt p c E rho (i + 1) x).base.stableRecord
        rw [hpost, arming_clock_gate]
        apply outageV_gateStep_covers p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _) q (eraseFG B)
        · rw [clockPre_stable]
          exact hSi x hx
        · rw [clockPre_fg]
          exact hf
        · intro C hC
          exact outageV_restored_gate hvalid hnr hdelta hcstar hroots hsync hgate
            (hGST q hrq hqs) (hpart q hrq hqs) (hheads q hrq hqs) hf hC
      · change S_at p c E rho (i + 1) x =
          Gen.AC.normalizeOutput (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hn
        rw [hn]
        apply outage_normalize_covers (hSi x hx)
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        exact (hist (i + 1) (Nat.le_succ_of_le hI) hi).2 x hx
      · exact (hnr i x t hre).elim
  exact ⟨(hist i hI hi).1, fun x hx => ⟨hS x hx, (hist i hI hi).2 x hx⟩⟩

end History

/-- OUTPUT-DIRECT §§5,6. DC: INTENTIONAL; the exact received marker stays
in the cumulative store and protects each later clocked HEAD. If F already
covers B, monotonic F supplies protection without a marker-height read. -/
theorem outageV_received_marker_head
    (hnr : V2.D.NoRestart rho) (hcumul : RStoreCumul p c E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hstrat : RStrat p c E rho)
    {j i : Nat} {x : V} {B P : FGBlock (Fin p.n)} (s : Slot)
    (hx : x ∈ rho.honest) (hji : j ≤ i) (hi : i ≤ rho.events.length)
    (hreceipt : Block.Preceq (eraseFG B) (F_at p c E rho j x) ∨
      P ∈ (storeAt p c E rho j x).fg.TF)
    (hBJ : FGBlock.Preceq B (heightView p P).J) (hnz : (heightView p P).h_j ≠ 0)
    (hnames : OutageNamedHistory p c E rho B i)
    (hlocks : ∀ row ∈ (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.obligations,
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.now < row.2.2 →
      Block.Compatible row.1 (eraseFG B)) :
    Block.Compatible (headVote p
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) (SA.voteTime p.toParams s)
  by_cases hs : s = 0
  · rw [hs, headVote_zero]
    exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
  have hc := cpCompat_of_scopedFrame p c E rho hstore hframe hstrat i x B hx hnames.history
  have hctrl : controls p dst = controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  have hfg : dst.fg = (storeAt p c E rho i x).fg := clock_fg p _ _
  by_cases hBF : Block.Preceq (eraseFG B) (F_at p c E rho i x)
  · have hBroot : Block.Preceq (eraseFG B) (liveRoot p dst) := by
      apply block_preceq_trans (B := eraseFG dst.fg.F) ?_ (F_preceq_liveRoot p dst hinv)
      rw [hfg]
      exact hBF
    have hh : Block.Preceq (eraseFG B) (headVote p dst s) := by
      change Block.Preceq _ (if s = 0 then .genesis else headInTree p dst _ _ _)
      rw [ite_eq_right hs]
      exact block_preceq_trans hBroot (liveRoot_preceq_headInTree p dst _ _ _)
    exact Bool.or_eq_true_iff.mpr (Or.inr hh)
  have hFB : FGBlock.Preceq dst.fg.F B := by
    rw [hfg]
    rcases hc.2.1 with h | h
    · exact h
    · exact (hBF (eraseFG_preceq h)).elim
  have hP : P ∈ dst.fg.TF := by
    rw [hfg]
    rcases hreceipt with h | h
    · exact (hBF (block_preceq_trans h (arming_F_mono (E := E) hnr hji x))).elim
    · exact (hcumul hnr j i x hx hji hi).1 h
  have hmark := outageV_received_height p dst hinv hP (preceq_trans hFB hBJ)
  have hZ : Block.Compatible (eraseFG (controls p dst).Z) (eraseFG B) := by
    rw [hctrl]
    have hz : FGBlock.Preceq (controls p (storeAt p c E rho i x)).Z B ∨
        FGBlock.Preceq B (controls p (storeAt p c E rho i x)).Z := by
      change FGBlock.Preceq (if (controls p _).rootIsJ then _ else _) B ∨
        FGBlock.Preceq B (if (controls p _).rootIsJ then _ else _)
      cases he : (controls p (storeAt p c E rho i x)).rootIsJ
      · exact hc.2.1
      · exact hc.2.2.1
    exact Bool.or_eq_true_iff.mpr (hz.imp eraseFG_preceq eraseFG_preceq)
  apply outageV_marker_head p dst hinv s
    (outageV_liveRoot_compatible p dst (eraseFG B) hZ hlocks) hBJ
    ((fgJustificationLaws p).J_entry P)
    (by rw [(fgJustificationLaws p).J_height P hnz]; exact hmark)
  · rw [hfg]
    exact hc.2.2.1
  · intro ht W hW hh
    rw [hctrl] at ht hh
    rw [hfg] at hW
    have htop := hc.2.2.2.2 ht
    exact outageV_contest_top p _ B htop.1 htop.2 W hW hh
  · intro W hW U hUW hh
    rw [hfg] at hW
    apply hc.1 W hW
    rw [certified_def]
    exact ⟨U, hUW, Or.inr (Or.inr ⟨rfl, hh⟩)⟩

/-- OUTPUT-DIRECT §§2–4. DC: INTENTIONAL; the event output and original
names supply live-root compatibility at the actual clocked HEAD read. -/
theorem outageV_clocked_root_compatible
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hstrat : RStrat p c E rho) {i : Nat} {x : V} {s : Slot}
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hx : x ∈ rho.honest) (B : FGBlock (Fin p.n))
    (hnames : OutageNamedHistory p c E rho B i)
    (hS : Block.Preceq (eraseFG B) (S_at p c E rho (i + 1) x)) :
    let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
    Block.Compatible (liveRoot p dst) (eraseFG B) ∧
      ∀ row ∈ dst.base.obligations, dst.base.now < row.2.2 →
        Block.Compatible row.1 (eraseFG B) := by
  intro dst
  have hpost : storeAt p c E rho (i + 1) x = dst := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [(V2.D.Run.step_tick_eq E rho ht).1]
    exact tick_st (c := c) E rho _ x _
  have hlocks := outageV_live_locks p (storeAt p c E rho (i + 1) x) (eraseFG B) hS
    (leaseBelowOutput_stateBefore E rho (i + 1) x)
  rw [hpost] at hlocks
  refine ⟨?_, hlocks⟩
  apply outageV_liveRoot_compatible p dst (eraseFG B) ?_ hlocks
  have hc := cpCompat_of_scopedFrame p c E rho hstore hframe hstrat i x B hx hnames.history
  have hctrl : controls p dst = controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  rw [hctrl]
  have hz : FGBlock.Preceq (controls p (storeAt p c E rho i x)).Z B ∨
      FGBlock.Preceq B (controls p (storeAt p c E rho i x)).Z := by
    change FGBlock.Preceq (if (controls p _).rootIsJ then _ else _) B ∨
      FGBlock.Preceq B (if (controls p _).rootIsJ then _ else _)
    cases he : (controls p (storeAt p c E rho i x)).rootIsJ
    · exact hc.2.1
    · exact hc.2.2.1
  exact Bool.or_eq_true_iff.mpr (hz.imp eraseFG_preceq eraseFG_preceq)

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; source names and post-tick S
protect a contested scheduled HEAD without a receipt or score premise. -/
theorem outageV_clocked_contested_head
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hstrat : RStrat p c E rho) {i : Nat} {x : V} {s : Slot}
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hx : x ∈ rho.honest) (B : FGBlock (Fin p.n))
    (hnames : OutageNamedHistory p c E rho B i)
    (hS : Block.Preceq (eraseFG B) (S_at p c E rho (i + 1) x))
    (hcontest : (controls p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s))).contest = true) :
    Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  have hctrl : controls p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) =
      controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  have hct : (R_at p c E rho i x).contest = true := by
    change (controls p (storeAt p c E rho i x)).contest = true
    rw [← hctrl]
    exact hcontest
  have hc := (cpCompat_of_scopedFrame p c E rho hstore hframe hstrat
    i x B hx hnames.history).2.2.2.2 hct
  apply outageV_contested_head p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) _)
    B s (outageV_clocked_root_compatible hstore hframe hstrat ht hx B hnames hS).1 ?_ hcontest
  intro W hW hh
  rw [clock_fg] at hW
  change (heightView p W).h = (controls p (clock p (storeAt p c E rho i x)
    (SA.voteTime p.toParams s))).H at hh
  rw [hctrl] at hh
  exact outageV_contest_top p _ B hc.1 hc.2 W hW hh

section Labels
variable [Fintype V]
variable (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho) (hdelta : E.Δ = p.Δ)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hstrat : RStrat p c E rho) (htsrc : TSrc p c E rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include hvalid hnr hcstar hdelta hstore hframe hstrat htsrc hroots hnamed in
/-- OUTPUT-DIRECT §10. DC: INTENTIONAL; strong label induction closes the
restored HEAD compatibility field. Before the first regression HEADs cover B.
At that regression the frame is contested. Its exact marker protects all later
reads, while earlier labels supply the causal source and S event induction. -/
theorem outageV_restored_heads
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreCumul p c E rho) (origin : RQCOrigin p c E rho)
    (B : FGBlock (Fin p.n)) (j r : Slot) (hr : r ≤ j + p.k)
    (hGST : ∀ q, r ≤ q → E.t_GST ≤ SA.voteTime p.toParams q)
    (hpart : ∀ q, r ≤ q → SA.voteTime p.toParams q ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams q)).card)
    (hseed : OutageSourceHistory p c E rho (eraseFG B)
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p)))
    (hSseed : ∀ x ∈ rho.honest, Block.Preceq (eraseFG B)
      (S_at p c E rho (V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p)) x))
    (hbefore : ∀ q, r ≤ q → SA.voteTime p.toParams q < SA.gateTime p.toParams j + L p →
      ∀ i x, rho.events[i]? = some (.tick x (SA.voteTime p.toParams q)) →
      Block.Preceq (eraseFG B)
        (headVote p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams q)) q)) :
    ∀ q, r ≤ q → ∀ i x, rho.events[i]? = some (.tick x (SA.voteTime p.toParams q)) →
      Block.Compatible
        (headVote p (clock p (storeAt p c E rho i x)
          (SA.voteTime p.toParams q)) q) (eraseFG B) := by
  classical
  have hs := hvalid.toScheduleWellFormed
  have hvm : ∀ a b : Slot, a ≤ b → SA.voteTime p.toParams a ≤ SA.voteTime p.toParams b := by
    intro a b hab
    rw [arming_vote_eq, arming_vote_eq]
    have hab' : (a : Int) ≤ (b : Int) := by exact_mod_cast hab
    have := p.deltaPos
    nlinarith
  let Bad := fun q => r ≤ q ∧ ∃ i x,
    rho.events[i]? = some (.tick x (SA.voteTime p.toParams q)) ∧
      ¬ Block.Preceq (eraseFG B)
        (headVote p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams q)) q)
  by_cases hex : ∃ q, Bad q
  swap
  · intro q hrq i x ht
    exact Bool.or_eq_true_iff.mpr (Or.inr (by
      by_contra hn
      exact hex ⟨q, hrq, i, x, ht, hn⟩))
  let m := Nat.find hex
  obtain ⟨hrm, k, y, hk, hbad⟩ := Nat.find_spec hex
  change (r : Nat) ≤ m at hrm
  have hprev : ∀ q, r ≤ q → q < m → ∀ i x,
      rho.events[i]? = some (.tick x (SA.voteTime p.toParams q)) →
      Block.Preceq (eraseFG B)
        (headVote p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams q)) q) := by
    intro q hrq hqm i x ht
    by_contra hn
    exact Nat.find_min hex hqm ⟨hrq, i, x, ht, hn⟩
  have hcutm : SA.gateTime p.toParams j + L p ≤ SA.voteTime p.toParams m := by
    by_contra hn
    exact hbad (hbefore m hrm (lt_of_not_ge hn) k y hk)
  have hrm' : r < m := by
    have hvr := outageV_vote_before_expiry p j r hr
    by_contra hn
    have he : m = r := Nat.le_antisymm (Nat.le_of_not_gt hn) hrm
    rw [he] at hcutm
    exact (not_le.mpr hvr) hcutm
  change (r : Nat) < m at hrm'
  have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le r) hrm')
  have hstate (q : Slot) (hrq : r ≤ q)
      (hcut : SA.gateTime p.toParams j + L p ≤ SA.voteTime p.toParams q)
      (hprior : ∀ a, r ≤ a → a < q → ∀ i x,
        rho.events[i]? = some (.tick x (SA.voteTime p.toParams a)) →
        Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
          (SA.voteTime p.toParams a)) a) (eraseFG B))
      {i : Nat} {x : V} (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams q))) :
      OutageNamedHistory p c E rho B i ∧
        Block.Preceq (eraseFG B) (S_at p c E rho (i + 1) x) := by
    have hx := hs.honest_only _ (List.mem_of_getElem? ht)
    have hhor := (hs.in_horizon _ (List.mem_of_getElem? ht)).2
    have hI : V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p) ≤ i := by
      by_contra hn
      exact (not_lt.mpr hcut) ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp
        (Nat.lt_of_not_ge hn))
    have hiD : i + 1 ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams q + p.Δ) :=
      Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mpr
        (lt_add_of_pos_right _ p.deltaPos))
    have hh := outageV_events_through_relay hvalid hnr hcstar hdelta hstore hframe hstrat
      htsrc hroots hnamed hsync B j r q hr (fun a ha _ => hGST a ha)
      (fun a ha haq => hpart a ha ((hvm a q haq.le).trans hhor)) hprior hseed hSseed
      (Nat.le_succ_of_le hI) hiD
    have hsource : OutageSourceHistory p c E rho (eraseFG B) i :=
      ⟨fun a z b C ha hz ht hC => hh.1.history a z b C (Nat.lt_succ_of_lt ha) hz ht hC⟩
    exact ⟨outage_named_of_source_history (hroots := hroots) rfl hsource hnamed, (hh.2 x hx).1⟩
  have hprevComp : ∀ q, r ≤ q → q < m → ∀ i x,
      rho.events[i]? = some (.tick x (SA.voteTime p.toParams q)) →
      Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
        (SA.voteTime p.toParams q)) q) (eraseFG B) := fun q hq hqm i x ht =>
    Bool.or_eq_true_iff.mpr (Or.inr (hprev q hq hqm i x ht))
  obtain ⟨hnamesM, hSM⟩ := hstate m hrm hcutm hprevComp hk
  have hy := hs.honest_only _ (List.mem_of_getElem? hk)
  have hrootM := (outageV_clocked_root_compatible hstore hframe hstrat hk hy B hnamesM hSM).1
  have hcontestM : (controls p (clock p (storeAt p c E rho k y)
      (SA.voteTime p.toParams m))).contest = true := by
    by_contra hn
    have hnt := Bool.eq_false_iff.mpr hn
    have hhistM : OutageSourceHistory p c E rho (eraseFG B) k := by
      have hIk : V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p) ≤ k := by
        by_contra hn
        exact (not_lt.mpr hcutm) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mp
          (Nat.lt_of_not_ge hn))
      exact (outageV_history_through_relay hvalid hnr hcstar hdelta hstore hframe hstrat
        htsrc hroots hnamed hsync B j r m hr (fun a ha _ => hGST a ha)
        (fun a ha ham => hpart a ha ((hvm a m ham.le).trans
          (hs.in_horizon _ (List.mem_of_getElem? hk)).2)) hprevComp hseed hseed hIk
        (Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr
          (lt_add_of_pos_right _ p.deltaPos)))).1
    apply hbad
    have hmPrev : r ≤ m - 1 := Nat.le_sub_one_of_lt hrm'
    have hvPrev := (hvm (m - 1) m (Nat.sub_le m 1)).trans
      (hs.in_horizon _ (List.mem_of_getElem? hk)).2
    have hh := outageV_uncontested_head hvalid hnr hdelta hcstar hcumul hroots origin hsync B
      (s := m - 1) (by simpa only [hmEq] using hk) (hGST _ hmPrev)
      (hpart _ hmPrev hvPrev) hhistM
      (fun a z _ hz => hprev _ hmPrev (by change (_ : Nat) < _; omega) a z hz)
      (by simpa only [hmEq] using hrootM) (by simpa only [hmEq] using hnt)
    simpa only [hmEq] using hh
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hrq i x ht
    have hx := hs.honest_only _ (List.mem_of_getElem? ht)
    have hhor := (hs.in_horizon _ (List.mem_of_getElem? ht)).2
    by_cases hqm : q < m
    · exact Bool.or_eq_true_iff.mpr (Or.inr (hprev q hrq hqm i x ht))
    have hmq : m ≤ q := Nat.le_of_not_gt hqm
    have hcut := hcutm.trans (hvm m q hmq)
    obtain ⟨hnames, hS⟩ := hstate q hrq hcut (fun a ha haq => ih a haq ha) ht
    obtain ⟨hroot, hlocks⟩ := outageV_clocked_root_compatible hstore hframe hstrat ht hx B hnames hS
    by_cases he : q = m
    · subst q
      by_cases hc : (controls p (clock p (storeAt p c E rho i x)
          (SA.voteTime p.toParams m))).contest = true
      · exact outageV_clocked_contested_head hstore hframe hstrat ht hx B hnames hS hc
      · have hmPrev : r ≤ m - 1 := Nat.le_sub_one_of_lt hrm'
        have hIk : V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p) ≤ i := by
          by_contra hn
          exact (not_lt.mpr hcutm) ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp
            (Nat.lt_of_not_ge hn))
        have hh := outageV_history_through_relay hvalid hnr hcstar hdelta hstore hframe hstrat
          htsrc hroots hnamed hsync B j r m hr (fun a ha _ => hGST a ha)
          (fun a ha ham => hpart a ha ((hvm a m ham.le).trans hhor)) hprevComp hseed hseed hIk
          (Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mpr
            (lt_add_of_pos_right _ p.deltaPos)))
        have hcover := outageV_uncontested_head hvalid hnr hdelta hcstar hcumul hroots origin
          hsync B (s := m - 1) (by simpa only [hmEq] using ht) (hGST _ hmPrev)
          (hpart _ hmPrev ((hvm _ m (Nat.sub_le m 1)).trans hhor)) hh.1
          (fun a z _ hz => hprev _ hmPrev (by change (_ : Nat) < _; omega) a z hz)
          (by simpa only [hmEq] using hroot)
          (by simpa only [hmEq] using Bool.eq_false_iff.mpr hc)
        have hcover' : Block.Preceq (eraseFG B) (headVote p
            (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams m)) m) := by
          simpa only [hmEq] using hcover
        exact Bool.or_eq_true_iff.mpr (Or.inr hcover')
    · have hmq' : m < q := by omega
      have hDq : SA.voteTime p.toParams m + p.Δ < SA.voteTime p.toParams q :=
        (outageV_regression_relay_bound p m _ _ le_rfl le_rfl).2.trans_le
          (hvm (m + 1) q hmq')
      have hIk : V2.D.Run.idxBefore rho (SA.gateTime p.toParams j + L p) ≤ k := by
        by_contra hn
        exact (not_lt.mpr hcutm) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mp
          (Nat.lt_of_not_ge hn))
      obtain ⟨P, hBJ, hnz, hreceipt⟩ := outageV_contest_relay hvalid hnr hcstar hdelta
        hstore hframe hstrat htsrc hroots hnamed hsync B j r m hr
        (fun a ha _ => hGST a ha)
        (fun a ha ham => hpart a ha ((hvm a m ham.le).trans ((hvm m q hmq).trans hhor)))
        hprevComp hseed hseed hk hIk (hGST m hrm) (hDq.le.trans hhor) hcontestM
      have hji : V2.D.Run.idxBefore rho (SA.voteTime p.toParams m + p.Δ) ≤ i := by
        by_contra hn
        exact (not_lt.mpr hDq.le) ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp
          (Nat.lt_of_not_ge hn))
      have hrec : Block.Preceq (eraseFG B)
          (F_at p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams m + p.Δ)) x) ∨
          P ∈ (storeAt p c E rho
            (V2.D.Run.idxBefore rho (SA.voteTime p.toParams m + p.Δ)) x).fg.TF := by
        have hh := hreceipt x hx
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hh
        exact hh.imp id And.left
      exact outageV_received_marker_head hnr hcumul hstore hframe hstrat q hx hji
        (Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1) hrec hBJ hnz hnames hlocks

end Labels

section Seed
variable [Fintype V]

/-- OUTPUT-DIRECT §§1,10. DC: INTENTIONAL; the first restored scheduled
HEAD covers B, including a sleeping node's deterministic read. Pending
reads use the healthy batch. Later reads use post-tick pre-expiry protection. -/
theorem outageV_first_restored_head
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho) (hdelta : E.Δ = p.Δ)
    (hfault : (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (htsrc : TSrc p c E rho)
    (hroots : NamedRootCollisionFree p c E rho) (hstrat : RStrat p c E rho)
    (hnamesFull : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C))
    {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (l + 1)) (SA.earlyTime p.toParams (l + 1)))
    (hpart : Batch (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    {r : Slot} (hstart : b₀ ≤ SA.voteTime p.toParams r)
    (hexpiry : SA.voteTime p.toParams r < SA.gateTime p.toParams (l + 1) + L p)
    {i : Nat} {x : V} (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams r))) :
    Block.Preceq B (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams r)) r) := by
  have hs := hvalid.toScheduleWellFormed
  have hx := hs.honest_only _ (List.mem_of_getElem? ht)
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? ht)).2
  by_cases hbefore : SA.voteTime p.toParams r < SA.gateTime p.toParams (l + 1)
  · have he := arming_vote_window p l r (hc.gate_le_cut.trans hstart) hbefore
    subst r
    have hDne : D ≠ .genesis := by
      intro heD
      have hBG := hc.max_read
      rw [heD] at hBG
      exact hne (block_preceq_antisymm hBG (block_genesis_preceq B))
    exact block_preceq_trans hc.max_read
      (arming_head_covers hvalid hnr hdelta hcstar hc.max_lift hDne hSync hpart
        hc.prefix_state hc.healthy_batch hx ht hroots)
  have hafter : SA.gateTime p.toParams (l + 1) < SA.voteTime p.toParams r :=
    lt_of_le_of_ne (le_of_not_gt hbefore) (arming_gate_ne_vote p (l + 1) r)
  obtain ⟨β, hβ, hall⟩ := outageV_armed_to_expiry hvalid hnr hcstar hdelta hfault
    hstore hframe hsrc htsrc hnamesFull hne hc le_rfl (hafter.le.trans hhor) hroots hstrat
  have hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i + 1 := by
    by_contra hn
    have hil : i < afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) := by omega
    have hle := arming_tick_le hs ht (hil.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
    exact (not_le.mpr hafter) hle
  have hie : i + 1 ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1) + L p) :=
    Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mpr hexpiry)
  obtain ⟨_, _, hnames, hlocal⟩ := hall (i + 1) hI hie
  have hp := hlocal x hx
  let post := storeAt p c E rho (i + 1) x
  have hpost : post = clock p (storeAt p c E rho i x) (SA.voteTime p.toParams r) := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [(V2.D.Run.step_tick_eq E rho ht).1]
    exact tick_st (c := c) E rho _ x _
  have hinv := cstoreInv_stateBefore E rho (i + 1) x
  have hroot : Block.Preceq B (liveRoot p post) := by
    have hret := (outage_frame_retains hstore hframe hsrc hx hβ hnames hp.1 hstrat).2
    apply outage_liveRoot_covers p post hinv hp.1 (leaseBelowOutput_stateBefore E rho (i + 1) x)
    rcases hret with hF | hret
    · exact Or.inl hF
    · rcases hp.2 with hF | ⟨dl, hm, hd⟩
      · exact Or.inl hF
      · refine Or.inr ⟨dl, arming_leaseOf p post hinv hm, ?_, hret⟩
        rw [hpost, (clock_vn _ _).2]
        exact hexpiry.trans_le hd
  have hr : r ≠ 0 := by
    intro he
    rw [he, arming_vote_eq, arming_gate_eq] at hafter
    have := p.deltaPos
    have : 0 ≤ (l : Int) := Nat.cast_nonneg l
    norm_num at hafter
    nlinarith
  rw [hpost] at hroot
  exact outage_head_of_root p _ hroot hr

/-- OUTPUT-DIRECT §10. DC: INTENTIONAL; arming and the event/label
inductions imply all inclusive continuation reads, including horizon deliveries.
The arming endpoint is b₀; its old outage budget is not used here. -/
theorem outageV_armed_outputs
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationPrem p c fast E rho T b₀ b₁ ΔF)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (htsrc : TSrc p c E rho)
    (hstrat : RStrat p c E rho) (hcumul : RStoreCumul p c E rho)
    (origin : RQCOrigin p c E rho)
    (hnamesFull : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C))
    {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₀ B l u s C iₛ D Dh)
    (r : Slot) (hr : ∀ q, b₁ ≤ SA.voteTime p.toParams q ↔ r ≤ q)
    (hrbound : r ≤ l + 1 + p.k) :
    ∀ y t, y ∈ rho.honest → b₀ ≤ t → t ≤ rho.horizon →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable y t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed y t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y) := by
  have hvalid := h.pre.base.valid
  have hnr := h.pre.base.noRestart
  have hdelta := h.pre.base.delta
  have hcstar := h.pre.base.cstar
  have hroots := h.pre.base.idealization
  have hs := hvalid.toScheduleWellFormed
  have hev := (arming_vote_lt_early p (l + 1)).1
  have he := hc.early_eq_gate.trans_le hc.gate_le_cut
  have hv0 : 0 ≤ SA.voteTime p.toParams (l + 1) := by
    rw [arming_vote_eq]
    have := p.deltaPos
    positivity
  have hpart := h.pre.partBefore _ hv0 (hev.trans_le he)
  have hcard : rho.honest.card = p.n - (Gen.V2.Duty.faulty rho).card := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, card_eq_n_of_linked h.pre.base.linked]
    have hn := Finset.card_le_univ rho.honest
    rw [card_eq_n_of_linked h.pre.base.linked] at hn
    omega
  have hhn : (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card ≤
      p.n - (Gen.V2.Duty.faulty rho).card := by
    rw [Gen.V2.Duty.awakeHonest_def, ← hcard]
    exact Finset.card_filter_le _ _
  have hfault := outage_fault_lt_release p hpart hhn
  have hSync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o)
    b₀ (SA.voteTime p.toParams (l + 1)) (SA.earlyTime p.toParams (l + 1))
    h.pre.healthy (fgsaDelay_nonrow E.Δ ΔF)
    (by rw [hdelta, arming_vote_add]) he h.pre.cut.2
  have hnamed : ∀ k x a (wire : RowWire p.n) e,
      HonestRowAt p c E rho k x a wire → namedEntry wire.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x a = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (a * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (a * p.R) (eraseFG C) := by
    intro k x a wire e hw he
    obtain ⟨e', C, G, he', hC, hn, hTC, hG, hCG, hf⟩ := hnamesFull k x a wire hw
    exact ⟨C, G, hC, (Option.some.inj (he.symm.trans he')).trans hn, hTC, hG, hCG, hf⟩
  intro y t hy hbt hthor
  have hlocal : Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y) := by
    by_cases htp : t < SA.gateTime p.toParams (l + 1)
    · exact ⟨hc.pending_cover y t hy (hc.gate_le_cut.trans hbt) htp hthor,
        hc.pending_compat y t hy (h.order.1.trans (h.order.2.1.trans hbt)) htp hthor⟩
    have hpt : SA.gateTime p.toParams (l + 1) ≤ t := le_of_not_gt htp
    have hgate := hpt.trans hthor
    obtain ⟨β, hβ, hall⟩ := outageV_armed_to_expiry hvalid hnr hcstar hdelta hfault
      hstore hframe hsrc htsrc hnamesFull hne hc le_rfl hgate hroots hstrat
    have hIt : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ timeIdx rho t :=
      (afterTicksIdx_mono rho hpt).trans (preIdx_le_afterTicksIdx E rho hs t).2
    by_cases hte : t < SA.gateTime p.toParams (l + 1) + L p
    · obtain ⟨_, _, hn, hl⟩ := hall _ hIt (arming_timeIdx_le_idxBefore rho hte)
      have hf := (cpCompat_of_scopedFrame p c E rho hstore hframe hstrat
        (timeIdx rho t) y β hy hn.history).2.1
      exact ⟨(hl y hy).1, hβ ▸ Bool.or_eq_true_iff.mpr
        (Or.symm (hf.imp eraseFG_preceq eraseFG_preceq))⟩
    have het : SA.gateTime p.toParams (l + 1) + L p ≤ t := le_of_not_gt hte
    have hIe : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤
        V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1) + L p) :=
      (preIdx_le_afterTicksIdx E rho hs _).2.trans (arming_timeIdx_le_idxBefore rho
        (lt_add_of_pos_right _ (arming_L_pos p)))
    obtain ⟨hseedB, _, _, hseedLocal⟩ := hall _ hIe le_rfl
    have hseed : OutageSourceHistory p c E rho (eraseFG β)
        (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1) + L p)) := hβ.symm ▸ hseedB
    have hSseed : ∀ x ∈ rho.honest, Block.Preceq (eraseFG β)
        (S_at p c E rho (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1) + L p)) x) :=
      fun x hx => hβ.symm ▸ (hseedLocal x hx).1
    have hGST := fun q hq => h.gst.trans ((hr q).mpr hq)
    have hpartAfter := fun q hq hhor => h.partAfter _ ((hr q).mpr hq) hhor
    have hbefore : ∀ q, r ≤ q → SA.voteTime p.toParams q <
        SA.gateTime p.toParams (l + 1) + L p → ∀ i x,
        rho.events[i]? = some (.tick x (SA.voteTime p.toParams q)) →
        Block.Preceq (eraseFG β) (headVote p
          (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams q)) q) := by
      intro q hq hqe i x ht
      rw [hβ]
      exact outageV_first_restored_head hvalid hnr hcstar hdelta hfault hstore hframe hsrc
        htsrc hroots hstrat hnamesFull hne hc hSync ⟨hpart⟩
        (h.order.2.2.1.trans ((hr q).mpr hq)) hqe ht
    have hheads := outageV_restored_heads hvalid hnr hcstar hdelta hstore hframe hstrat
      htsrc hroots hnamed h.sync hcumul origin β (l + 1) r hrbound hGST hpartAfter
      hseed hSseed hbefore
    obtain ⟨q, hq⟩ := outageV_first_restored_exists p (rho.horizon + 1)
    have hstop : rho.horizon < SA.voteTime p.toParams q := by
      have hh := (hq q).mpr le_rfl
      change (_ : Int) ≤ _ at hh
      change (_ : Int) < _
      omega
    have hpartBefore : ∀ a, r ≤ a → a < q → (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams a)).card := by
      intro a ha haq
      have haH : SA.voteTime p.toParams a ≤ rho.horizon := by
        have hn : ¬ rho.horizon + 1 ≤ SA.voteTime p.toParams a :=
          fun hh => (not_le.mpr haq) ((hq a).mp hh)
        change ¬ ((_ : Int) ≤ _) at hn
        change (_ : Int) ≤ _
        omega
      exact hpartAfter a ha haH
    have hEi : V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1) + L p) ≤
        timeIdx rho t := (arming_idxBefore_le_timeIdx rho _).trans (arming_timeIdx_mono rho het)
    have hidx : timeIdx rho t ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams q + p.Δ) :=
      arming_timeIdx_le_idxBefore rho (hthor.trans_lt
        (hstop.trans (lt_add_of_pos_right _ p.deltaPos)))
    have hh := outageV_events_through_relay hvalid hnr hcstar hdelta hstore hframe hstrat
      htsrc hroots hnamed h.sync β (l + 1) r q hrbound (fun a ha _ => hGST a ha)
      hpartBefore (fun a ha _ => hheads a ha) hseed hSseed hEi hidx
    exact hβ ▸ hh.2 y hy
  have hstable := arming_stable_read hs y t
  exact ⟨hlocal.1, hstable.symm ▸ hlocal.1, hstable.symm ▸ hlocal.1, hlocal.2⟩

end Seed

section Body
variable [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
variable (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hnonempty : ∀ i y s, i < timeIdx rho b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hbelow : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsavedKeep : fast = false → ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho
          (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
          Block.Preceq C' C)

include hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
  hsavedKeep hsOrigin hmono hcleanGate in
/-- OUTPUT-DIRECT §10. DC: INTENTIONAL; the corrected outage premise and
healthy-cut supplier facts produce arming and all continuation outputs. -/
theorem outageV_body (h : OutageContinuationPrem p c fast E rho T b₀ b₁ ΔF)
    (hstrat : RStrat p c E rho) (hcumul : RStoreCumul p c E rho)
    (origin : RQCOrigin p c E rho) : OutageContinuationConcl p c E rho T b₀ := by
  intro x B hx hread y t hy hbt hthor
  by_cases hne : B = .genesis
  · subst B
    exact ⟨block_genesis_preceq _, block_genesis_preceq _, block_genesis_preceq _,
      Bool.or_eq_true_iff.mpr (Or.inl (block_genesis_preceq _))⟩
  have h0 := outageV_arming_prem h
  have hreadStable : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T) := by
    rw [arming_stable_read h.pre.base.valid.toScheduleWellFormed x T]
    exact hread
  have harm : ArmingData p c E rho fast T b₀ b₀ B := by
    cases fast with
    | true =>
      exact fast_arming (hroots := h.pre.base.idealization) (hstrat := hstrat)
        T b₀ b₀ ΔF h.pre.base.valid h.pre.base.cstar h.pre.base.noRestart h.pre.base.delta
        h.pre.cut h.pre.healthy h.pre.partBefore h0.order h0.budget x B hx hreadStable hne
        hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
        hsOrigin hmono hcleanGate h.lag (h.fastPart rfl)
    | false =>
      exact slow_arming (hroots := h.pre.base.idealization) (hstrat := hstrat)
        T b₀ b₀ ΔF h.pre.base.valid h.pre.base.cstar h.pre.base.noRestart h.pre.base.delta
        h.pre.cut h.pre.healthy h.pre.partBefore h0.order h0.budget x B hx hreadStable hne
        hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
        (hsavedKeep rfl) hsOrigin hmono hcleanGate h.lag
  rw [ArmingData_def] at harm
  obtain ⟨u, s, C, iₛ, D, Dh, hc⟩ := harm
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hh := hc.gate_le_cut
    rw [arming_gate_eq] at hh
    have hn : 0 ≤ 4 * p.Δ * ((((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat : Nat) : Int) := by
      have := p.deltaPos
      positivity
    linarith
  obtain ⟨r, hr⟩ := outageV_first_restored_exists p b₁
  have hrbound := (outageV_iff_restored_label p b₀ b₁ h6 r hr).mp h.lengthV
  exact outageV_armed_outputs h hstore hframe hsrc htsrc hstrat hcumul origin hnamed
    hne hc r hr hrbound y t hy hbt hthor

end Body

end AvailableChain.FGSA.Run
end
