module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedBridge
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedEarly

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The public W-reader branch names its actual post-E gate and awake suffix.
The regime produces the batch again at that gate, and the enabled guard supplies
the receipt epoch. No batch is inferred at the gate actor's earlier HEAD tick. -/
theorem outage_caught_up_gate_scope [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    {x : V} {t : Time}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (hOutside : x ∉ coveredNodes p E rho fast b₀) (hhor : t ≤ rho.horizon) :
    ∃ s j, restoredLabel p b₁ + p.k ≤ s ∧ j < timeIdx rho t ∧
      enabledGateAt p c E rho j x s ∧
      BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) ∧
      AwakeClosed E x (SA.gateTime p.toParams s) t ∧
      RestartFreeTime rho x (SA.gateTime p.toParams s) t ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
        (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) := by
  obtain ⟨hConfirmed, hCovered | ⟨s, j, hEnd, hst, hj, hG, _, hAw, hRF⟩⟩ := hReader
  · exact (hOutside hCovered).elim
  have hLabel : restoredLabel p b₁ + p.k ≤ s := by
    change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤
      4 * p.Δ * (s : Int) + 6 * p.Δ at hEnd
    have hlt : ((restoredLabel p b₁ + p.k : Nat) : Int) < (s : Int) + 1 := by
      nlinarith [p.deltaPos]
    dsimp only [Slot] at *
    omega
  have hrs : restoredLabel p b₁ ≤ s := (Nat.le_add_right _ _).trans hLabel
  have hJ := outage_enabled_gate_joined h.pre.base.valid hConfirmed.1 hG
  have hEG : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hBatch := (outage_continuation_receipt h).2.1 x s hrs
    (hEG.le.trans (hst.trans hhor)) ⟨hConfirmed.1, hJ⟩
  have hEpoch := outage_restored_reader_epoch h.pre.base.valid.toScheduleWellFormed hJ
    (a := SA.voteTime p.toParams s)
    (by change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
        linarith [p.deltaPos]) (fgsa_vote_lt_gate p s)
  exact ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF,
    hEpoch.mono le_rfl (fgsa_idxBefore_mono rho hEG.le)⟩

/-- The finalized branch supplies inclusion at the actual inclusive read.
This branch needs no covering target demand on later HEADs. -/
theorem outage_finalized_continuation_read {x : V} {t : Time} {B : Block}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hBF : Block.Preceq B (F_at p c E rho (timeIdx rho t) x)) :
    Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  have hFS := fgsaAC_anchor_le_output E rho (timeIdx rho t) x
  have hBS := Gen.Pure.block_preceq_trans hBF hFS
  exact ⟨hBS, outage_continuation_inclusive_read hs hBS
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) hBF)⟩

/-- The actual W gate uses the produced global HEAD invariant. Its batch,
awake suffix and epoch remain explicit; raw result compatibility is produced. -/
theorem outage_caught_up_gate_result_history [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {t : Time}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (hOutside : x ∉ coveredNodes p E rho fast b₀) (hhor : t ≤ rho.horizon) :
    ∃ s j, restoredLabel p b₁ + p.k ≤ s ∧ j < timeIdx rho t ∧
      enabledGateAt p c E rho j x s ∧
      BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) ∧
      AwakeClosed E x (SA.gateTime p.toParams s) t ∧
      RestartFreeTime rho x (SA.gateTime p.toParams s) t ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
        (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) ∧
      ∀ C, gateResultAt p c E rho j = some (some C) → Block.Compatible C B := by
  obtain ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF, hEpoch⟩ :=
    outage_caught_up_gate_scope h hReader hOutside hhor
  refine ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF, hEpoch, ?_⟩
  intro C hC
  have hks := p.kLarge
  have hrs : restoredLabel p b₁ < s := by dsimp only [Slot] at *; omega
  exact outage_continuation_result_of_head_history h hReader.1.1 hrs hG hC
    (fun q K hR hK => outage_continuation_scoped_heads h hf origin htsrc hnamed hsrc
      hState hprov hne hc hβ s q K hrs hR hK)

/-- A gate preserves stable compatibility when the old record and its result are compatible. -/
theorem outage_gateStep_stable_compatible (p : Params) (st : State p.n)
    (hinv : CStoreInv p st) (s : Slot) (B : Block)
    (hS : Block.Compatible st.base.stableRecord B)
    (hF : Block.Compatible (eraseFG st.fg.F) B)
    (hC : joinedNow p st = true → ∀ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some C → Block.Compatible C B) :
    Block.Compatible (gateStep p st s).base.stableRecord B := by
  have norm (q : State p.n) (hQ : Block.Compatible q.base.stableRecord B)
      (hFQ : Block.Compatible (eraseFG q.fg.F) B) :
      Block.Compatible (normalizeS q).base.stableRecord B := by
    rw [normalizeS_fields]
    change Block.Compatible (if Block.preceq (eraseFG q.fg.F) q.base.stableRecord
      then q.base.stableRecord else eraseFG q.fg.F) B
    split <;> assumption
  by_cases hJ : joinedNow p st = true
  swap
  · have hN := Bool.eq_false_iff.mpr hJ
    unfold gateStep
    rw [hN]
    simp only [Bool.not_false, ite_true]
    split <;> exact norm _ hS hF
  let Q : State p.n := { onView
    (fun v => SA.Root.gateFrom p.toParams (eraseFG st.fg.F) v s) st with
    fastWrite := st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] }
  have hQ : Block.Compatible Q.base.stableRecord B := by
    change Block.Compatible
      (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).stableRecord B
    rcases (saGate_cases p.toParams (eraseFG st.fg.F) (actView st) s
      hinv.leaseKeys.1 hinv.leaseKeys.2).2.2 with he | ⟨C, hRaw, he⟩
    · rw [he]; exact hS
    · rw [he]
      unfold GridCO.advance
      split
      · exact hS
      · exact hC hJ C hRaw
  unfold gateStep
  rw [hJ]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  change Block.Compatible
    (normalizeS (if (GridCO.savedGenuine st.base s).isSome then st else Q)).base.stableRecord B
  split
  · exact norm st hS hF
  · exact norm Q hQ hF

/-- The local inclusive suffix needs only compatible enabled results and current F.
It includes restart and same-time delivery events. -/
theorem outage_stable_compatible_suffix
    (hBase : Base₂ p c E rho) {x : V} {B : Block} {s : Slot} {j I : Nat}
    (_hG : enabledGateAt p c E rho j x s) (hjI : j < I)
    (hSeed : Block.Compatible (S_at p c E rho (j + 1) x) B)
    (hF : ∀ i, j + 1 ≤ i → i ≤ I → Block.Compatible (F_at p c E rho i x) B)
    (hResults : ∀ i q C, j < i → i < I → enabledGateAt p c E rho i x q →
      gateResultAt p c E rho i = some (some C) → Block.Compatible C B) :
    Block.Compatible (S_at p c E rho I x) B := by
  have hs := hBase.valid.toScheduleWellFormed
  have suff : ∀ i, j + 1 ≤ i → i ≤ I → Block.Compatible (S_at p c E rho i x) B := by
    intro i hji
    induction i, hji using Nat.le_induction with
    | base => intro _; exact hSeed
    | succ i hji ih =>
      intro hi
      have hiI : i < I := by omega
      have hSi := ih hiI.le
      rcases fgsaAC_output_step E rho i x with he | ⟨q, ht⟩ |
          ⟨o, t, b, _, _, _, hn⟩ | ⟨t, hr, _⟩
      · change S_at p c E rho (i + 1) x = S_at p c E rho i x at he
        rw [he]; exact hSi
      · have post : storeAt p c E rho (i + 1) x =
            clock p (storeAt p c E rho i x) (SA.gateTime p.toParams q) := by
          change (rho.stateBefore E (i + 1) x).st = _
          rw [(rho.step_tick_eq E ht).1]
          exact tick_st (c := c) E rho _ x _
        change Block.Compatible (storeAt p c E rho (i + 1) x).base.stableRecord B
        rw [post, arming_clock_gate]
        apply outage_gateStep_stable_compatible p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _) q B
        · rw [clockPre_stable]; exact hSi
        · rw [clockPre_fg]; exact hF i hji hiI.le
        · intro hJ C hC
          have hguard : joinedAtTime p (storeAt p c E rho i x).restartTime
              (SA.gateTime p.toParams q) = true := by
            rw [clockPre_joined] at hJ
            exact hJ
          have hslot : p.slotOf (SA.gateTime p.toParams q) = q + 1 :=
            (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
              (fgsa_gate_slot (c := c) (rho.stateBefore E i x) q)
          have hEnabled : enabledGateAt p c E rho i x q := by
            refine ⟨ht, ?_⟩
            cases hr : (storeAt p c E rho i x).restartTime with
            | none => trivial
            | some w =>
              simp only [joinedAtTime, hr, hslot, Nat.cast_add, Nat.cast_one,
                add_sub_cancel_right, decide_eq_true_eq] at hguard
              exact hguard
          exact hResults i q C (by omega) hiI hEnabled
            ((inclusion_gate_raw_at_tick E rho hs hEnabled).trans (congrArg some hC))
      · change S_at p c E rho (i + 1) x =
          Gen.AC.normalizeOutput (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hn
        rw [hn, Gen.AC.normalizeOutput_def]
        split
        · exact hSi
        · exact hF (i + 1) (by omega) hi
      · change Block.Compatible (storeAt p c E rho (i + 1) x).base.stableRecord B
        have post : storeAt p c E rho (i + 1) x = acRestart p (storeAt p c E rho i x) t := by
          change (rho.stateBefore E (i + 1) x).st = _
          rw [V2.D.Engine.state_after_restart hr]; rfl
        rw [post, acRestart_stableRecord]
        exact hSi
  exact suff I (Nat.succ_le_of_lt hjI) le_rfl

/-- O11-W-READ carries the actual post-gate seed to the inclusive public read.
The global producer supplies all later enabled results and durable F compatibility. -/
theorem outage_caught_up_public_read_from_seed [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {t : Time} {s : Slot} {j : Nat}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (_hhor : t ≤ rho.horizon) (hLabel : restoredLabel p b₁ + p.k ≤ s)
    (hj : j < timeIdx rho t) (hG : enabledGateAt p c E rho j x s)
    (hSeed : Block.Compatible B (S_at p c E rho (j + 1) x)) :
    Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hrs : restoredLabel p b₁ < s := by
    have := p.kLarge; dsimp only [Slot] at *; omega
  have hEarly : SA.earlyTime p.toParams (restoredLabel p b₁) <
      SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]
    have hc := Int.ofNat_le.mpr hrs.le
    nlinarith [p.deltaPos]
  have hGateHor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hHor := hEarly.le.trans hGateHor
  have hStart : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ j :=
    le_of_not_gt (fun hn => (not_lt_of_ge (arming_tick_le hs hG.1
      (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2))) hEarly)
  have state {i : Nat} (hi : j ≤ i) (hlen : i ≤ rho.events.length) :=
    outage_continuation_event_state h hf origin htsrc hnamed hsrc hState hprov hne hc hβ
      hHor (hStart.trans hi) hlen
  have hLen : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
  have current := state hj.le hLen
  have hS := outage_stable_compatible_suffix h.pre.base hG hj
    (Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp hSeed)))
    (fun i hji hi => (state (by omega) (hi.trans hLen)).2.2.2.1 x hReader.1.1)
    (by
      intro i q C hji hi hEnabled hC
      have htime : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams q := by
        apply le_of_not_gt
        intro hn
        have hij := V2.D.Engine.eventIndex_lt_of_time_lt hs hEnabled.1 hG.1 hn
        omega
      have hsq : s ≤ q := (arming_gate_le_iff p s q).mp htime
      exact current.1 i x q C hi hReader.1.1 (hrs.trans_le hsq) hEnabled hC)
  have hStable : V2.D.outputAt E rho (fgsaInterface p c).stable x t =
      S_at p c E rho (timeIdx rho t) x := arming_stable_read hs x t
  have hConfirmed : V2.D.outputAt E rho (fgsaInterface p c).confirmed x t =
      S_at p c E rho (timeIdx rho t) x := arming_stable_read hs x t
  have symm (A : Block) (h : Block.Compatible A B) : Block.Compatible B A :=
    Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp h))
  exact ⟨symm _ hS, hStable.symm ▸ symm _ hS, hConfirmed.symm ▸ symm _ hS,
    symm _ (current.2.2.2.1 x hReader.1.1)⟩

/-- Join the finite early reads, covered suffix and actual W gate.
The W seed is the exact remaining P-Ou obligation, not a supplied public premise. -/
theorem outage_continuation_public_reads [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
    (hWSeed : ∀ x t s j, outageConfirmedReader p c E rho fast b₀ b₁ x t →
      x ∉ coveredNodes p E rho fast b₀ → t ≤ rho.horizon →
      restoredLabel p b₁ + p.k ≤ s → j < timeIdx rho t →
      enabledGateAt p c E rho j x s →
      BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) →
      AwakeClosed E x (SA.gateTime p.toParams s) t →
      RestartFreeTime rho x (SA.gateTime p.toParams s) t →
      V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
        (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) →
      ¬ Block.Preceq B (F_at p c E rho j x) →
      Block.Compatible B (S_at p c E rho (j + 1) x)) :
    ∀ x t, b₀ ≤ t → t ≤ rho.horizon →
      outageConfirmedReader p c E rho fast b₀ b₁ x t →
      Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      (x ∈ coveredNodes p E rho fast b₀ →
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
        Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
        Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t)) := by
  classical
  intro x t hb hhor hReader
  have hs := h.pre.base.valid.toScheduleWellFormed
  by_cases hEarly : t < SA.earlyTime p.toParams (restoredLabel p b₁)
  · exact outage_early_public_read h hf htsrc hnamed hsrc hState hprov hne hc hβ
      hHist hOutput hb hhor hEarly hReader
  have ht := le_of_not_gt hEarly
  by_cases hxG : x ∈ coveredNodes p E rho fast b₀
  · obtain ⟨hStable, hConfirmed, _⟩ := outage_covered_public_read_after_seed h hf origin
      htsrc hnamed hsrc hState hprov hne hc hβ hxG ht hhor
    have hS : Block.Preceq B (S_at p c E rho (timeIdx rho t) x) := by
      rwa [arming_stable_read hs] at hStable
    exact ⟨block_compatible_of_common hS (block_preceq_refl _),
      block_compatible_of_common hStable (block_preceq_refl _),
      block_compatible_of_common hConfirmed (block_preceq_refl _),
      fun _ => ⟨hS, hStable, hConfirmed⟩⟩
  have hRead : Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) := by
    by_cases hBF : Block.Preceq B (F_at p c E rho (timeIdx rho t) x)
    · obtain ⟨hS, hStable, hConfirmed, _⟩ := outage_finalized_continuation_read hs hBF
      exact ⟨block_compatible_of_common hS (block_preceq_refl _),
        block_compatible_of_common hStable (block_preceq_refl _),
        block_compatible_of_common hConfirmed (block_preceq_refl _)⟩
    · obtain ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF, hEpoch⟩ :=
        outage_caught_up_gate_scope h hReader hxG hhor
      have hLow : ¬ Block.Preceq B (F_at p c E rho j x) := by
        intro hBj
        exact hBF (block_preceq_trans hBj (eraseFG_preceq
          (hf.mono j (timeIdx rho t) x hReader.1.1 hj.le).1))
      have hSeed := hWSeed x t s j hReader hxG hhor hLabel hj hG hBatch hAw hRF hEpoch hLow
      obtain ⟨hS, hStable, hConfirmed, _⟩ := outage_caught_up_public_read_from_seed h hf origin
        htsrc hnamed hsrc hState hprov hne hc hβ hReader hhor hLabel hj hG hSeed
      exact ⟨hS, hStable, hConfirmed⟩
  exact ⟨hRead.1, hRead.2.1, hRead.2.2, fun hx => (hxG hx).elim⟩

/-- The complete scoped HEAD and F consumers have no continuation callback.
Early labels use covered duty history; later labels use ScopedBridge's global producer. -/
theorem outage_continuation_public_heads_and_finality [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
 :
    (∀ y t o H, b₀ ≤ t → t ≤ rho.horizon →
      outageHeadReader p E rho fast b₀ b₁ y t →
      V2.D.Run.emits E rho y o t → HeadTargetAtEmission p c E rho y o t H →
      Block.Compatible B H) ∧
    (∀ y t, y ∈ rho.honest → b₀ ≤ t → t ≤ rho.horizon →
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y)) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have symm (A : Block) (h : Block.Compatible A B) : Block.Compatible B A :=
    Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp h))
  constructor
  · intro y t o H hb hhor hReader hem hTarget
    have hKeep := hTarget
    obtain ⟨i, s, q, hi, hm, ho, _⟩ := hTarget
    have hm' := hm
    rw [ho, (rho.step_tick_eq E hi).2] at hm'
    have hFields := (fgsa_emits_head E rho _ y t s q H.root).mp hm'
    have ht : t = SA.voteTime p.toParams s := hFields.2.1.symm
    have hy : y = rho.seatOf (.base (.head s)) q := hFields.2.2.1.symm
    subst t; subst y
    have hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, H.root⟩) (SA.voteTime p.toParams s) H := by
      rwa [ho] at hKeep
    by_cases hsr : s ≤ restoredLabel p b₁
    · have hBH := outage_early_scoped_head h hf htsrc hnamed hsrc hState hprov hne hc hβ
        hsr hb hhor hReader hK
      exact block_compatible_of_common hBH (block_preceq_refl _)
    · exact symm H (outage_continuation_scoped_heads h hf origin htsrc hnamed hsrc
        hState hprov hne hc hβ s q H (Nat.lt_of_not_ge hsr) hReader hK)
  · intro y t hy hb hhor
    by_cases hEarly : t < SA.earlyTime p.toParams (restoredLabel p b₁)
    · exact outage_early_finalized_read h hf htsrc hnamed hsrc hState hprov hne hc hβ
        hy hb hhor hEarly
    have ht := le_of_not_gt hEarly
    have hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤
        timeIdx rho t := (preIdx_le_afterTicksIdx E rho hs _).2.trans
          (arming_timeIdx_mono rho ht)
    exact symm _ ((outage_continuation_event_state h hf origin htsrc hnamed hsrc hState
      hprov hne hc hβ (ht.trans hhor) hI (List.length_filter_le _ _)).2.2.2.1 y hy)

end AvailableChain.FGSA.Run
end
