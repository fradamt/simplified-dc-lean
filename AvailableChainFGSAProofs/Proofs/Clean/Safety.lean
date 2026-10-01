module
public import AvailableChainFGSAProofs.Proofs.Clean.Closure
public import AvailableChainFGSAProofs.Proofs.Clean.GateOutput

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open AvailableChain.SimplexFG
open Gen.Pure (CompatOn MonoOn)

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- P3 §8.5 (cleanSafety), bp02 §6: transport the supplied truncation to
all public reads. DC Generic/Properties:27,41,48 and Generic/Interface:64
have the same compatibility and monotonicity meaning. The representation
and all-integer domain differ intentionally: finite prefix reads always
have an index at most the event count, even outside the run horizon.
Three-class rule: INTENTIONAL, for this finite-read reason (S3 D43/D61);
no UNMOTIVATED or UNCLEAR premise difference. No restart, quorum, channel,
or extra honesty premise is needed by this read transport. -/
theorem cleanSafety_of_trunc_body
    (hs : V2.D.ScheduleWellFormed E rho)
    (ht :
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho rho.horizon) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho rho.horizon) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon)) ∧
  ((∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest → IsGateTick p c rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → IsGateTick p c rho j v s →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho rho.horizon → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho rho.horizon → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho rho.horizon → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)) ∧
  (∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))) ∧
  (∀ l x, SA.gateTime p.toParams l ≤ rho.horizon → x ∈ rho.honest →
    ∃ B, gateResult p c E rho x l = some (some B) ∧
      (∃ j, IsGateTick p c rho j x l ∧ gatePassedAt p c E rho j) ∧
      Block.Preceq B (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams l)) x) ∧
      ∀ l' < l, ∀ B', gateResult p c E rho x l' = some (some B') → Block.Preceq B' B)) :
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True)) := by
  have hlast : timeIdx rho rho.horizon = rho.events.length := by
    change (rho.events.filter _).length = _
    congr 1
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (hs.in_horizon e he).2
  have hbound (t : Time) : timeIdx rho t ≤ rho.events.length :=
    List.length_filter_le _ _
  have hread (g) (hg : g ∈ [(fgsaInterface p c).stable,
      (fgsaInterface p c).confirmed]) (t : Time) (x : V) :
      V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  have hc := ht.1
  have hm := ht.2.1
  rw [hlast] at hc hm
  refine ⟨hc, hm, ?_⟩
  intro g hg
  constructor
  · intro t u x y _ _ hx hy
    change Block.Compatible (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g y u)
    rw [hread g hg t x, hread g hg u y]
    exact hc _ _ _ _ (hbound t) (hbound u) hx hy
  · intro t u x _ _ htu hx
    change Block.Preceq (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g x u)
    rw [hread g hg t x, hread g hg u x]
    exact hm _ _ _ (hbound t) (hbound u)
      (V2.D.Engine.read_length_mono t u htu) hx

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27. INTENTIONAL difference:
S origins use raw gate results and event indices at an inclusive finite cut.
NoRestart is inherited from Base₂.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_sCompatible [Fintype V] {b₀ : Time}
    (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho b₀) := by
  have hh := clean_invariant p c E rho h hq hf hsrc _ le_rfl
  have ho := (cleanHistoryAt_body p c E rho h hq hf hsrc).2.2.2.1
  intro i j x y hi hj hx hy
  exact cleanHist_belowLabel_compatible hh
    (belowLabel_mono_index hi (ho i x hi hx).2.2.1)
    (belowLabel_mono_index hj (ho j y hj hy).2.2.1)

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27,41 and Generic/Interface:64.
INTENTIONAL representation difference: both FG-SA getters read S.
The time domain is the bounded inclusive Clean cut. NoRestart is in Base₂.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem clean_outputsAt [Fintype V] {b₀ : Time}
    (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t)
        (fun t => 0 ≤ t ∧ t ≤ b₀) ∧
      MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t)
        (fun t => 0 ≤ t ∧ t ≤ b₀) := by
  have hread (g) (hg : g ∈ [(fgsaInterface p c).stable,
      (fgsaInterface p c).confirmed]) (t : Time) (x : V) :
      V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [V2.D.Engine.readAt_eq_stateBefore h.base.valid.toScheduleWellFormed t] <;> rfl
  intro g hg
  constructor
  · intro t u x y ht hu hx hy
    change Block.Compatible (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g y u)
    rw [hread g hg t x, hread g hg u y]
    exact clean_sCompatible p c E rho h hq hf hsrc _ _ _ _
      (V2.D.Engine.read_length_mono t b₀ ht.2) (V2.D.Engine.read_length_mono u b₀ hu.2) hx hy
  · intro t u x _ hu htu _
    change Block.Preceq (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g x u)
    rw [hread g hg t x, hread g hg u x]
    exact sExtends p c E rho h hq hf hsrc x _ _
      (V2.D.Engine.read_length_mono t u htu) (V2.D.Engine.read_length_mono u b₀ hu.2)

/-- P3:3331–3335, bp02 §5.5; DC SafetyRegimes:61–75.
INTENTIONAL difference: raw SA results, whole-result guard, and the cut
before same-time deliveries. NoRestart is inherited from Base₂.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanGateAt_body [Fintype V] {b₀ : Time}
    (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
  ∀ l x, SA.gateTime p.toParams l ≤ b₀ → x ∈ rho.honest →
    ∃ B, gateResult p c E rho x l = some (some B) ∧
      (∃ j, IsGateTick p c rho j x l ∧ gatePassedAt p c E rho j) ∧
      Block.Preceq B (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams l)) x) ∧
      ∀ l' < l, ∀ B', gateResult p c E rho x l' = some (some B') → Block.Preceq B' B := by
  intro l x hl hx
  have hs := h.base.valid.toScheduleWellFormed
  have heq : ((4 * l + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams l := by
    change ((4 * l + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (l : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs h.base.delta x hx
    (4 * l + 6) (heq ▸ hl.trans h.cut.2)
  rw [heq] at hj
  have hjN := (V2.D.Engine.index_lt_read_length_iff hs b₀ hj).mpr hl
  have hjI : j + 1 ≤ timeIdx rho b₀ := Nat.succ_le_of_lt hjN
  obtain ⟨B, hB, hp, hBS⟩ := clean_gateOutput_body p c E rho b₀ h hq hf hsrc
    (j + 1) hjI (clean_invariant p c E rho h hq hf hsrc _ hjI)
    j x l (Nat.lt_succ_self j) hx hj
  have hpub := (gateResultAt_eq_gateResult p c E rho hs hj).symm.trans hB
  have hjcut : j < afterTicksIdx rho (SA.gateTime p.toParams l) := by
    by_contra hn
    have hfalse := V2.D.Engine.filter_false_of_index_ge hs
      (cutPred (P := fgsa p c) (SA.gateTime p.toParams l))
      (fun e f hef hf => decide_eq_true (hef.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hj
    change decide (toLex (SA.gateTime p.toParams l, (1 : Nat)) ≤
      toLex (SA.gateTime p.toParams l, (1 : Nat))) = false at hfalse
    have ht : decide (toLex (SA.gateTime p.toParams l, (1 : Nat)) ≤
        toLex (SA.gateTime p.toParams l, (1 : Nat))) = true := decide_eq_true le_rfl
    exact Bool.noConfusion (ht.symm.trans hfalse)
  have hcutN : afterTicksIdx rho (SA.gateTime p.toParams l) ≤ timeIdx rho b₀ :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans (V2.D.Engine.read_length_mono _ _ hl)
  refine ⟨B, hpub, ⟨j, hj, hp⟩,
    Gen.Pure.block_preceq_trans hBS
      (sExtends p c E rho h hq hf hsrc x _ _ (Nat.succ_le_of_lt hjcut) hcutN), ?_⟩
  intro l' hll B' hB'
  have htime : SA.gateTime p.toParams l' ≤ SA.gateTime p.toParams l := by
    change 4 * p.Δ * (l' : Int) + 6 * p.Δ ≤ 4 * p.Δ * (l : Int) + 6 * p.Δ
    have hcast : (l' : Int) < (l : Int) := by exact_mod_cast hll
    have := p.deltaPos
    nlinarith
  exact ((cleanHistoryAt_body p c E rho h hq hf hsrc).1 x x l' l B' B hx hx
    (htime.trans hl) hl hB' hpub).1 hll

/-- P3 §8.5, bp02 §§5.4–6; DC Legacy/Definitions/SafetyRegimes:53–80.
INTENTIONAL difference: six finite-cut clauses use raw SA gates and exact
FG-SA state origins. NoRestart is inherited from CleanCut₂ through Base₂.
The conclusion is the unfolded frozen body; Claims stays in Export.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanTruncAt_body [Fintype V] {b₀ : Time}
    (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho b₀) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho b₀) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun t => 0 ≤ t ∧ t ≤ b₀) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun t => 0 ≤ t ∧ t ≤ b₀)) ∧
  ((∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho b₀ → x ∈ rho.honest → IsGateTick p c rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho x s = some (some B) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → IsGateTick p c rho j v s →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho b₀ → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho b₀ → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho b₀ → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)) ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))) ∧
  (∀ l x, SA.gateTime p.toParams l ≤ b₀ → x ∈ rho.honest →
    ∃ B, gateResult p c E rho x l = some (some B) ∧
      (∃ j, IsGateTick p c rho j x l ∧ gatePassedAt p c E rho j) ∧
      Block.Preceq B (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams l)) x) ∧
      ∀ l' < l, ∀ B', gateResult p c E rho x l' = some (some B') → Block.Preceq B' B) := by
  refine ⟨clean_sCompatible p c E rho h hq hf hsrc, ?_,
    clean_outputsAt p c E rho h hq hf hsrc,
    cleanHistoryAt_body p c E rho h hq hf hsrc, ?_,
    cleanGateAt_body p c E rho h hq hf hsrc⟩
  · intro i j x _ hj hij _
    exact sExtends p c E rho h hq hf hsrc x i j hij hj
  · intro i v hi hv
    have hframe := cleanFrame (ΔF := ΔF) p c E rho (b₀ := b₀)
    rw [CleanFrameStmt_def (ΔF := ΔF)] at hframe
    exact hframe h hq hf hsrc i hi
      (clean_invariant p c E rho h hq hf hsrc i hi) v hv

end AvailableChain.FGSA.Run
end
