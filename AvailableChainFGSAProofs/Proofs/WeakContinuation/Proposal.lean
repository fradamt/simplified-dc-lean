module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead

public section

/-! WC J3, plan §6.9; DC proposal comparison prefix.
Blueprint 23 §11 restricts the finite maximum to the seed and labels through s−2. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC J3, plan §6.9; DC comparison prefix: a finite compatible history has a maximum.
Only actual completed suffix results enter the set; the seed makes it nonempty. -/
theorem wc_historyMax
    (hi : WCInv p c E rho w iStar rho.events.length) (r : Slot) :
    ∃ D, (D = w.QStar ∨ ∃ j x s,
      WCResult p c E rho w iStar rho.events.length j x s D ∧ s ≤ r) ∧
      Block.Preceq w.QStar D ∧
      ∀ j x s B, WCResult p c E rho w iStar rho.events.length j x s B →
        s ≤ r → Block.Preceq B D := by
  classical
  let candidates : Finset Block := (Finset.range rho.events.length).image
    (fun j => ((gateResultAt p c E rho j).getD none).getD .genesis)
  let genuine := candidates.filter (fun B => ∃ j x s,
    WCResult p c E rho w iStar rho.events.length j x s B ∧ s ≤ r)
  let pool := insert w.QStar genuine
  have hseed {j x s B}
      (hB : WCResult p c E rho w iStar rho.events.length j x s B) :
      Block.Preceq w.QStar B := by
    obtain ⟨C, hC, hQC, _⟩ := hi.nonempty j x s hB.afterCut hB.completed
      hB.honest hB.event hB.label
    have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hB.value))
    exact he ▸ hQC
  have hmem {j x s B}
      (hB : WCResult p c E rho w iStar rho.events.length j x s B) (hs : s ≤ r) :
      B ∈ genuine := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hB.completed, ?_⟩,
      j, x, s, hB, hs⟩
    rw [hB.value]
    rfl
  have hcompatible {j k x y s t B C}
      (hB : WCResult p c E rho w iStar rho.events.length j x s B)
      (hC : WCResult p c E rho w iStar rho.events.length k y t C) :
      Block.Compatible B C := by
    rcases lt_trichotomy s t with h | h | h
    · exact block_compatible_of_common (hi.ordered j k x y s t B C hB hC h)
        (block_preceq_refl C)
    · subst t
      exact hi.sameLabel j k x y s B C hB hC
    · exact block_compatible_of_common (block_preceq_refl B)
        (hi.ordered k j y x t s C B hC hB h)
  have hpool : ∀ B ∈ pool, ∀ C ∈ pool, Block.Compatible B C := by
    intro B hB C hC
    rcases Finset.mem_insert.mp hB with rfl | hB
    · rcases Finset.mem_insert.mp hC with rfl | hC
      · exact block_compatible_of_common (block_preceq_refl _) (block_preceq_refl _)
      · obtain ⟨j, x, s, hC, _⟩ := (Finset.mem_filter.mp hC).2
        exact block_compatible_of_common (hseed hC) (block_preceq_refl _)
    · rcases Finset.mem_insert.mp hC with rfl | hC
      · obtain ⟨j, x, s, hB, _⟩ := (Finset.mem_filter.mp hB).2
        exact block_compatible_of_common (block_preceq_refl _) (hseed hB)
      · obtain ⟨j, x, s, hB, _⟩ := (Finset.mem_filter.mp hB).2
        obtain ⟨k, y, t, hC, _⟩ := (Finset.mem_filter.mp hC).2
        exact hcompatible hB hC
  obtain ⟨D, hD, hmax⟩ := deepest_of_compatible pool
    ⟨w.QStar, Finset.mem_insert_self ..⟩ hpool
  refine ⟨D, ?_, hmax _ (Finset.mem_insert_self ..), ?_⟩
  · rcases Finset.mem_insert.mp hD with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2
  · intro j x s B hB hs
    exact hmax B (Finset.mem_insert_of_mem (hmem hB hs))

/-- WC J3, plan §6.9; DC slot separation: gates read before v_s have label at most s−2. -/
private theorem wc_gateLabel_beforeVote (r s : Slot)
    (h : SA.gateTime p.toParams r ≤ SA.voteTime p.toParams s) : r + 2 ≤ s := by
  by_contra hn
  have hsr : s ≤ r + 1 := by
    simp only [Slot] at hn ⊢
    omega
  have hcast : (s : Time) ≤ (r : Time) + 1 := by exact_mod_cast hsr
  have hd := p.deltaPos
  have hscaled := mul_le_mul_of_nonneg_left hcast
    (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le)
  change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (s : Time) + p.Δ at h
  nlinarith

/-- WC J3, plan §6.9; DC selected-source history: high rows at the compared reads
have sources below the maximum. The pre-cut branch uses the seed bound only. -/
theorem wc_highSource_beforeVote
    (hi : WCInv p c E rho w iStar rho.events.length)
    (s : Slot) (D : Block) (hseedD : Block.Preceq w.QStar D)
    (hmax : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r ≤ s - 2 → Block.Preceq B D)
    {i j : Nat} {y : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    {K : SimplexFG.FGBlock (Fin p.n)} (hiN : i ≤ rho.events.length) (hji : j < i)
    (hbefore : ∀ k < i, ∀ event, rho.events[k]? = some event →
      event.time ≤ SA.voteTime p.toParams s)
    (hrow : HonestRowAt p c E rho j y r a)
    (hentry : namedEntry a.payload.height_pair = some e) (hhigh : w.M + 1 ≤ e.1)
    (hsource : actionSourceFG p c E rho y r = some (some K)) :
    Block.Preceq (eraseFG K) D := by
  by_cases hjcut : j < iStar
  · obtain ⟨C, hC, _, hCQ⟩ := hi.preCutHigh j y r a e hjcut hrow hentry hhigh
    have he : C = K := Option.some.inj (Option.some.inj (hC.symm.trans hsource))
    exact block_preceq_trans (he ▸ hCQ) hseedD
  · obtain ⟨B, hB, hKB⟩ := hi.suffixSources j y r K (Nat.le_of_not_lt hjcut)
      (hji.trans_le hiN) hrow.1 hrow.2.1 hsource
    have hlabel := wc_gateLabel_beforeVote (r * p.R) s (hbefore j hji _ hrow.2.1)
    have hr : r * p.R ≤ s - 2 := by
      simp only [Slot] at hlabel ⊢
      omega
    exact block_preceq_trans hKB (hmax j y (r * p.R) B hB hr)

/-- WC J3, plan §6.9; DC retrospective HEAD: enlarge only the covered prefix. -/
private theorem wc_headRead_of_prefix {i : Nat} {x : V} {s : Slot} {A B : Block}
    (h : WCHeadRead p c E rho i x s B) (hAB : Block.Preceq A B) :
    WCHeadRead p c E rho i x s A := by
  exact ⟨h.event, block_preceq_trans hAB h.covers,
    fun C hCA => h.path C (block_preceq_trans hCA hAB), h.receipts⟩

omit [DecidableEq V] in
/-- WC J3, plan §6.9; DC prefix agreement: a later tick is after the selected cut. -/
private theorem wc_cut_le_laterTick
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

/-- WC J3, plan §6.9; DC comparison prefix: previous HEADs cover every maximum member.
At the first eligible slot, the source seed supplies the pending HEAD read. -/
theorem wc_history_previousHeads
    (hs : V2.D.ScheduleWellFormed E rho) (hdelta : E.Δ = p.Δ)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (s : Slot) (D : Block) (hstart : w.u + 2 ≤ s)
    (hgate : SA.gateTime p.toParams s ≤ rho.horizon)
    (hmember : D = w.QStar ∨ ∃ j x r,
      WCResult p c E rho w iStar rho.events.length j x r D ∧ r ≤ s - 2) :
    ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y (s - 1) D := by
  intro y hy
  have hs2 : 2 ≤ s := by
    simp only [Slot] at hstart ⊢
    omega
  have hlabels : s - 2 + 1 = s - 1 := by
    simp only [Slot] at hs2 ⊢
    omega
  by_cases hfirst : s = w.u + 2
  · have hD : D = w.QStar := by
      rcases hmember with h | ⟨j, x, r, hresult, hr⟩
      · exact h
      · have hlabel := hresult.label
        simp only [hfirst, Slot] at hr hlabel
        omega
    subst D
    obtain ⟨k, _, hhead⟩ := hseed.nextHeads y hy
    refine ⟨k, ?_⟩
    have he : s - 1 = w.u + 1 := by
      simp only [Slot] at hfirst ⊢
      omega
    exact he.symm ▸ hhead
  · have hq : w.u < s - 2 := by
      simp only [Slot] at hstart hfirst ⊢
      omega
    have hd := p.deltaPos
    have htime : SA.gateTime p.toParams w.u < SA.gateTime p.toParams (s - 2) := by
      change 4 * p.Δ * (w.u : Time) + 6 * p.Δ <
        4 * p.Δ * ((s - 2 : Nat) : Time) + 6 * p.Δ
      have hcast : (w.u : Time) < ((s - 2 : Nat) : Time) := Nat.cast_lt.mpr hq
      nlinarith
    have hqtime : SA.gateTime p.toParams (s - 2) ≤ rho.horizon := by
      refine le_trans ?_ hgate
      change 4 * p.Δ * ((s - 2 : Nat) : Time) + 6 * p.Δ ≤
        4 * p.Δ * (s : Time) + 6 * p.Δ
      have hcast : ((s - 2 : Nat) : Time) ≤ (s : Time) :=
        Nat.cast_le.mpr (Nat.sub_le s 2)
      nlinarith
    have heq : ((4 * (s - 2) + 6 : Nat) : Time) * p.Δ =
        SA.gateTime p.toParams (s - 2) := by
      change ((4 * (s - 2) + 6 : Nat) : Int) * p.Δ =
        4 * p.Δ * ((s - 2 : Nat) : Int) + 6 * p.Δ
      push_cast
      ring
    obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hdelta y hy
      (4 * (s - 2) + 6) (heq ▸ hqtime)
    rw [heq] at hj
    have hjcut : iStar ≤ j := by
      rw [hseed.cut]
      exact wc_cut_le_laterTick hs hj htime
    have hjlength := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨C, hC, hQC, _⟩ := hi.nonempty j y (s - 2) hjcut hjlength hy hj hq
    have hresult : WCResult p c E rho w iStar rho.events.length j y (s - 2) C :=
      ⟨hy, hjcut, hjlength, hq, hj, hC⟩
    rcases hmember with h | ⟨k, x, r, hD, hr⟩
    · subst D
      obtain ⟨k, _, hk⟩ := hi.retrospective j y (s - 2) C hresult y hy
      exact ⟨k, hlabels ▸ wc_headRead_of_prefix hk hQC⟩
    · rcases Nat.lt_or_eq_of_le hr with hr | rfl
      · have hDC := hi.ordered k j x y r (s - 2) D C hD hresult hr
        obtain ⟨l, _, hl⟩ := hi.retrospective j y (s - 2) C hresult y hy
        exact ⟨l, hlabels ▸ wc_headRead_of_prefix hl hDC⟩
      · obtain ⟨l, _, hl⟩ := hi.retrospective k x (s - 2) D hD y hy
        exact ⟨l, hlabels ▸ hl⟩

/-- WC J3, plan §6.9; DC handler order: recover the actual proposal tick and input. -/
theorem wc_proposalInput {i : Nat} {x : V} {s : Slot} {st : State p.n}
    (h : WCDutyInput p c E rho i x (.proposal s) st) :
    rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)) ∧
      st = clock p (storeAt p c E rho i x) (SA.proposalTime p.toParams s) := by
  obtain ⟨t, he, hp | hh | hg | ha⟩ := h.input
  · obtain ⟨r, hr, ht, hst⟩ := hp
    cases hr
    exact ⟨ht ▸ he, ht ▸ hst⟩
  · obtain ⟨r, hr, _⟩ := hh
    cases hr
  · obtain ⟨r, hr, _⟩ := hg
    cases hr
  · obtain ⟨r, hr, _⟩ := ha
    cases hr

/-- WC J3, plan §6.9; DC handler order: recover the actual HEAD tick and input. -/
theorem wc_headInput {i : Nat} {x : V} {s : Slot} {st : State p.n}
    (h : WCDutyInput p c E rho i x (.head s) st) :
    rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)) ∧
      st = clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s) := by
  obtain ⟨t, he, hp | hh | hg | ha⟩ := h.input
  · obtain ⟨r, hr, _⟩ := hp
    cases hr
  · obtain ⟨r, hr, ht, hst⟩ := hh
    cases hr
    exact ⟨ht ▸ he, ht ▸ hst⟩
  · obtain ⟨r, hr, _⟩ := hg
    cases hr
  · obtain ⟨r, hr, _⟩ := ha
    cases hr

/-- WC J3, plan §6.9; DC original receipt: a previous HEAD path has earlier stamps. -/
theorem wc_headRead_stamped {k : Nat} {x : V} {r : Slot} {D : Block}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (h : WCHeadRead p c E rho k x r D) :
    ∀ A, Block.Preceq A D →
      A ∈ (storeAt p c E rho k x).base.blocks ∧
      GridCO.stampBlock (storeAt p c E rho k x).base A < SA.voteTime p.toParams r := by
  intro A hAD
  have hm := h.path A hAD
  rw [clock_base_blocks] at hm
  refine ⟨hm, ?_⟩
  have ht : 0 < SA.voteTime p.toParams r := by
    change 0 < 4 * p.Δ * (r : Time) + p.Δ
    have hd := p.deltaPos
    have hr : (0 : Time) ≤ r := Nat.cast_nonneg r
    nlinarith
  have hkeys : A ∈ (storeAt p c E rho k x).base.blockStamp.map Prod.fst := by
    change A ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp.map Prod.fst
    rw [(metaInv_stateBefore E rho k x).stampKeys]
    exact hm
  have hreceipt := h.receipts.blocks
  rw [(clock_cumulative p _ _).2.2.1] at hreceipt
  unfold GridCO.stampBlock
  cases hf : (storeAt p c E rho k x).base.blockStamp.find? (fun row => row.1 == A) with
  | none =>
    obtain ⟨⟨B, t⟩, hb, he⟩ := List.mem_map.mp hkeys
    dsimp only at he
    subst B
    have hn := List.find?_eq_none.mp hf (A, t) hb
    exact (hn (by simp)).elim
  | some row =>
    simp only [Option.map_some, Option.getD_some]
    have hr := List.mem_of_find?_eq_some hf
    rcases hreceipt row.1 row.2 hr with hg | ⟨j, hj, t, o, _, _, hstamp⟩
    · rw [hg.2]
      exact ht
    · rw [hstamp]
      have hmono := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c)
        E rho hs hnr hj.le x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho k x)] at hmono
      exact hmono.trans_lt (fgsa_preTick_now_lt E rho hs h.event ht)

/-- WC J3, plan §6.9; DC path persistence: keep the original stamp at a later tick. -/
theorem wc_headRead_laterPath {k i : Nat} {x : V} {r : Slot} {D : Block} {t : Time}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (h : WCHeadRead p c E rho k x r D)
    (he : rho.events[i]? = some (.tick x t)) (hlt : SA.voteTime p.toParams r < t) :
    ∀ A, Block.Preceq A D →
      A ∈ (clock p (storeAt p c E rho i x) t).base.blocks ∧
      GridCO.stampBlock (clock p (storeAt p c E rho i x) t).base A <
        SA.voteTime p.toParams r := by
  have hki := V2.D.Engine.eventIndex_lt_of_time_lt hs h.event he hlt
  have hc := fgsa_store_cumulative p c E rho hnr hki.le x
  intro A hAD
  obtain ⟨hm, hstamp⟩ := wc_headRead_stamped hs hnr h A hAD
  have hkey : A ∈ (storeAt p c E rho k x).base.blockStamp.map Prod.fst := by
    change A ∈ (V2.D.Run.stateBefore E rho k x).st.base.blockStamp.map Prod.fst
    rw [(metaInv_stateBefore E rho k x).stampKeys]
    exact hm
  refine ⟨?_, ?_⟩
  · rw [clock_base_blocks]
    exact hc.2.1.subset hm
  · rw [inclusion_stampBlock_of_prefix
      (show (storeAt p c E rho k x).base.blockStamp <+:
        (clock p (storeAt p c E rho i x) t).base.blockStamp by
        rw [(clock_cumulative p _ _).2.2.1]
        exact hc.2.2.1) hkey]
    exact hstamp

/-- WC J3, plan §6.9; DC filtered path: the frame bound admits its height witness. -/
theorem wc_frameMember {st : State p.n} {D : Block}
    (hstore : CStoreInv p st) (hf : WCFrameBelow p st D) (hm : D ∈ st.base.blocks) :
    ∃ Dfg ∈ fullTree p st, eraseFG Dfg = D := by
  obtain ⟨Dfg, he, hlo⟩ := hf.floor
  obtain ⟨B, hB, hBD⟩ := (hstore.baseTree D).mp hm
  have hD : Dfg ∈ st.fg.TF := by
    rwa [eraseFG_injective (hBD.trans he.symm)] at hB
  refine ⟨Dfg, ?_, he⟩
  apply (KitFG.mem_filteredFromView (heightView p) (frameR p st) st.fg.TF Dfg).mpr
  exact ⟨hD, eraseFG_preceq_iff.mp
    (he ▸ block_preceq_trans hf.finalRoot hf.rootBelow),
    eraseFG_preceq_iff.mp (he ▸ hf.rootBelow), Dfg, hD, KitFG.preceq_refl _, hlo⟩

/-- WC J3, plan §6.9; DC proposal path: previous HEAD ancestry precedes proposal time. -/
theorem wc_proposalPath_of_previous {s : Slot} {D : Block}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho) (hs2 : 2 ≤ s)
    {i k : Nat} {x : V} {st : State p.n}
    (hi : WCDutyInput p c E rho i x (.proposal s) st)
    (hh : WCHeadRead p c E rho k x (s - 1) D) (hf : WCFrameBelow p st D) :
    ∃ Dfg ∈ fullTree p st, eraseFG Dfg = D ∧
      ∀ A, Block.Preceq A D → A ∈ st.base.blocks ∧
        GridCO.stampBlock st.base A < SA.proposalTime p.toParams s := by
  obtain ⟨he, rfl⟩ := wc_proposalInput hi
  have hlabel : s - 1 + 1 = s := by simp only [Slot] at hs2 ⊢; omega
  have htime : SA.voteTime p.toParams (s - 1) < SA.proposalTime p.toParams s := by
    rw [← hlabel]
    change 4 * p.Δ * ((s - 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * ((s - 1 + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hp := wc_headRead_laterPath hs hnr hh he htime
  obtain ⟨Dfg, hm, hD⟩ := wc_frameMember
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) _) hf
    (hp D (block_preceq_refl D)).1
  exact ⟨Dfg, hm, hD, fun A hAD => ⟨(hp A hAD).1, (hp A hAD).2.trans htime⟩⟩

/-- WC J3, plan §6.9; DC HEAD path: previous HEAD ancestry is in the pre-freeze arm. -/
theorem wc_headPath_of_previous {s : Slot} {D : Block}
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho) (hs2 : 2 ≤ s)
    {i k : Nat} {x : V} {st : State p.n}
    (hi : WCDutyInput p c E rho i x (.head s) st)
    (hh : WCHeadRead p c E rho k x (s - 1) D) (hf : WCFrameBelow p st D) :
    ∃ Dfg ∈ KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocks p st s),
      eraseFG Dfg = D ∧ ∀ A, Block.Preceq A D → A ∈ st.base.blocks ∧
        GridCO.stampBlock st.base A < SA.freezeTime p.toParams (s - 1) := by
  obtain ⟨he, rfl⟩ := wc_headInput hi
  have hlabel : s - 1 + 1 = s := by simp only [Slot] at hs2 ⊢; omega
  have htime : SA.voteTime p.toParams (s - 1) < SA.voteTime p.toParams s := by
    rw [← hlabel]
    change 4 * p.Δ * ((s - 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * ((s - 1 + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hfreeze : SA.voteTime p.toParams (s - 1) < SA.freezeTime p.toParams (s - 1) := by
    change 4 * p.Δ * ((s - 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * ((s - 1 : Nat) : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have hp := wc_headRead_laterPath hs hnr hh he htime
  obtain ⟨Dfg, hfull, hD⟩ := wc_frameMember
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) _) hf
    (hp D (block_preceq_refl D)).1
  let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hmem : Dfg ∈ voterBlocks p st s := by
    apply Finset.mem_filter.mpr
    refine ⟨(Next.mem_tree p st Dfg).mpr ⟨(Finset.mem_filter.mp hfull).1, ?_⟩, ?_⟩
    · exact ((KitFG.mem_filteredFromView (heightView p) (frameR p st) _ Dfg).mp
        hfull).2.1
    · apply Bool.or_eq_true_iff.mpr
      exact Or.inl (decide_eq_true (hD ▸ (hp D (block_preceq_refl D)).2.trans hfreeze))
  obtain ⟨_, hF, hZ, _⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (frameR p st) _ Dfg).mp hfull
  obtain ⟨D', hD', hlo⟩ := hf.floor
  have hEq : D' = Dfg := eraseFG_injective (hD'.trans hD.symm)
  subst D'
  refine ⟨Dfg, ?_, hD, fun A hAD => ⟨(hp A hAD).1, (hp A hAD).2.trans hfreeze⟩⟩
  exact (KitFG.mem_filteredFromView (heightView p) (frameR p st) _ Dfg).mpr
    ⟨hmem, hF, hZ, Dfg, hmem, KitFG.preceq_refl _, hlo⟩

/-- WC J3, plan §6.9; DC history bound: a completed result read by v_s has label ≤ s−2. -/
theorem wc_history_beforeVote
    {i : Nat} (hiN : i ≤ rho.events.length)
    (s : Slot) (D : Block) (hseedD : Block.Preceq w.QStar D)
    (hmax : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r ≤ s - 2 → Block.Preceq B D)
    (hbefore : ∀ j < i, ∀ e, rho.events[j]? = some e →
      e.time ≤ SA.voteTime p.toParams s) {X : Block}
    (hX : WCBelowHistory p c E rho w iStar i X) : Block.Preceq X D := by
  rcases hX.origin with hX | ⟨j, x, r, B, hB, hXB⟩
  · exact block_preceq_trans hX hseedD
  · have hlabel := wc_gateLabel_beforeVote r s (hbefore j hB.completed _ hB.event)
    have hr : r ≤ s - 2 := by simp only [Slot] at hlabel ⊢; omega
    have hBN : WCResult p c E rho w iStar rho.events.length j x r B :=
      ⟨hB.honest, hB.afterCut, hB.completed.trans_le hiN, hB.label, hB.event, hB.value⟩
    exact block_preceq_trans hXB (hmax j x r B hBN hr)

/-- WC J3, plan §6.9; DC grid separation: proposal and HEAD ticks are off the gate grid. -/
theorem wc_clock_offProposalHead (st : State p.n) (s : Slot) (t : Time)
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) :
    clock p st t = clockPre p st t := by
  have hn : ∀ r, SA.gateTime p.toParams r ≠ t := by
    intro r he
    have hd := p.deltaPos
    rcases ht with rfl | rfl
    · change 4 * p.Δ * (r : Time) + 6 * p.Δ = 4 * p.Δ * (s : Time) at he
      have hz : (4 * (r : Time) + 6 - 4 * (s : Time)) * p.Δ = 0 := by
        linear_combination he
      have hc := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hd)
      simp only [Time] at hc
      omega
    · change 4 * p.Δ * (r : Time) + 6 * p.Δ = 4 * p.Δ * (s : Time) + p.Δ at he
      have hz : (4 * (r : Time) + 5 - 4 * (s : Time)) * p.Δ = 0 := by
        linear_combination he
      have hc := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hd)
      simp only [Time] at hc
      omega
  unfold clock
  rw [ite_eq_right (by
    intro hg
    obtain ⟨r, hr⟩ := (isGateTime_iff p t).mp hg
    exact hn r hr)]

/-- WC J3, plan §6.9; DC comparison read: high sources and live targets precede D. -/
theorem wc_comparisonInputs
    (hs : V2.D.ScheduleWellFormed E rho)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (s : Slot) (D : Block) (hspos : 0 < s) (hseedD : Block.Preceq w.QStar D)
    (hmax : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r ≤ s - 2 → Block.Preceq B D)
    {i : Nat} {x : V} {t : Time} (hiN : i ≤ rho.events.length) (hcut : iStar ≤ i)
    (hx : x ∈ rho.honest) (he : rho.events[i]? = some (.tick x t))
    (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) :
    let st := clock p (storeAt p c E rho i x) t
    WCUsableHighSourcesBelow p c E rho w i x st D ∧
      ∀ row ∈ st.base.obligations, st.base.now < row.2.2 → Block.Preceq row.1 D := by
  intro st
  have htv : t ≤ SA.voteTime p.toParams s := by
    rcases ht with rfl | rfl
    · change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * (s : Time) + p.Δ
      linarith [p.deltaPos]
    · exact le_rfl
  have hbefore : ∀ j < i, ∀ e, rho.events[j]? = some e →
      e.time ≤ SA.voteTime p.toParams s := by
    intro j hj e hjEvent
    by_contra hn
    have hk := V2.D.Engine.eventIndex_lt_of_time_lt hs he hjEvent
      (htv.trans_lt (lt_of_not_ge hn))
    omega
  refine ⟨⟨hx, ?_⟩, ?_⟩
  · intro a _ j y r wire e K hji hrow _ hentry hhigh hsource
    exact wc_highSource_beforeVote hi s D hseedD hmax hiN hji hbefore
      hrow hentry hhigh hsource
  · intro row hrow hlive
    have hrow' : row ∈ (storeAt p c E rho i x).base.obligations := by
      change row ∈ (clock p (storeAt p c E rho i x) t).base.obligations at hrow
      rw [wc_clock_offProposalHead _ s t ht] at hrow
      exact (clockPre_obligations_sublist p _ _).subset hrow
    have htime : 0 < t := by
      rcases ht with rfl | rfl
      · have hd := p.deltaPos
        change 0 < 4 * p.Δ * (s : Time)
        exact mul_pos (mul_pos (by decide) hd) (Nat.cast_pos.mpr hspos)
      · change 0 < 4 * p.Δ * (s : Time) + p.Δ
        have hd := p.deltaPos
        have hcast : (0 : Time) ≤ s := Nat.cast_nonneg s
        nlinarith
    have hnow : (storeAt p c E rho i x).base.now < row.2.2 := by
      have hb := fgsa_preTick_now_lt E rho hs he htime
      have hst : st.base.now = t := (clock_vn _ _).2
      rw [hst] at hlive
      exact hb.trans hlive
    exact wc_history_beforeVote hiN s D hseedD hmax hbefore
      (hi.liveTargets i x row hcut hiN hx hrow' hnow)

/-- WC J3, plan §6.9; DC previous HEAD batch: proposer majority and strict dominance. -/
theorem wc_proposer_prior_of_F_prefix [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head (s - 1))) q) (SA.voteTime p.toParams (s - 1)) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hFD : Block.Preceq (eraseFG st.fg.F) D0)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  intro L hL
  have hstored (o : GridCO.Wire p.n .root) (ho : o ∈ proposerVotes st s) :
      o ∈ (storeAt p c E rho i x).base.votes ∧ GridCO.headLabel? o = some (s - 1) := by
    have h := List.mem_filter.mp ho
    exact ⟨hvotes ▸ h.1, beq_iff_eq.mp h.2⟩
  have hclean : ∀ q ∈ H, GridCO.equivocates (proposerVotes st s) q = false := by
    intro q hq
    obtain ⟨K, t, he, _, _, _, _, _⟩ := hrec q hq
    refine inclusion_no_equivocation _ q
      (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) ?_
    intro o ho hs
    obtain ⟨hm, hl⟩ := hstored o ho
    exact fgsa_honest_head_eq_of_stored E rho hE i x (s - 1) q K.root t ((hH q).mp hq).1 he
      o hm hl hs
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports st.base.blocks (proposerSupport st s) q D0 = true := by
    intro q hq
    obtain ⟨K, t, _, hv, hK, hlookup, hslot, hDK⟩ := hrec q hq
    have hKb := (List.mem_filter.mp (resolvedHead_mem _ _ hK)).1
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head (s - 1)) q, K.root⟩, ?_, rfl, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨hv, beq_self_eq_true _⟩, ?_⟩
      change (match GridCO.resolvedHead? (actView st) _ with
        | some H => Block.preceq (eraseFG st.fg.F) H && decide (H.slot ≤ s - 1)
        | none => false) = true
      rw [hK]
      exact Bool.and_eq_true_iff.mpr ⟨block_preceq_trans hFD hDK, decide_eq_true hslot⟩
    · exact (Gen.AC.Root.vote_support_body _ _ _).mpr ⟨K, hlookup, hKb, hslot, hDK⟩
  have hother := inclusion_rest_bound E rho hC hE (s - 1) H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (proposerVotes st s)
    (fun o ho k hk => ⟨i, x, o, (hstored o ho).1, (hstored o ho).2, hk⟩)
  have hc := Gen.AC.Root.batch_counts st.base.blocks (proposerVotes st s) (proposerVotes st s)
    (proposerSupport st s) H H.card (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) (fun _ h => (List.mem_filter.mp h).1) rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, hrival, _⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  have hDB : Block.compatible D0 B = false := by
    cases h : Block.compatible D0 B with
    | false => rfl
    | true =>
      have hLB := block_compatible_of_preceq_compatible hL h
      change Block.compatible L B = true at hLB
      rw [hB] at hLB
      contradiction
  exact lt_of_le_of_lt (hrival B hDB) (lt_of_lt_of_le hbatch.lt (hprefix L hL).1)

/-- WC J3, plan §6.9; DC previous HEAD batch: voter majority and strict dominance. -/
theorem wc_reader_scores [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    {ih : Nat} {y : V}
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
        (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 → RetainedTargetScores p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1)))
      (r + 1) L ∧ (∀ B, Block.compatible L B = false →
      RetainedWalk.ts p
        (clock p (V2.D.Run.stateBefore E rho ih y).st
          (SA.voteTime p.toParams (r + 1))) (r + 1) B <
        RetainedWalk.ts p
          (clock p (V2.D.Run.stateBefore E rho ih y).st
            (SA.voteTime p.toParams (r + 1))) (r + 1) L) := by
  intro L hL
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))
  have hsub : headSupport p dst (r + 1) ⊆ headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
  have hprov := fgsa_headVotes_provenance E rho hE hN ih y r hih
  have hseat (q : Fin p.n) (hq : q ∈ H) : ∃ K t,
      V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (r + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ r ∧ Block.Preceq D0 K ∧
      ∀ o ∈ headVotes p dst (r + 1), GridCO.headSeat? o = some q →
        o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
    obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrec q hq
    have hpre : ∀ o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r,
        GridCO.headSeat? o = some q →
          o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
      intro o ho hs
      have h := List.mem_filter.mp ho
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K.root t ((hH q).mp hq).1 he
        o h.1 (beq_iff_eq.mp h.2) hs
    refine ⟨K, t, he, hv, hK, hslot, hDK, ?_⟩
    intro o ho hs
    rcases hprov o ho q hs with hm | heq
    · exact hpre o hm hs
    · have hne : GridCO.equivocates
          (GridCO.votesAt (V2.D.Run.stateBefore E rho ih y).st.base r) q = false :=
        inclusion_no_equivocation _ q _ hpre
      rw [hne] at heq
      contradiction
  have hclean : ∀ q ∈ H, GridCO.equivocates (headVotes p dst (r + 1)) q = false := by
    intro q hq
    obtain ⟨K, _, _, _, _, _, _, hu⟩ := hseat q hq
    exact inclusion_no_equivocation _ q _ hu
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (r + 1)) q D0 = true := by
    intro q hq
    obtain ⟨K, _, _, hv, hK, hslot, hDK, _⟩ := hseat q hq
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head r) q, K.root⟩, hv, rfl, ?_⟩
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
        (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)) _ hK rfl,
        hK, hslot, hDK⟩
  have hother := inclusion_rest_bound E rho hC hE r H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.Root.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.Root.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card
    (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) hsub rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, hrival, hnone⟩ := hc
  refine ⟨⟨(hprefix L hL).2, ?_⟩, ?_⟩
  swap
  · intro B hB
    have hDB : Block.compatible D0 B = false := by
      cases he : Block.compatible D0 B with
      | false => rfl
      | true =>
        have hLB := block_compatible_of_preceq_compatible hL he
        change Block.compatible L B = true at hLB
        rw [hB] at hLB
        contradiction
    exact lt_of_le_of_lt (hrival B hDB) (lt_of_lt_of_le hbatch.lt (hprefix L hL).1)
  · intro B hB
    apply hnone B
    intro q hq
    obtain ⟨K, _, _, _, hK, _, hDK, hu⟩ := hseat q hq
    apply Bool.eq_false_iff.mpr
    intro hs
    obtain ⟨o, ho, hk, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ q B).mp hs
    rw [hu o (hsub ho) hk] at hvote
    have hlookup := resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
      (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _))
      (baseVote ⟨.seat (.head r) q, K.root⟩) hK rfl
    rw [Gen.AC.Root.voteSupports_def, hlookup] at hvote
    change (_ && _ && Block.preceq B K) = true at hvote
    have hBK : Block.Preceq B K := (Bool.and_eq_true_iff.mp hvote).2
    have hLB := block_compatible_of_common (block_preceq_trans hL hDK) hBK
    change Block.compatible L B = true at hLB
    rw [hB] at hLB
    contradiction

variable [Fintype V]

/-- WC J3, plan §6.9; DC strict receipt relay: the previous honest HEAD batch is stored.
The receiving F bound is taken at the later duty and transported to its early tick. -/
theorem wc_previousReceipts
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho) (hmono : RMono p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (q : Slot) (D : Block)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams (q + 1))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (q + 1))).card)
    (hhor : SA.voteTime p.toParams (q + 2) ≤ rho.horizon)
    (hprev : ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y (q + 1) D)
    {i : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x t))
    (ht : t = SA.proposalTime p.toParams (q + 2) ∨ t = SA.voteTime p.toParams (q + 2))
    (hF : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) D) :
    let st := clock p (storeAt p c E rho i x) t
    ∃ H : Finset (Fin p.n),
      (∀ w, w ∈ H ↔ rho.seatOf (.base (.head (q + 1))) w ∈ rho.honest ∧
        E.awake (rho.seatOf (.base (.head (q + 1))) w)
          (SA.voteTime p.toParams (q + 1)) = true) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card ∧
      ∀ w ∈ H, ∃ K,
        rho.emits E (rho.seatOf (.base (.head (q + 1))) w)
          (ofHead p ⟨.seat (.head (q + 1)) w, K.root⟩)
          (SA.voteTime p.toParams (q + 1)) ∧
        baseVote (⟨.seat (.head (q + 1)) w, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
        K ∈ st.base.blocks ∧ K.slot ≤ q + 1 ∧ Block.Preceq D K ∧
        GridCO.stampVote st.base (baseVote ⟨.seat (.head (q + 1)) w, K.root⟩) <
          SA.freezeTime p.toParams (q + 1) ∧
        GridCO.stampBlock st.base K < SA.freezeTime p.toParams (q + 1) := by
  intro st
  have hs := hvalid.toScheduleWellFormed
  have hd := p.deltaPos
  have het : SA.earlyTime p.toParams (q + 1) < t := by
    rcases ht with rfl | rfl
    · change 4 * p.Δ * ((q + 1 : Nat) : Time) + 2 * p.Δ <
        4 * p.Δ * ((q + 2 : Nat) : Time)
      push_cast
      nlinarith
    · change 4 * p.Δ * ((q + 1 : Nat) : Time) + 2 * p.Δ <
        4 * p.Δ * ((q + 2 : Nat) : Time) + p.Δ
      push_cast
      nlinarith
  have hbefore : SA.earlyTime p.toParams (q + 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    change 4 * p.Δ * ((q + 1 : Nat) : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((q + 2 : Nat) : Time) + p.Δ
    push_cast
    nlinarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.voteTime p.toParams (q + 1)) (SA.earlyTime p.toParams (q + 1)) hsync
    (fgsaDelay_nonrow E.Δ ΔF) hGST (by
      rw [hdelta]
      change 4 * p.Δ * ((q + 1 : Nat) : Time) + p.Δ + p.Δ ≤
        4 * p.Δ * ((q + 1 : Nat) : Time) + 2 * p.Δ
      exact le_of_eq (by ring)) hbefore
  have heq : ((4 * (q + 1) + 2 : Nat) : Time) * p.Δ =
      SA.earlyTime p.toParams (q + 1) := by
    change ((4 * (q + 1) + 2 : Nat) : Time) * p.Δ =
      4 * p.Δ * ((q + 1 : Nat) : Time) + 2 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hdelta x hx (4 * (q + 1) + 2)
    (heq ▸ hbefore)
  rw [heq] at hj
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hs hj he het
  have hFj := eraseFG_preceq ((hmono hnr j i x hx hji.le).1)
  obtain ⟨H, hH, hbatch⟩ := inclusion_head_seats E rho hcstar (q + 1) ⟨hpart⟩
  refine ⟨H, hH, hbatch, ?_⟩
  intro w hw
  obtain ⟨hy, haw⟩ := (hH w).mp hw
  obtain ⟨k, hk⟩ := hprev _ hy
  let K := headAtIdx p c E rho k (q + 1)
  have hhead : headVote p (clock p (storeAt p c E rho k
      (rho.seatOf (.base (.head (q + 1))) w)) (SA.voteTime p.toParams (q + 1)))
      (q + 1) = K := by
    dsimp only [K, headAtIdx]
    rw [hk.event]
    rfl
  obtain ⟨hem, hv, hvs, hK, hbs, hslot⟩ := inclusion_head_receipt_early E rho hvalid hnr
    hdelta hcstar (q + 1) hSync hj w hy haw hk.event K hhead
    (block_preceq_trans hFj (block_preceq_trans hF hk.covers)) hroots
  have hkeep := inclusion_stamps_kept E rho hnr hji.le x _ K hv hK
  have hkv : baseVote (⟨.seat (.head (q + 1)) w, K.root⟩ : HeadWire p.n) ∈
      st.base.votes := by rw [(clock_vn _ _).1]; exact hkeep.1
  have hkb : K ∈ st.base.blocks := by rw [clock_base_blocks]; exact hkeep.2.1
  have hkeyV := hkeep.1
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at hkeyV
  rw [← fgsa_vote_stamp_keys E rho i x] at hkeyV
  have hkeyB := hkeep.2.1
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks at hkeyB
  rw [← (metaInv_stateBefore E rho i x).stampKeys] at hkeyB
  change _ ∈ (storeAt p c E rho i x).base.voteStamp.map Prod.fst at hkeyV
  change _ ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst at hkeyB
  have hf : SA.earlyTime p.toParams (q + 1) < SA.freezeTime p.toParams (q + 1) := by
    change 4 * p.Δ * ((q + 1 : Nat) : Time) + 2 * p.Δ <
      4 * p.Δ * ((q + 1 : Nat) : Time) + 3 * p.Δ
    nlinarith
  refine ⟨K, hem, hkv, hkb, hslot, hk.covers, ?_, ?_⟩
  · have hpV : (storeAt p c E rho i x).base.voteStamp <+: st.base.voteStamp := by
      dsimp only [st]
      rw [(clock_cumulative p _ _).2.2.2.1]
    rw [inclusion_stampVote_of_prefix hpV hkeyV, hkeep.2.2.1]
    exact hvs.trans hf
  · have hpB : (storeAt p c E rho i x).base.blockStamp <+: st.base.blockStamp := by
      dsimp only [st]
      rw [(clock_cumulative p _ _).2.2.1]
    rw [inclusion_stampBlock_of_prefix hpB hkeyB, hkeep.2.2.2]
    exact hbs.trans hf

omit [Fintype V] in
/-- WC J3, plan §6.9; DC frame join: use the reviewed live-frame conclusion.
The caller discharges its separate [L] telescope before this local construction. -/
private theorem wc_comparisonFrame
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
  have hcut : iStar ≤ i := hseed.cut ▸ wc_cut_le_laterTick hs he hcutTime
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

/-- WC J3, plan §6.9; DC proposer pools: resolve every previous honest HEAD above D. -/
theorem wc_proposalCounts
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho) (hmono : RMono p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (q : Slot) (D : Block)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams (q + 1))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (q + 1))).card)
    (hhor : SA.voteTime p.toParams (q + 2) ≤ rho.horizon)
    (hprev : ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y (q + 1) D)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams (q + 2))))
    (hf : WCFrameBelow p (clock p (storeAt p c E rho i x)
      (SA.proposalTime p.toParams (q + 2))) D) :
    let st := clock p (storeAt p c E rho i x) (SA.proposalTime p.toParams (q + 2))
    ∀ L, Block.Preceq L D →
      GridCO.voterCount (proposerVotes st (q + 2)) < 2 * RetainedWalk.ss st (q + 2) L ∧
      ∀ B, Block.compatible L B = false →
        RetainedWalk.ss st (q + 2) B < RetainedWalk.ss st (q + 2) L := by
  intro st
  have hF : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) D := by
    have h := block_preceq_trans hf.finalRoot hf.rootBelow
    simpa only [clock_fg] using h
  obtain ⟨H, hH, hbatch, hrec⟩ := wc_previousReceipts hvalid hnr hdelta hcstar hroots
    hmono ΔF hsync q D hGST hpart hhor hprev hx he (Or.inl rfl) hF
  have hlabel : q + 2 - 1 = q + 1 := by simp only [Slot]; omega
  have hseatEq (w : Fin p.n) : rho.seatOf (.base (.head (q + 2 - 1))) w =
      rho.seatOf (.base (.head (q + 1))) w :=
    congrArg (fun r : Slot => rho.seatOf (.base (.head r)) w) hlabel
  apply wc_proposer_prior_of_F_prefix E rho hvalid hcstar (q + 2) i x st (clock_vn _ _).1 H
    (by simpa only [hlabel, hseatEq] using hH) hbatch D
    (block_preceq_trans hf.finalRoot hf.rootBelow)
  intro w hw
  obtain ⟨K, hem, hv, hK, hslot, hDK, _, _⟩ := hrec w hw
  have hInv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x)
    (SA.proposalTime p.toParams (q + 2))
  have hactive : K ∈ (actView st).blocks := (actView_blocks st K).mpr
    ⟨hK, block_compatible_of_common (block_preceq_refl K)
      (block_preceq_trans (block_preceq_trans hf.finalRoot hf.rootBelow) hDK)⟩
  have hdomain : st.base.headDomain = none :=
    base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho i x))
  simpa only [hlabel, hseatEq] using
    (show ∃ K t, rho.emits E (rho.seatOf (.base (.head (q + 1))) w)
        (ofHead p ⟨.seat (.head (q + 1)) w, K.root⟩) t ∧
      baseVote (⟨.seat (.head (q + 1)) w, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (q + 1)) w, K.root⟩) =
        some K ∧ Gen.AC.Root.resolvedTarget? st.base.blocks
          (baseVote ⟨.seat (.head (q + 1)) w, K.root⟩) = some K ∧
      K.slot ≤ q + 1 ∧ Block.Preceq D K from
      ⟨K, _, hem, hv, actView_resolve_target p st hInv hdomain _ hactive rfl,
        resolvedTarget_of_mem _ (baseBlocks_rootInj p st hInv) _ hK rfl, hslot, hDK⟩)

/-- WC J3, plan §6.9; DC voter pools: retain previous honest support in the frozen arm. -/
theorem wc_headCounts
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho) (hmono : RMono p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (q : Slot) (D : Block)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams (q + 1))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (q + 1))).card)
    (hhor : SA.voteTime p.toParams (q + 2) ≤ rho.horizon)
    (hprev : ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y (q + 1) D)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (q + 2))))
    (hf : WCFrameBelow p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams (q + 2))) D) :
    let st := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (q + 2))
    ∀ L, Block.Preceq L D → RetainedTargetScores p st (q + 2) L ∧
      ∀ B, Block.compatible L B = false →
        RetainedWalk.ts p st (q + 2) B < RetainedWalk.ts p st (q + 2) L := by
  intro st
  have hF : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) D := by
    have h := block_preceq_trans hf.finalRoot hf.rootBelow
    simpa only [clock_fg] using h
  obtain ⟨H, hH, hbatch, hrec⟩ := wc_previousReceipts hvalid hnr hdelta hcstar hroots
    hmono ΔF hsync q D hGST hpart hhor hprev hx he (Or.inr rfl) hF
  apply wc_reader_scores E rho hvalid hnr hcstar (q + 1) he H hH hbatch D
  intro w hw
  obtain ⟨K, hem, hv, hK, hslot, hDK, hvs, hbs⟩ := hrec w hw
  have hInv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x)
    (SA.voteTime p.toParams (q + 2))
  have hactive : K ∈ (actView st).blocks := (actView_blocks st K).mpr
    ⟨hK, block_compatible_of_common (block_preceq_refl K)
      (block_preceq_trans (block_preceq_trans hf.finalRoot hf.rootBelow) hDK)⟩
  have hdomain : st.base.headDomain = none :=
    base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho i x))
  refine ⟨K, _, hem, ?_, hK, hslot, hDK⟩
  unfold headSupport
  dsimp only
  rw [List.mem_eraseDups]
  apply List.mem_append_left
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨hv, beq_self_eq_true _⟩, ?_⟩
  have hres := actView_resolve_target p st hInv hdomain
    (baseVote ⟨.seat (.head (q + 1)) w, K.root⟩) hactive rfl
  change GridCO.resolvedBefore (actView st)
    (baseVote ⟨.seat (.head (q + 1)) w, K.root⟩) (SA.freezeTime p.toParams (q + 1)) = true
  unfold GridCO.resolvedBefore
  rw [hres]
  change (decide (K.slot ≤ q + 1) &&
    decide (GridCO.stampVote st.base _ < SA.freezeTime p.toParams (q + 1)) &&
    decide (GridCO.stampBlock st.base K < SA.freezeTime p.toParams (q + 1))) = true
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hslot, decide_eq_true hvs⟩, decide_eq_true hbs⟩

omit [Fintype V] in
/-- WC J3, plan §6.9; DC retained path: D witnesses height in the canonical duty view. -/
theorem wc_treeFrameAncestry {st : State p.n} {D : Block} {Dfg : FGBlock (Fin p.n)}
    (hstore : CStoreInv p st) (hf : WCFrameBelow p st D) (hD : eraseFG Dfg = D)
    (view : Finset (FGBlock (Fin p.n))) (hsub : view ⊆ st.fg.TF) (hm : Dfg ∈ view)
    (hclosed : ∀ A, FGBlock.Preceq st.fg.F A → FGBlock.Preceq A Dfg → A ∈ view) :
    ∀ A, Block.Prec (liveRoot p st) A → Block.Preceq A D →
      A ∈ erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg view) := by
  intro A hLA hAD
  obtain ⟨Afg, hA, he⟩ := eraseFG_ancestor_mem hstore.fg.closed (hsub hm) (hD ▸ hAD)
  have hZ : Block.Preceq (eraseFG (frameR p st).Z) A :=
    block_preceq_trans (fgsa_Z_preceq_liveRoot p st) (Bool.and_eq_true_iff.mp hLA).2
  obtain ⟨Bfg, hB, hlo⟩ := hf.floor
  have hBD : Bfg = Dfg := eraseFG_injective (hB.trans hD.symm)
  subst Bfg
  have hAf : FGBlock.Preceq Afg Dfg := eraseFG_preceq_iff.mp (he ▸ hD ▸ hAD)
  have hFA : FGBlock.Preceq st.fg.F Afg :=
    eraseFG_preceq_iff.mp (he ▸ block_preceq_trans hf.finalRoot hZ)
  apply List.mem_filter.mpr
  refine ⟨(hstore.baseTree A).mpr ⟨Afg, hA, he⟩, decide_eq_true ⟨Afg, ?_, he⟩⟩
  exact (KitFG.mem_filteredFromView (heightView p) (frameR p st) view Afg).mpr
    ⟨hclosed Afg hFA hAf, hFA,
      eraseFG_preceq_iff.mp (he ▸ hZ), Dfg, hm, hAf, hlo⟩

/-- WC J3, plan §6.9; DC first eligible proposal: join the finite pivot, paths and walks.
The only lane producer premise is the reviewed live-frame Statement. -/
theorem wc_proposalPivot (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframeLive : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCProposalPivotStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed hinv pt hstart hprop hgate
  have hs := hvalid.toScheduleWellFormed
  have hi := hinv rho.events.length ⟨hseed.within, le_rfl⟩
  have hfl := hframeLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault
    hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc
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
    exact wc_comparisonFrame hs hseed hi hfl pt.s D hstart hQD hmax hprev hnr hduty
      hprop.1.2 he hst (Or.inl rfl) st.fg.TF
      ⟨Or.inr ⟨⟨pt.s, Or.inl rfl⟩, rfl⟩⟩ (fun _ h => h)
  have hFH : ∀ i x st, x ∈ rho.honest → WCDutyInput p c E rho i x (.head pt.s) st →
      WCFrameBelow p st D ∧ Block.Preceq (liveRoot p st) D := by
    intro i x st hx hduty
    obtain ⟨he, hst⟩ := wc_headInput hduty
    exact wc_comparisonFrame hs hseed hi hfl pt.s D hstart hQD hmax hprev hnr hduty
      hx he hst (Or.inr rfl) (voterBlocks p st pt.s) ⟨Or.inl ⟨pt.s, rfl, rfl⟩⟩
      (fun _ h => Next.tree_subset_TF p st (Finset.mem_filter.mp h).1)
  have hPP : ∀ i x st, WCDutyInput p c E rho i x (.proposal pt.s) st →
      x = V2.D.proposerOf rho (fgsaInterface p c) pt.s →
      ∃ Dfg ∈ fullTree p st, eraseFG Dfg = D ∧
        ∀ A, Block.Preceq A D → A ∈ st.base.blocks ∧
          GridCO.stampBlock st.base A < SA.proposalTime p.toParams pt.s := by
    intro i x st hduty hx
    obtain ⟨k, hk⟩ := hprev x (hx ▸ hprop.1.2)
    exact wc_proposalPath_of_previous hs hnr hs2 hduty hk (hFP i x st hduty hx).1
  have hHP : ∀ i x st, x ∈ rho.honest → WCDutyInput p c E rho i x (.head pt.s) st →
      ∃ Dfg ∈ KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocks p st pt.s),
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
      have hclosed : ∀ A, FGBlock.Preceq st.fg.F A → FGBlock.Preceq A Dfg →
          A ∈ voterBlocks p st pt.s := by
        intro A hFA hAD
        obtain ⟨B, hB, hBA⟩ := eraseFG_ancestor_mem hInv.fg.closed
          (Next.tree_subset_TF p st
            (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1) (eraseFG_preceq hAD)
        have hA : A ∈ st.fg.TF := (eraseFG_injective hBA) ▸ hB
        exact Finset.mem_filter.mpr ⟨(Next.mem_tree p st A).mpr ⟨hA, hFA⟩,
          Bool.or_eq_true_iff.mpr (Or.inl
          (decide_eq_true (hpath (eraseFG A) (hD ▸ eraseFG_preceq hAD)).2))⟩
      have hw := fgsa_headInTree_covers_of_transfer p st _ _ _ D
        (block_compatible_of_common hlive (block_preceq_refl D))
        (wc_treeFrameAncestry hInv hf hD (voterBlocks p st pt.s)
          (fun _ h => Next.tree_subset_TF p st (Finset.mem_filter.mp h).1)
          (Finset.mem_filter.mp hm).1 hclosed)
        (hcountsS D (block_preceq_refl D)).1.majority
        (hcountsS D (block_preceq_refl D)).2
      have hsne : pt.s ≠ 0 := by simp only [Slot] at hs2 ⊢; omega
      have hread : headVote p st pt.s = H := hH
      change (if pt.s = 0 then .genesis else headInTree p st
        (erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocks p st pt.s)))
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
    (wc_treeFrameAncestry hInv hfs hD src.fg.TF (fun _ h => h)
      (Finset.mem_filter.mp hDsrc).1 (fun A _ hAD => hclosed A hAD))
    (hcountsS D (block_preceq_refl D)).1 (hcountsS D (block_preceq_refl D)).2
  have hem' := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hem'
  have hp := (fgsa_emits_proposal E rho _ _ _ pt.s _).mp hem'
  have hparent := (fgsa_walkRun_proposal_parent p src pt.s _ N hp.2.2.2).2.2
  have hDP : Block.Preceq D pt.P.parent := by rw [← hN, hparent]; exact hwalk
  exact ⟨D, hmember, hQD, hmax, hFP, hFH, hprev, hPP, hHP, hheadWalk, hDP⟩

end AvailableChain.FGSA.Run
end
