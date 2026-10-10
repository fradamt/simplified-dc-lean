module
public import AvailableChainFGSAProofs.Proofs.Healing.Phase
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1003–1012, 1193–1209; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL no effective event fixes the frontier and both evidence bits.
A bit can be true later only if it is true at the first prefix. -/
theorem healing_phase_window (hnr : V2.D.NoRestart rho) {i m : Nat} {v : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hquiet : ∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) :
    ∀ k, i + 1 ≤ k → k ≤ timeIdx rho v →
      frontierAtIdx p c E rho k = m ∧
      (TopEvidence p c E rho k m → TopEvidence p c E rho (i + 1) m) ∧
      (ContestEvidence p c E rho k m → ContestEvidence p c E rho (i + 1) m) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨hfront, id, id⟩
  | succ k hk ih =>
    intro hkv
    obtain ⟨hf, ht, hc⟩ := ih (by omega)
    have hq := hquiet k (by omega) (by omega)
    have hmono := healing_frontier_mono p c E rho hnr (Nat.le_add_right k 1)
    have hf' : frontierAtIdx p c E rho (k + 1) = m := by
      by_contra hne
      exact hq (Or.inl (by omega))
    refine ⟨hf', fun h => ht ?_, fun h => hc ?_⟩
    · by_contra hn
      exact hq (Or.inr (show (¬ TopEvidence p c E rho k (frontierAtIdx p c E rho (k + 1)) ∧
        TopEvidence p c E rho (k + 1) (frontierAtIdx p c E rho (k + 1))) ∨ _ from
        Or.inl (by rw [hf']; exact ⟨hn, h⟩)))
    · by_contra hn
      exact hq (Or.inr (show _ ∨
        (¬ ContestEvidence p c E rho k (frontierAtIdx p c E rho (k + 1)) ∧
        ContestEvidence p c E rho (k + 1) (frontierAtIdx p c E rho (k + 1))) from
        Or.inr (by rw [hf']; exact ⟨hn, h⟩)))

/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL a held top carrier fixes the local top J below the frontier cap.
Assembly supplies RXing. A J on the carrier path is the carrier's J.
At m = 1 both J are genesis (B21). -/
theorem healing_phase_top_node (crossing : RXing p c E rho) {k m : Nat} {y : V}
    {C : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hC : C ∈ (storeAt p c E rho k y).fg.TF) (hh : (heightView p C).h = m)
    (hj : (heightView p C).h_j + 1 = m) (hcap : frontierAtIdx p c E rho k ≤ m) :
    (storeAt p c E rho k y).fg.h_max = m ∧ (storeAt p c E rho k y).fg.h_j + 1 = m ∧
      (FGBlock.Preceq (storeAt p c E rho k y).fg.J C →
        (storeAt p c E rho k y).fg.J = (heightView p C).J) := by
  have hs : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho k y).fg := (storeBundle_stateBefore E rho k y).cstore.fg
  have hmax : (storeAt p c E rho k y).fg.h_max = m := le_antisymm
    ((healing_phase_local_le_frontier p c E rho hy).trans hcap)
    (hh ▸ healing_phase_height_le p c E rho hC)
  have hlt := healing_phase_justified_lt p c E rho k y
  have hJC : FGBlock.Preceq (heightView p C).J C :=
    KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry C)
      ((fgCertificateLaws p).height.entry_preceq C)
  obtain ⟨K, hK, hKF⟩ := hs.Fcar
  have hFK := healing_phase_finality_le p c E rho hK hKF
  have hlo : m - 1 ≤ (storeAt p c E rho k y).fg.h_j := by
    by_cases hF : m - 1 ≤ (finalityView p K).h_F
    · (simp only [Height] at *; omega)
    · have hjne : (heightView p C).h_j ≠ 0 := by (simp only [Height] at *; omega)
      have hJh := (fgJustificationLaws p).J_height C hjne
      have hJmem := KitFG.ancestor_closed_of_parent_closed _ hs.closed C hC _ hJC
      have hFJ := crossing k k y y K _ hy le_rfl hK hKF ⟨hy, hJmem⟩
        (by (simp only [Height] at *; omega))
      have hkey := KitFG.fst_le_of_lexKey_le (hs.pair.2 C hC hFJ)
      (simp only [Height] at *; omega)
  refine ⟨hmax, by (simp only [Height] at *; omega), ?_⟩
  intro hJ
  obtain ⟨D, _, _, hjD, hJD⟩ := hs.pair.1
  rw [hJD]
  apply healing_phase_entries_eq p (W := C)
  · (simp only [Height] at *; omega)
  · exact hJD ▸ hJ
  · exact hJC

/-- Blueprint 21:1012–1045; plan S20, H-PHASE r2/P3.
DC: SAME the settled frame reads only the FG store. -/
private theorem settle_frame_fg {st st' : State p.n} (h : st.fg = st'.fg)
    {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hf : SettledPhaseFrame p st m J contested) : SettledPhaseFrame p st' m J contested := by
  unfold SettledPhaseFrame FGSA.controls at *
  rw [← h]
  exact hf

/-- Blueprint 21:1003–1012, 1155–1163; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL common live controls from Δ after the event give the interval
from the strict cut at 3Δ (B25) and every frozen HEAD frame.
Assembly supplies RXing. -/
private theorem settle_finish (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) {ev : V2.Event V (Obj p)}
    {v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon) (hm : 1 ≤ m)
    (hcore : ∀ k y, V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k → k ≤ timeIdx rho v →
      y ∈ rho.honest →
      (R_at p c E rho k y).H = m ∧ (R_at p c E rho k y).contest = contested ∧
      (match J with
        | some B => (R_at p c E rho k y).rootIsJ = true ∧ (R_at p c E rho k y).J = B
        | none => (R_at p c E rho k y).rootIsJ = false)) :
    PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m J contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st m J contested) := by
  have hs := hvalid.toScheduleWellFormed
  have hpos := p.deltaPos
  have hd3 : ev.time + p.Δ ≤ ev.time + 3 * p.Δ := by
    simp only [Time] at *
    omega
  refine ⟨⟨by simp only [Time] at *; omega, hv, hm, ?_⟩, ?_⟩
  · intro k x hk hkv hx
    exact hcore k x ((healing_phase_idxBefore_mono p c rho hd3).trans hk) hkv hx
  · intro y s nd hy hvote hvs hpost
    rw [postClock_def, preTick_def] at hpost
    cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
    | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
    | some k =>
      rw [hk] at hpost
      have hnd := Option.some.inj hpost
      subst nd
      have htick := V2.D.Run.tickIdx?_spec hk
      have hjk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k := by
        by_contra hn
        have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick (ev.time + p.Δ)).mp (by omega)
        change SA.voteTime p.toParams s < ev.time + p.Δ at hlt
        simp only [Time] at *
        omega
      have hkv : k ≤ timeIdx rho v :=
        (healing_phase_lt_timeIdx p c E rho hs htick (t := v) hvs).le
      obtain ⟨hH, hc, hr⟩ := hcore k y hjk hkv hy
      have hf := healing_phase_frame p c E rho crossing hy hm hH hc hr
      exact settle_frame_fg p (clock_fg p _ _).symm hf

/-- ROOT-DIGEST W2b. Blueprint 21:1003–1045, 1142–1209; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL settlement after a start event, with live controls,
one common top J, and frozen HEAD frames. Evidence can be present at the start.
The effective-event corollary gives the third frozen RPhase clause.
Its two matches list all three kinds, where the frozen text uses a
wildcard; they agree for each kind. Assembly supplies RXing. The top-J
identity uses the global absence of contest evidence, so no fault bound is an
input. Carriers accepted before GST are relayed by GST + Δ. -/
theorem healing_settle_start (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hAwake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ i ev v m kind, rho.events[i]? = some ev →
      E.t_GST ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
          SA.voteTime p.toParams s ≤ v →
          postClock E rho y (SA.voteTime p.toParams s) = some nd →
          SettledPhaseFrame p nd.st m root contested) := by
  intro i (ev : V2.Event V (Obj p)) v m kind hi hgst hu hv hm hfront hkind hquiet
  -- Restate the event times at the object type of the relay lemmas.
  have hu : ev.time + 3 * p.Δ ≤ v := hu
  have hgst : E.t_GST ≤ ev.time := hgst
  have hs := hvalid.toScheduleWellFormed
  have hpos := p.deltaPos
  have hij0 : i < V2.D.Run.idxBefore rho (ev.time + p.Δ) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (lt_add_of_pos_right _ hpos)
  have hdv : ev.time + p.Δ ≤ v := by
    simp only [Time] at *
    omega
  have hj0v : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ timeIdx rho v :=
    healing_phase_idx_le_time p c rho hdv
  have hhor : ev.time + p.Δ ≤ rho.horizon := hdv.trans hv
  have hwin := healing_phase_window p c E rho hnr hfront hquiet
  have hcap (k : Nat) (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k)
      (hkv : k ≤ timeIdx rho v) :
      frontierAtIdx p c E rho k = m := (hwin k (by omega) hkv).1
  -- Every carrier held at i + 1 is held by every honest node in the window.
  have relay {x : V} {W : FGBlock (Fin p.n)} (hW : HeldAt p c E rho (i + 1) x W)
      (hh : (heightView p W).h = m) {k : Nat} {y : V}
      (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k) (hy : y ∈ rho.honest) :
      W ∈ (storeAt p c E rho k y).fg.TF := by
    have h0 := healing_phase_held_receipt (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync hi
      hW.1 hgst hW.2 hhor ((hcap _ le_rfl hj0v).trans hh.symm).le hy
      (hAwake y hy _ (hgst.trans (le_add_of_nonneg_right p.deltaPos.le)) hhor)
    exact (fgsa_store_cumulative p c E rho hnr hk y).1 h0
  have hH {x : V} {W : FGBlock (Fin p.n)} (hW : HeldAt p c E rho (i + 1) x W)
      (hh : (heightView p W).h = m) {k : Nat} {y : V}
      (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k) (hkv : k ≤ timeIdx rho v)
      (hy : y ∈ rho.honest) : (R_at p c E rho k y).H = m :=
    le_antisymm ((healing_phase_local_le_frontier p c E rho hy).trans_eq (hcap k hk hkv))
      (hh ▸ healing_phase_height_le p c E rho (relay hW hh hk hy))
  have wit := healing_phaseWitness p c E rho hm hfront
  cases kind with
  | gap =>
    obtain ⟨hnt, _⟩ := hkind
    obtain ⟨x, W, hW, hh⟩ := wit.frontier
    refine ⟨.genesis, settle_finish p c E rho crossing hvalid hu hv hm ?_⟩
    intro k y hk hkv hy
    have hHk := hH hW hh hk hkv hy
    have hnj : (storeAt p c E rho k y).fg.h_j + 1 ≠ m :=
      fun ht => hnt ((hwin k (by omega) hkv).2.1 ⟨y, hy, ht⟩)
    change (storeAt p c E rho k y).fg.h_max = m at hHk
    have hc : (R_at p c E rho k y).contest = false := by
      change (decide ((storeAt p c E rho k y).fg.h_max =
        (storeAt p c E rho k y).fg.h_j + 1) && _) = false
      rw [hHk]
      simp only [Ne.symm hnj, decide_false, Bool.false_and]
    refine ⟨hHk, hc, ?_⟩
    change (decide ((R_at p c E rho k y).H = (R_at p c E rho k y).j + 1) &&
      !(R_at p c E rho k y).contest) = false
    change (decide ((storeAt p c E rho k y).fg.h_max =
      (storeAt p c E rho k y).fg.h_j + 1) && _) = false
    rw [hHk]
    simp only [Ne.symm hnj, decide_false, Bool.false_and]
  | topJ =>
    obtain ⟨ht, hnc⟩ := hkind
    obtain ⟨x, C, hC, hh, hj, _⟩ := wit.top ht
    refine ⟨(heightView p C).J, settle_finish p c E rho crossing hvalid hu hv hm ?_⟩
    intro k y hk hkv hy
    have hCk := relay hC hh hk hy
    obtain ⟨hmax, htop, hJ⟩ := healing_phase_top_node p c E rho crossing hy hCk hh hj
      (hcap k hk hkv).le
    have hc : (R_at p c E rho k y).contest = false := by
      cases he : (R_at p c E rho k y).contest with
      | false => rfl
      | true => exact (hnc ((hwin k (by omega) hkv).2.2 ⟨y, hy, hmax, he⟩)).elim
    have hc' := hc
    change (decide ((storeAt p c E rho k y).fg.h_max =
      (storeAt p c E rho k y).fg.h_j + 1) && decide (∃ W ∈ (storeAt p c E rho k y).fg.TF,
        FGBlock.Preceq (storeAt p c E rho k y).fg.F W ∧
        (heightView p W).h = (storeAt p c E rho k y).fg.h_max ∧
        ¬ FGBlock.Preceq (storeAt p c E rho k y).fg.J W)) = false at hc'
    have hJC : FGBlock.Preceq (storeAt p c E rho k y).fg.J C := by
      by_contra hn
      rcases Bool.and_eq_false_iff.mp hc' with h | h
      · exact of_decide_eq_false h (hmax.trans htop.symm)
      · exact of_decide_eq_false h ⟨C, hCk,
          (healing_phase_frontier_root p c E rho crossing hy hCk
            (hh.trans hmax.symm)).1, hh.trans hmax.symm, hn⟩
    refine ⟨hmax, hc, ?_, hJ hJC⟩
    change (decide ((storeAt p c E rho k y).fg.h_max =
      (storeAt p c E rho k y).fg.h_j + 1) && !(R_at p c E rho k y).contest) = true
    rw [hc, hmax, htop]
    simp only [decide_true, Bool.not_false, Bool.and_self]
  | contest =>
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff⟩ := wit.contest hkind
    refine ⟨.genesis, settle_finish p c E rho crossing hvalid hu hv hm ?_⟩
    intro k y hk hkv hy
    have hCk := relay hC hhC hk hy
    have hWk := relay hW hhW hk hy
    obtain ⟨hmax, htop, hJ⟩ := healing_phase_top_node p c E rho crossing hy hCk hhC hj
      (hcap k hk hkv).le
    have hc : (R_at p c E rho k y).contest = true := by
      change (decide ((storeAt p c E rho k y).fg.h_max =
        (storeAt p c E rho k y).fg.h_j + 1) && decide (∃ W ∈ (storeAt p c E rho k y).fg.TF,
          FGBlock.Preceq (storeAt p c E rho k y).fg.F W ∧
          (heightView p W).h = (storeAt p c E rho k y).fg.h_max ∧
          ¬ FGBlock.Preceq (storeAt p c E rho k y).fg.J W)) = true
      refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hmax.trans htop.symm),
        decide_eq_true ?_⟩
      by_cases hJC : FGBlock.Preceq (storeAt p c E rho k y).fg.J C
      · exact ⟨W, hWk,
          (healing_phase_frontier_root p c E rho crossing hy hWk
            (hhW.trans hmax.symm)).1, hhW.trans hmax.symm,
          by rw [hJ hJC]; exact hoff⟩
      · exact ⟨C, hCk,
          (healing_phase_frontier_root p c E rho crossing hy hCk
            (hhC.trans hmax.symm)).1, hhC.trans hmax.symm, hJC⟩
    refine ⟨hmax, hc, ?_⟩
    change (decide ((R_at p c E rho k y).H = (R_at p c E rho k y).j + 1) &&
      !(R_at p c E rho k y).contest) = false
    rw [hc]
    simp only [Bool.not_true, Bool.and_false]

/-- ROOT-DIGEST W2b. The frozen effective-event statement follows from start settlement. -/
theorem healing_settle_event (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hAwake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ i ev v m kind, rho.events[i]? = some ev → EffectiveEvent p c E rho i →
      E.t_GST ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
          SA.voteTime p.toParams s ≤ v →
          postClock E rho y (SA.voteTime p.toParams s) = some nd →
          SettledPhaseFrame p nd.st m root contested) := by
  exact fun i ev v m kind hi _heff =>
    healing_settle_start (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync hAwake i ev v m kind hi

/-- ROOT-DIGEST W2b. Blueprint 21:1086–1278; plan S20, H-PHASE r2/P6.
DC: INTENTIONAL the five frozen RPhase clauses from P1–P5.
Assembly supplies RMono and RXing. The other inputs are Base₂ and Recovery₂
fields. No phase, service, fault-bound, or reset premise is an input. -/
theorem healing_rPhase (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hAwake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    RPhase p c E rho := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b m hab hb hm hfixed
    exact healing_phase_order_of_crossing p c E rho crossing mono hnr a b m hab hb hm hfixed
  · intro i ev x W m hi hx hgst hm hfront hbefore hafter hh
    have he := healing_evidence_spread (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync i ev x W m
      hi hx hgst hm hfront hbefore hafter hh
    exact ⟨fun hhor y hy => he.1 hhor y hy
      (hAwake y hy _ (hgst.trans (le_add_of_nonneg_right p.deltaPos.le)) hhor), he.2⟩
  · intro i ev v m kind hi heff hgst hu hv hm hfront hkind hquiet
    obtain ⟨J, h⟩ := healing_settle_event (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync hAwake
      i ev v m kind hi heff hgst hu hv hm hfront hkind hquiet
    refine ⟨J, ?_⟩
    cases kind <;> exact h
  · intro u v m J contested hgst hp i x hui hiv hx
    exact healing_settled_frame p c E rho crossing u v m J contested hgst hp i x hui hiv hx
  · intro i x m X B hx hi hm hH hX hB hpath hh
    exact healing_frontier_mem p c E rho crossing i x m X B hx hi hm hH hX hB hpath hh

/-- Quiet phase windows use all-restart FG bounds. -/
theorem healing_phase_window_all (mono : RMonoAll p c E rho) {i m : Nat} {v : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hquiet : ∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) :
    ∀ k, i + 1 ≤ k → k ≤ timeIdx rho v →
      frontierAtIdx p c E rho k = m ∧
      (TopEvidence p c E rho k m → TopEvidence p c E rho (i + 1) m) ∧
      (ContestEvidence p c E rho k m → ContestEvidence p c E rho (i + 1) m) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨hfront, id, id⟩
  | succ k hk ih =>
    intro hkv
    obtain ⟨hf, ht, hc⟩ := ih (by omega)
    have hq := hquiet k (by omega) (by omega)
    have hmono := healing_frontier_mono_all p c E rho mono (Nat.le_add_right k 1)
    have hf' : frontierAtIdx p c E rho (k + 1) = m := by
      by_contra hne
      exact hq (Or.inl (by omega))
    refine ⟨hf', fun h => ht ?_, fun h => hc ?_⟩
    · by_contra hn
      exact hq (Or.inr (show (¬ TopEvidence p c E rho k (frontierAtIdx p c E rho (k + 1)) ∧
        TopEvidence p c E rho (k + 1) (frontierAtIdx p c E rho (k + 1))) ∨ _ from
        Or.inl (by rw [hf']; exact ⟨hn, h⟩)))
    · by_contra hn
      exact hq (Or.inr (show _ ∨
        (¬ ContestEvidence p c E rho k (frontierAtIdx p c E rho (k + 1)) ∧
        ContestEvidence p c E rho (k + 1) (frontierAtIdx p c E rho (k + 1))) from
        Or.inr (by rw [hf']; exact ⟨hn, h⟩)))


/-- Retained settlement uses per-object local services and durable storage. -/
theorem healing_settle_start_on (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (mono : RMonoAll p c E rho)
    (hServices : ∀ i (ev : V2.Event V (Obj p)) x W y,
      rho.events[i]? = some ev → x ∈ rho.honest → y ∈ rho.honest →
      E.t_GST ≤ ev.time → W ∈ (storeAt p c E rho (i + 1) x).fg.TF →
      ev.time + p.Δ ≤ rho.horizon →
      TargetReceiptService E rho (eraseFG W) (ev.time + p.Δ) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ i ev v m kind, rho.events[i]? = some ev →
      E.t_GST ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
          SA.voteTime p.toParams s ≤ v →
          postClock E rho y (SA.voteTime p.toParams s) = some nd →
          SettledPhaseFrame p nd.st m root contested) := by
  intro i (ev : V2.Event V (Obj p)) v m kind hi hgst hu hv hm hfront hkind hquiet
  -- Restate the event times at the object type of the relay lemmas.
  have hu : ev.time + 3 * p.Δ ≤ v := hu
  have hgst : E.t_GST ≤ ev.time := hgst
  have hs := hvalid.toScheduleWellFormed
  have hpos := p.deltaPos
  have hij0 : i < V2.D.Run.idxBefore rho (ev.time + p.Δ) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (lt_add_of_pos_right _ hpos)
  have hdv : ev.time + p.Δ ≤ v := by
    simp only [Time] at *
    omega
  have hj0v : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ timeIdx rho v :=
    healing_phase_idx_le_time p c rho hdv
  have hhor : ev.time + p.Δ ≤ rho.horizon := hdv.trans hv
  have hwin := healing_phase_window_all p c E rho mono hfront hquiet
  have hcap (k : Nat) (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k)
      (hkv : k ≤ timeIdx rho v) :
      frontierAtIdx p c E rho k = m := (hwin k (by omega) hkv).1
  -- Every carrier held at i + 1 is held by every honest node in the window.
  have relay {x : V} {W : FGBlock (Fin p.n)} (hW : HeldAt p c E rho (i + 1) x W)
      (hh : (heightView p W).h = m) {k : Nat} {y : V}
      (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k) (hy : y ∈ rho.honest) :
      W ∈ (storeAt p c E rho k y).fg.TF := by
    have h0 := healing_held_block_receipt_on p c E rho hvalid hroots W
      (ev.time + p.Δ) y hy (hServices i ev x W y hi hW.1 hy hgst hW.2 hhor)
    change W ∈ (V2.D.Run.stateBeforeTime E rho (ev.time + p.Δ) y).st.fg.TF at h0
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at h0
    exact (fgsa_store_durable p c E rho hk y).1 h0
  have hH {x : V} {W : FGBlock (Fin p.n)} (hW : HeldAt p c E rho (i + 1) x W)
      (hh : (heightView p W).h = m) {k : Nat} {y : V}
      (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k) (hkv : k ≤ timeIdx rho v)
      (hy : y ∈ rho.honest) : (R_at p c E rho k y).H = m :=
    le_antisymm ((healing_phase_local_le_frontier p c E rho hy).trans_eq (hcap k hk hkv))
      (hh ▸ healing_phase_height_le p c E rho (relay hW hh hk hy))
  have wit := healing_phaseWitness p c E rho hm hfront
  cases kind with
  | gap =>
    obtain ⟨hnt, _⟩ := hkind
    obtain ⟨x, W, hW, hh⟩ := wit.frontier
    refine ⟨.genesis, settle_finish p c E rho crossing hvalid hu hv hm ?_⟩
    intro k y hk hkv hy
    have hHk := hH hW hh hk hkv hy
    have hnj : (storeAt p c E rho k y).fg.h_j + 1 ≠ m :=
      fun ht => hnt ((hwin k (by omega) hkv).2.1 ⟨y, hy, ht⟩)
    change (storeAt p c E rho k y).fg.h_max = m at hHk
    have hc : (R_at p c E rho k y).contest = false := by
      change (decide ((storeAt p c E rho k y).fg.h_max =
        (storeAt p c E rho k y).fg.h_j + 1) && _) = false
      rw [hHk]
      simp only [Ne.symm hnj, decide_false, Bool.false_and]
    refine ⟨hHk, hc, ?_⟩
    change (decide ((R_at p c E rho k y).H = (R_at p c E rho k y).j + 1) &&
      !(R_at p c E rho k y).contest) = false
    change (decide ((storeAt p c E rho k y).fg.h_max =
      (storeAt p c E rho k y).fg.h_j + 1) && _) = false
    rw [hHk]
    simp only [Ne.symm hnj, decide_false, Bool.false_and]
  | topJ =>
    obtain ⟨ht, hnc⟩ := hkind
    obtain ⟨x, C, hC, hh, hj, _⟩ := wit.top ht
    refine ⟨(heightView p C).J, settle_finish p c E rho crossing hvalid hu hv hm ?_⟩
    intro k y hk hkv hy
    have hCk := relay hC hh hk hy
    obtain ⟨hmax, htop, hJ⟩ := healing_phase_top_node p c E rho crossing hy hCk hh hj
      (hcap k hk hkv).le
    have hc : (R_at p c E rho k y).contest = false := by
      cases he : (R_at p c E rho k y).contest with
      | false => rfl
      | true => exact (hnc ((hwin k (by omega) hkv).2.2 ⟨y, hy, hmax, he⟩)).elim
    have hc' := hc
    change (decide ((storeAt p c E rho k y).fg.h_max =
      (storeAt p c E rho k y).fg.h_j + 1) && decide (∃ W ∈ (storeAt p c E rho k y).fg.TF,
        FGBlock.Preceq (storeAt p c E rho k y).fg.F W ∧
        (heightView p W).h = (storeAt p c E rho k y).fg.h_max ∧
        ¬ FGBlock.Preceq (storeAt p c E rho k y).fg.J W)) = false at hc'
    have hJC : FGBlock.Preceq (storeAt p c E rho k y).fg.J C := by
      by_contra hn
      rcases Bool.and_eq_false_iff.mp hc' with h | h
      · exact of_decide_eq_false h (hmax.trans htop.symm)
      · exact of_decide_eq_false h ⟨C, hCk,
          (healing_phase_frontier_root p c E rho crossing hy hCk
            (hh.trans hmax.symm)).1, hh.trans hmax.symm, hn⟩
    refine ⟨hmax, hc, ?_, hJ hJC⟩
    change (decide ((storeAt p c E rho k y).fg.h_max =
      (storeAt p c E rho k y).fg.h_j + 1) && !(R_at p c E rho k y).contest) = true
    rw [hc, hmax, htop]
    simp only [decide_true, Bool.not_false, Bool.and_self]
  | contest =>
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff⟩ := wit.contest hkind
    refine ⟨.genesis, settle_finish p c E rho crossing hvalid hu hv hm ?_⟩
    intro k y hk hkv hy
    have hCk := relay hC hhC hk hy
    have hWk := relay hW hhW hk hy
    obtain ⟨hmax, htop, hJ⟩ := healing_phase_top_node p c E rho crossing hy hCk hhC hj
      (hcap k hk hkv).le
    have hc : (R_at p c E rho k y).contest = true := by
      change (decide ((storeAt p c E rho k y).fg.h_max =
        (storeAt p c E rho k y).fg.h_j + 1) && decide (∃ W ∈ (storeAt p c E rho k y).fg.TF,
          FGBlock.Preceq (storeAt p c E rho k y).fg.F W ∧
          (heightView p W).h = (storeAt p c E rho k y).fg.h_max ∧
          ¬ FGBlock.Preceq (storeAt p c E rho k y).fg.J W)) = true
      refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hmax.trans htop.symm),
        decide_eq_true ?_⟩
      by_cases hJC : FGBlock.Preceq (storeAt p c E rho k y).fg.J C
      · exact ⟨W, hWk,
          (healing_phase_frontier_root p c E rho crossing hy hWk
            (hhW.trans hmax.symm)).1, hhW.trans hmax.symm,
          by rw [hJ hJC]; exact hoff⟩
      · exact ⟨C, hCk,
          (healing_phase_frontier_root p c E rho crossing hy hCk
            (hhC.trans hmax.symm)).1, hhC.trans hmax.symm, hJC⟩
    refine ⟨hmax, hc, ?_⟩
    change (decide ((R_at p c E rho k y).H = (R_at p c E rho k y).j + 1) &&
      !(R_at p c E rho k y).contest) = false
    rw [hc]
    simp only [Bool.not_true, Bool.and_false]

end AvailableChain.FGSA.Run
end
