module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW

public section

/-! Blueprint 21 H.10/HG.3/HG.5; frontier plan gaps 6 and 7.
Least events are selected only inside the finite run prefix.
Earlier rows retain their actual emission, including SO-COV coverage. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
/-- Blueprint 21 H.10; plan §4 closed horizon.
DC: SAME an actual event in the inclusive prefix has time at most its cut. -/
theorem frontierSearch_event_time_le (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {ev : V2.Event V (Obj p)} {deadline : Time}
    (hj : rho.events[j]? = some ev) (hcut : j < timeIdx rho deadline) :
    ev.time ≤ deadline := by
  have hc : V2.D.Run.idxBefore rho (deadline + 1) = timeIdx rho deadline := by
    change (rho.events.filter (fun e => decide (e.time < deadline + 1))).length =
      (rho.events.filter (fun e => decide (e.time ≤ deadline))).length
    simp only [Int.lt_add_one_iff]
  exact Int.lt_add_one_iff.mp
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mp (hc ▸ hcut))

/-- Blueprint 21 H.10 and HG.3; plan gap 6.
DC: SAME construct the least actual event in the closed deadline prefix. -/
theorem frontierSearch_first_effective_split (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (deadline : Time) :
    FirstEffectiveBy p c E rho i deadline ∨
      (∀ j, i < j → j < timeIdx rho deadline → ¬ EffectiveEvent p c E rho j) := by
  classical
  by_cases hex : ∃ j, i < j ∧ j < timeIdx rho deadline ∧ EffectiveEvent p c E rho j
  · left
    apply (firstEffectiveBy_iff p c E rho i deadline).mpr
    let j := Nat.find hex
    obtain ⟨hij, hjd, heff⟩ := Nat.find_spec hex
    have hjlen : j < rho.events.length := hjd.trans_le (List.length_filter_le ..)
    let ev := rho.events[j]
    have hj : rho.events[j]? = some ev := List.getElem?_eq_getElem hjlen
    have htime := frontierSearch_event_time_le p c E rho hs hj hjd
    refine ⟨j, ev, hij, hj, htime, heff, ?_⟩
    intro k hik hkj he
    exact Nat.find_min hex hkj ⟨hik, hkj.trans hjd, he⟩
  · right
    intro j hij hjd he
    exact hex ⟨j, hij, hjd, he⟩

/-- Blueprint 21 HG.3; plan Q1.
DC: SAME classify the finite first stop by its actual frontier. -/
theorem frontierSearch_classify_stop (mono : RMonoAll p c E rho)
    {i m : Nat} {deadline : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hstop : FirstEffectiveBy p c E rho i deadline) :
    FirstPhaseStopBy p c E rho i m deadline ∨
      FirstRiseStopBy p c E rho i m deadline := by
  obtain ⟨j, ev, hij, hj, ht, heff, hfirst⟩ := (firstEffectiveBy_iff p c E rho i deadline).mp hstop
  have hmono := healing_frontier_mono_all p c E rho mono
    (show i + 1 ≤ j + 1 by omega)
  rw [hfront] at hmono
  by_cases heq : frontierAtIdx p c E rho (j + 1) = m
  · exact Or.inl ((firstPhaseStopBy_iff p c E rho i m deadline).mpr
      ⟨j, ev, hij, hj, ht, heff, heq, hfirst⟩)
  · exact Or.inr ((firstRiseStopBy_iff p c E rho i m deadline).mpr
      ⟨j, ev, hij, hj, ht, heff, by omega, hfirst⟩)

/-- Blueprint 21 HG.1/HG.4; plan §4.
DC: SAME first rise selection permits earlier same-frontier events. -/
theorem frontierSearch_first_rise (hs : V2.D.ScheduleWellFormed E rho)
    {i m : Nat} {deadline : Time}
    (hex : ∃ j, i < j ∧ j < timeIdx rho deadline ∧
      m < frontierAtIdx p c E rho (j + 1))
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m) :
    FrontierRiseBy p c E rho i m deadline := by
  classical
  apply (frontierRiseBy_iff p c E rho i m deadline).mpr
  let j := Nat.find hex
  obtain ⟨hij, hjd, hheight⟩ := Nat.find_spec hex
  have hjlen : j < rho.events.length := hjd.trans_le (List.length_filter_le ..)
  let ev := rho.events[j]
  have hj : rho.events[j]? = some ev := List.getElem?_eq_getElem hjlen
  refine ⟨j, ev, hij, hj, frontierSearch_event_time_le p c E rho hs hj hjd, hheight, ?_⟩
  intro k hik hkj
  by_cases hk : k = i + 1
  · exact hk ▸ hstart
  · by_contra hn
    have hkpos : 0 < k := by omega
    have hpred : i < k - 1 := by omega
    have hpredj : k - 1 < j := by omega
    apply Nat.find_min hex hpredj
    exact ⟨hpred, hpredj.trans hjd, by simpa only [Nat.sub_add_cancel hkpos] using
      (lt_of_not_ge hn)⟩

/-- Blueprint 21 HG.4/H.11; plan §3.3.
DC: SAME select one first row from an actual emitted row. -/
theorem frontierSearch_first_row {m r : Nat} {deadline : Time}
    (hrow : HeightRow p c E rho r m) (htime : p.actionTime r ≤ deadline) :
    FirstHeightRowBy p c E rho m deadline := by
  classical
  apply (firstHeightRowBy_iff p c E rho m deadline).mpr
  have hex : ∃ r', HeightRow p c E rho r' m := ⟨r, hrow⟩
  have hfirst : Nat.find hex ≤ r := Nat.find_min' hex hrow
  refine ⟨Nat.find hex, Nat.find_spec hex, fun r' hr' => Nat.find_min' hex hr', ?_⟩
  have hc : (Nat.find hex : Time) ≤ r := by exact_mod_cast hfirst
  have hP : 0 ≤ P p := by
    change 0 ≤ 4 * (p.R : Time) * p.Δ
    have hd := p.deltaPos
    positivity
  rw [actionTime_periodW] at htime ⊢
  have hm := mul_le_mul_of_nonneg_right hc hP
  linarith only [hm, htime]

/-- Blueprint 21 H.11; plan §3.3 reset minimization.
DC: SAME both repair allowances must select this same first round. -/
theorem frontierSearch_first_row_unique {m r r' : Nat}
    (hr : HeightRow p c E rho r m)
    (hfirst : ∀ s, HeightRow p c E rho s m → r ≤ s)
    (hr' : HeightRow p c E rho r' m)
    (hfirst' : ∀ s, HeightRow p c E rho s m → r' ≤ s) : r = r' :=
  Nat.le_antisymm (hfirst r' hr') (hfirst' r hr)

/-- Blueprint 21 HG.5 and IF.3(a); plan §3.3.
DC: SAME a skipped frontier supplies a real earlier honest M+1 row via RCap.
The height inequality alone is never used as a row witness. -/
theorem frontierSearch_skipped_row (cap : RCap p c E rho)
    {M i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hW : HeldAt p c E rho i x W) (hskip : M + 2 ≤ (heightView p W).h) :
    ∃ j z r a e, j < i ∧ HonestRowAt p c E rho j z r a ∧
      namedEntry a.payload.height_pair = some (M + 1, e) := by
  obtain ⟨j, z, r, a, e, hji, hr, hn, _⟩ := cap M i x W hW hskip
  exact ⟨j, z, r, a, e, hji, hr, hn⟩

omit [DecidableEq V] in
/-- Blueprint 21 HG.5. DC: SAME three phase charges in their fixed order. -/
def frontierSearch_phaseRank (kind : PhaseKind) : Nat :=
  match kind with | .gap => 0 | .topJ => 1 | .contest => 2

/-- Blueprint 21 HG.5; phase-order composition.
DC: SAME a same-frontier effective stop strictly advances the phase.
Thus the gap and top-J charge cannot be repeated at this frontier. -/
theorem frontierSearch_phase_step_of_crossing (crossing : RXing p c E rho)
    (mono : RMonoAll p c E rho)
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {kind : PhaseKind}
    {ev : V2.Event V (Obj p)} {deadline : Time}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hstop : FirstPhaseStopBy p c E rho i m deadline) :
    ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
      FrontierSearchStart p c E rho j nextEv m nextKind ∧
      frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind := by
  classical
  obtain ⟨j, nextEv, hij, hj, ht, heff, hf, _⟩ :=
    (firstPhaseStopBy_iff p c E rho i m deadline).mp hstop
  obtain ⟨hi, hgst, _, hf0, hm, hk⟩ :=
    (frontierSearchStart_iff p c E rho i ev m kind).mp hstart
  have hjlen : j < rho.events.length := (List.getElem?_eq_some_iff.mp hj).1
  have hfixed : ∀ k, i + 1 ≤ k → k ≤ j + 1 → frontierAtIdx p c E rho k = m := by
    intro k hik hkj
    apply Nat.le_antisymm
    · exact (healing_frontier_mono_all p c E rho mono hkj).trans_eq hf
    · exact hf0 ▸ healing_frontier_mono_all p c E rho mono hik
  have horder := healing_phase_order_of_crossing_all p c E rho crossing mono
    (i + 1) (j + 1) m
    (by omega) (by omega) hm hfixed
  have hbits := horder.1 (i + 1) j le_rfl (by omega) (by omega)
  have heff' : (¬ TopEvidence p c E rho j m ∧ TopEvidence p c E rho (j + 1) m) ∨
      (¬ ContestEvidence p c E rho j m ∧ ContestEvidence p c E rho (j + 1) m) := by
    rcases heff with h | h
    · rw [hfixed j (by omega) (by omega), hf] at h
      exact (lt_irrefl m h).elim
    · simpa only [hf] using h
  have htime : ev.time ≤ nextEv.time := by
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    have hkey := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
    rw [hie, hje] at hkey
    exact V2.D.Engine.time_le_of_key_le _ _ hkey
  have finish (nextKind : PhaseKind) (hnext : AttemptPhaseAt p c E rho (j + 1) m nextKind)
      (hrank : frontierSearch_phaseRank kind < frontierSearch_phaseRank nextKind) :
      ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
        FrontierSearchStart p c E rho j nextEv m nextKind ∧
        frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind := by
    exact ⟨j, nextEv, nextKind, hij, ht,
      (frontierSearchStart_iff p c E rho j nextEv m nextKind).mpr
        ⟨hj, hgst.trans htime, Or.inl heff, hf, hm, hnext⟩, hrank⟩
  cases kind with
  | gap =>
    rcases heff' with ⟨_, ht⟩ | ⟨_, hc⟩
    · by_cases hc : ContestEvidence p c E rho (j + 1) m
      · exact finish .contest hc (by decide)
      · exact finish .topJ ⟨ht, hc⟩ (by decide)
    · exact finish .contest hc (by decide)
  | topJ =>
    have htj := hbits.1 hk.1
    rcases heff' with ⟨hn, _⟩ | ⟨_, hc⟩
    · exact (hn htj).elim
    · exact finish .contest hc (by decide)
  | contest =>
    have hcj := hbits.2 hk
    have ht0 := horder.2 (i + 1) le_rfl (by omega) hk
    have htj := hbits.1 ht0
    rcases heff' with ⟨hn, _⟩ | ⟨hn, _⟩
    · exact (hn htj).elim
    · exact (hn hcj).elim

/-- Blueprint 21:1592–1638; S5 H2, route step 1.
DC: SAME choose the first rise strictly before D, or cap the strict cut.
A rise at exactly D does not enter the strict prefix. Same-frontier events do not stop it. -/
theorem frontierSearch_strict_cap_or_rise
    (hs : V2.D.ScheduleWellFormed E rho) (mono : RMonoAll p c E rho)
    (i m : Nat) (D : Time) (hstart : frontierAtIdx p c E rho (i + 1) ≤ m) :
    FrontierRiseBy p c E rho i m D ∨
      (∀ k x, k ≤ V2.D.Run.idxBefore rho D → x ∈ rho.honest →
        (storeAt p c E rho k x).fg.h_max ≤ m) := by
  classical
  by_cases hc : frontierAtIdx p c E rho (V2.D.Run.idxBefore rho D) ≤ m
  · right
    intro k x hk hx
    exact (healing_phase_local_le_frontier p c E rho hx).trans
      ((healing_frontier_mono_all p c E rho mono hk).trans hc)
  · left
    have hcut : i + 1 < V2.D.Run.idxBefore rho D := by
      by_contra hn
      exact hc ((healing_frontier_mono_all p c E rho mono (by omega)).trans hstart)
    have hex : ∃ j, i < j ∧ j < V2.D.Run.idxBefore rho D ∧
        m < frontierAtIdx p c E rho (j + 1) := by
      refine ⟨V2.D.Run.idxBefore rho D - 1, by omega, by omega, ?_⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ V2.D.Run.idxBefore rho D)] using
        (lt_of_not_ge hc)
    let j := Nat.find hex
    obtain ⟨hij, hjD, hh⟩ := Nat.find_spec hex
    have hjlen : j < rho.events.length := hjD.trans_le (List.length_filter_le ..)
    let ev := rho.events[j]
    have hj : rho.events[j]? = some ev := List.getElem?_eq_getElem hjlen
    apply (frontierRiseBy_iff p c E rho i m D).mpr
    refine ⟨j, ev, hij, hj,
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hj D).mp hjD).le, hh, ?_⟩
    intro k hik hkj
    by_cases hk : k = i + 1
    · exact hk ▸ hstart
    · by_contra hn
      have hkpos : 0 < k := by omega
      apply Nat.find_min hex (show k - 1 < j by omega)
      exact ⟨by omega, by omega, by
        simpa only [Nat.sub_add_cancel hkpos] using (lt_of_not_ge hn)⟩

omit [DecidableEq V] in
/-- Blueprint 21:1592–1638; S5 H2, route step 4.
DC: SAME an inclusive earlier read lies inside the strict later cut. -/
theorem frontierSearch_timeIdx_le_idxBefore {t D : Time} (ht : t < D) :
    timeIdx rho t ≤ V2.D.Run.idxBefore rho D := by
  change (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
    (rho.events.filter (fun e => decide (e.time < D))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_lt ht))

/-- Blueprint 21:1695–1720; S5 F2.
DC: SAME a longer deadline retains the same first rise and earlier frontier cap. -/
theorem frontierSearch_rise_mono {i m : Nat} {d D : Time} (hd : d ≤ D)
    (hr : FrontierRiseBy p c E rho i m d) : FrontierRiseBy p c E rho i m D := by
  obtain ⟨j, ev, hij, hj, ht, hh, hf⟩ := (frontierRiseBy_iff p c E rho i m d).mp hr
  exact (frontierRiseBy_iff p c E rho i m D).mpr ⟨j, ev, hij, hj, ht.trans hd, hh, hf⟩

/-- Blueprint 21:1695–1720; S5 F2.
DC: SAME strict honest high receipt forces a first rise before the receipt deadline. -/
theorem frontierSearch_rise_of_receipt (hs : V2.D.ScheduleWellFormed E rho)
    (mono : RMonoAll p c E rho) {i m : Nat} {d D : Time} {x : V}
    {X : FGBlock (Fin p.n)} (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hx : x ∈ rho.honest) (hh : m + 1 ≤ (heightView p X).h)
    (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ nd.st.fg.TF) d x)
    (hd : d ≤ D) : FrontierRiseBy p c E rho i m D := by
  rcases frontierSearch_strict_cap_or_rise p c E rho hs mono i m D hstart with hr | hc
  · exact hr
  · change X ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
    have hX := (fgsa_store_durable p c E rho
      (healing_phase_idxBefore_mono p c rho hd) x).1 hheld
    have hhi := healing_phase_height_le p c E rho hX
    have hcap := hc _ x le_rfl hx
    simp only [Height] at *
    omega

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen phase rank for finite composition. -/
@[simp] theorem frontierSearch_phaseRank_gap :
    frontierSearch_phaseRank .gap = 0 := by
  exact Eq.refl _

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen phase rank for finite composition. -/
@[simp] theorem frontierSearch_phaseRank_topJ :
    frontierSearch_phaseRank .topJ = 1 := by
  exact Eq.refl _

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen phase rank for finite composition. -/
@[simp] theorem frontierSearch_phaseRank_contest :
    frontierSearch_phaseRank .contest = 2 := by
  exact Eq.refl _

end AvailableChain.FGSA.Run
end
