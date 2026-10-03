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
theorem frontierSearch_classify_stop (hnr : V2.D.NoRestart rho)
    {i m : Nat} {deadline : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hstop : FirstEffectiveBy p c E rho i deadline) :
    FirstPhaseStopBy p c E rho i m deadline ∨
      FirstRiseStopBy p c E rho i m deadline := by
  obtain ⟨j, ev, hij, hj, ht, heff, hfirst⟩ := (firstEffectiveBy_iff p c E rho i deadline).mp hstop
  have hmono := healing_frontier_mono p c E rho hnr
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
theorem frontierSearch_phase_step (mono : RMono p c E rho) (hnr : V2.D.NoRestart rho)
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
    · exact (healing_frontier_mono p c E rho hnr hkj).trans_eq hf
    · exact hf0 ▸ healing_frontier_mono p c E rho hnr hik
  have horder := healing_phase_order p c E rho mono hnr (i + 1) (j + 1) m
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

end AvailableChain.FGSA.Run
end
