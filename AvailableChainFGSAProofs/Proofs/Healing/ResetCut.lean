module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! S5 RS-0, plan Q4; blueprint 21 H.11:1744–1800.
The cut includes all events at its time. The frontier is the frozen
`honestFrontier`, with no replacement. Foundations supplies the INLINE
`emittedName` input through `emittedName_window` (Sources:217).

C1 STOP: the permitted inputs do not supply an event at the cut. A finite
run can end before the cut. C3 STOP: the permitted inputs allow an empty
honest set. Then the frontier is zero and `muOf` is one. The results below
prove the timing, row cap, old-row bound, and exact conditions for these gaps.
No premise is added to close either item. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- H.11: the period is at least 8Δ. Params supplies R ≥ 2. -/
theorem reset_period_lower : 8 * p.Δ ≤ P p := by
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
  nlinarith [p.deltaPos]

/-- H.11: the action clock has a round at or after recoveryStart. -/
theorem reset_action_exists : ∃ r, recoveryStart p E ≤ p.actionTime r := by
  refine ⟨(recoveryStart p E).toNat + 1, ?_⟩
  rw [actionTime_periodW]
  have hP : 1 ≤ P p := by
    have hd : 1 ≤ p.Δ := p.deltaPos
    have hp := reset_period_lower p
    linarith
  have hn : 0 ≤ ((recoveryStart p E).toNat : Time) := Int.natCast_nonneg _
  have ht := Int.self_le_toNat (recoveryStart p E)
  push_cast
  nlinarith [p.deltaPos]

/-- H.11: the first mathematical action round at or after recoveryStart. -/
noncomputable def resetFirstRound : Nat := Nat.find (reset_action_exists p E)

/-- H.11: the time of the inclusive cut. -/
noncomputable def resetCutTime : Time := p.actionTime (resetFirstRound p E + 2)

theorem reset_rG_after : recoveryStart p E ≤ p.actionTime (resetFirstRound p E) :=
  Nat.find_spec (reset_action_exists p E)

theorem reset_rG_first (r : Nat) (hr : recoveryStart p E ≤ p.actionTime r) :
    resetFirstRound p E ≤ r := Nat.find_min' (reset_action_exists p E) hr

theorem reset_cut : resetCutTime p E = p.actionTime (resetFirstRound p E + 2) := by
  exact Eq.refl _

/-- H.11: the first action lies in [recoveryStart, recoveryStart + P). -/
theorem reset_first_action_upper :
    p.actionTime (resetFirstRound p E) < recoveryStart p E + P p := by
  by_cases hz : resetFirstRound p E = 0
  · rw [hz, actionTime_periodW]
    have hp := reset_period_lower p
    have hg : 0 ≤ recoveryStart p E := by
      have hτ := healing_recovery_start_lower (p := p) E
      linarith [E.t_GST_nonneg, p.deltaPos]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    linarith [p.deltaPos]
  · have hpred : p.actionTime (resetFirstRound p E - 1) < recoveryStart p E := by
      by_contra hn
      have hm := reset_rG_first p E (resetFirstRound p E - 1) (le_of_not_gt hn)
      omega
    rw [actionTime_periodW] at hpred ⊢
    have hn : 1 ≤ resetFirstRound p E := by omega
    push_cast [hn] at hpred
    linarith

theorem reset_cut_lower : recoveryStart p E + 2 * P p ≤ resetCutTime p E := by
  have ha := reset_rG_after p E
  rw [actionTime_periodW] at ha
  rw [reset_cut, actionTime_periodW]
  push_cast
  linarith

theorem reset_cut_upper : resetCutTime p E < recoveryStart p E + 3 * P p := by
  have ha := reset_first_action_upper p E
  rw [actionTime_periodW] at ha
  rw [reset_cut, actionTime_periodW]
  push_cast
  linarith

variable [DecidableEq V]

/-- H.11: the frozen honest frontier at the cut. -/
noncomputable def resetCutFrontier : Nat := honestFrontier p c E rho (resetCutTime p E)

theorem reset_frontier :
    resetCutFrontier p c E rho = honestFrontier p c E rho (resetCutTime p E) := by
  exact Eq.refl _

/-- C4: the time read includes all simultaneous ticks and deliveries. -/
theorem reset_inclusive_frontier (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    honestFrontier p c E rho t = frontierAtIdx p c E rho (timeIdx rho t) := by
  unfold honestFrontier frontierAtIdx storeAt timeIdx
  rw [V2.D.Engine.readAt_eq_stateBefore hs t]

omit [DecidableEq V] in
/-- C1 gap: a cut has a last event at its time exactly when that time occurs
in the finite run. The last index includes every event at that time. -/
theorem reset_inclusive_start_iff (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    (∃ start ev, rho.events[start]? = some ev ∧ ev.time = t ∧
      timeIdx rho t = start + 1) ↔ ∃ ev ∈ rho.events, ev.time = t := by
  constructor
  · rintro ⟨start, ev, he, ht, _⟩
    exact ⟨ev, List.mem_of_getElem? he, ht⟩
  · rintro ⟨ev, hev, ht⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hev
    have hjn : j < timeIdx rho t :=
      (V2.D.Engine.index_lt_read_length_iff hs t hj).mpr ht.le
    have hn : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
    have hslt : timeIdx rho t - 1 < rho.events.length := by omega
    have hlast := List.getElem?_eq_getElem hslt
    let last := rho.events[timeIdx rho t - 1]
    have hle : last.time ≤ t :=
      (V2.D.Engine.index_lt_read_length_iff hs t hlast).mp
        (show timeIdx rho t - 1 < timeIdx rho t by omega)
    have hge : t ≤ last.time := by
      by_cases heq : j = timeIdx rho t - 1
      · subst j
        have he : ev = last := Option.some.inj (hj.symm.trans hlast)
        exact ht ▸ he ▸ le_rfl
      · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        have hk := (List.pairwise_iff_getElem.mp hs.sorted) j
          (timeIdx rho t - 1) hjl hslt (by omega)
        rw [hje] at hk
        exact ht ▸ V2.D.Engine.time_le_of_key_le _ _ hk
    exact ⟨timeIdx rho t - 1, last, hlast, le_antisymm hle hge, by omega⟩

/-- C2: the actual row source is stored before its action and remains in
the cumulative store at the inclusive cut. INLINE producer: emittedName_window. -/
theorem reset_row_cap (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {j r h : Nat} {y : V} {a : RowWire p.n} {e : BlockId} {t u : Time}
    (ha : HonestRowAt p c E rho j y r a) (hj : rho.events[j]? = some (.tick y t))
    (htu : t ≤ u) (he : namedEntry a.payload.height_pair = some (h, e)) :
    h ≤ honestFrontier p c E rho u := by
  obtain ⟨C, _, hC, hh, _⟩ := emittedName ha he
  have hheld := repair_source_mem E rho hs ha.2.1 hC
  have hidx : j ≤ timeIdx rho u :=
    (V2.D.Engine.index_lt_read_length_iff hs u hj).mpr htu |>.le
  have hcut := (fgsa_store_durable p c E rho hidx y).1 hheld
  have hheight := healing_phase_height_le p c E rho hcut
  rw [reset_inclusive_frontier p c E rho hs u]
  exact hh.trans_le (hheight.trans
    (Finset.le_sup (f := fun x => (storeAt p c E rho (timeIdx rho u) x).fg.h_max) ha.1))

omit [DecidableEq V] in
/-- C3 timing: an old row acts 5Δ after its vote and strictly before u₀. -/
theorem reset_old_row_before_cut {r : Nat}
    (hold : SA.voteTime p.toParams (r * p.R) < recoveryStart p E) :
    p.actionTime r < resetCutTime p E := by
  have ht : p.actionTime r = SA.voteTime p.toParams (r * p.R) + 5 * p.Δ := by
    change 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ =
      4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ + 5 * p.Δ
    ring
  rw [ht]
  have hp := reset_period_lower p
  have hc := reset_cut_lower p E
  linarith [p.deltaPos]

/-- C3 causal part: all old-row heights are bounded by the frozen M.
The result also holds for an empty honest set. -/
theorem reset_old_height_sup_le (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    sSup (oldRowHeights p c E rho) ≤ resetCutFrontier p c E rho := by
  apply csSup_le'
  rintro h ⟨j, y, r, a, e, ha, he, hold⟩
  exact reset_row_cap p c E rho hs emittedName ha ha.2.1
    (reset_old_row_before_cut p E hold).le he

/-- C3 gap: μ ≤ M holds exactly when the honest set is nonempty.
The permitted standing inputs do not imply this condition. -/
theorem reset_mu_le_iff (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    muOf p c E rho ≤ resetCutFrontier p c E rho ↔ rho.honest.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : resetCutFrontier p c E rho = 0 := by
      change rho.honest.sup (fun x =>
        (V2.D.Run.readAt E rho (resetCutTime p E) x).st.fg.h_max) = 0
      rw [he]
      exact Finset.sup_empty
    have h1 : 1 ≤ muOf p c E rho := Nat.le_max_left _ _
    omega
  · rintro ⟨x, hx⟩
    rw [muOf_def]
    apply max_le
    · rw [reset_frontier, reset_inclusive_frontier p c E rho hs]
      have hg := (storeBundle_stateBefore E rho (timeIdx rho (resetCutTime p E)) x).cstore.fg.gen
      exact ((fgCertificateLaws p).height.one_le_h .genesis).trans
        ((healing_phase_height_le p c E rho hg).trans
          (Finset.le_sup (f := fun x =>
            (storeAt p c E rho (timeIdx rho (resetCutTime p E)) x).fg.h_max) hx))
    · exact reset_old_height_sup_le p c E rho hs emittedName

end AvailableChain.FGSA.Run
end
