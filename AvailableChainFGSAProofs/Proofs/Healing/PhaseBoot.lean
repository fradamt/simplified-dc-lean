module
public import AvailableChainFGSAProofs.Proofs.Healing.Phase

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1236–1237, 1467–1468; plan S20, H-PHASE r2/Q3.
DC: SAME every cache has height at least one. -/
private theorem boot_one_le_hmax (i : Nat) (x : V) :
    1 ≤ (storeAt p c E rho i x).fg.h_max := by
  have hs : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho i x).fg := (storeBundle_stateBefore E rho i x).cstore.fg
  rw [hs.hmax]
  exact le_sup_right

/-- Blueprint 21:1236–1237, 1467–1468; plan S20, H-PHASE r2/Q3 (B1).
DC: INTENTIONAL at frontier one each live frame is the genesis top-J frame.
No contest is possible. This fact is not a PhaseInterval, which needs 2 ≤ m. -/
theorem healing_phase_height_one {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hfront : frontierAtIdx p c E rho i = 1) :
    (R_at p c E rho i x).H = 1 ∧ (R_at p c E rho i x).j = 0 ∧
      (R_at p c E rho i x).J = .genesis ∧ (R_at p c E rho i x).contest = false ∧
      (R_at p c E rho i x).rootIsJ = true := by
  let st := storeAt p c E rho i x
  have hs : KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg :=
    (storeBundle_stateBefore E rho i x).cstore.fg
  have hmax : st.fg.h_max = 1 := le_antisymm
    ((healing_phase_local_le_frontier p c E rho hx).trans_eq hfront)
    (boot_one_le_hmax p c E rho i x)
  have hj : st.fg.h_j = 0 := by
    have := healing_phase_justified_lt p c E rho i x
    change st.fg.h_j < st.fg.h_max at this
    (simp only [Height] at *; omega)
  have hJ : st.fg.J = .genesis := by
    obtain ⟨C, _, _, hjC, hJC⟩ := hs.pair.1
    rw [hJC]
    exact (fgCertificateLaws p).justified_zero C (hjC ▸ hj)
  have hc : (R_at p c E rho i x).contest = false := by
    change (decide (st.fg.h_max = st.fg.h_j + 1) && decide (∃ W ∈ st.fg.TF,
      (heightView p W).h = st.fg.h_max ∧ ¬ FGBlock.Preceq st.fg.J W)) = false
    refine Bool.and_eq_false_iff.mpr (Or.inr (decide_eq_false ?_))
    rintro ⟨W, _, _, hn⟩
    exact hn (hJ ▸ KitFG.genesis_preceq W)
  refine ⟨hmax, hj, hJ, hc, ?_⟩
  change (decide (st.fg.h_max = st.fg.h_j + 1) && !(R_at p c E rho i x).contest) = true
  rw [hc, hmax, hj]
  rfl

/-- Blueprint 21:1236–1237, 1467–1468; plan S20, H-PHASE r2/Q3.
DC: INTENTIONAL the first frontier rise to height two is an effective event.
This locates the rise if it occurs. It does not prove that the rise occurs. -/
theorem healing_phase_first_rise (hne : rho.honest.Nonempty) {n : Nat}
    (hn : 2 ≤ frontierAtIdx p c E rho n) :
    ∃ i, i < n ∧ frontierAtIdx p c E rho i = 1 ∧ 2 ≤ frontierAtIdx p c E rho (i + 1) ∧
      EffectiveEvent p c E rho i := by
  classical
  have hex : ∃ j, 2 ≤ frontierAtIdx p c E rho j := ⟨n, hn⟩
  have hj : 2 ≤ frontierAtIdx p c E rho (Nat.find hex) := Nat.find_spec hex
  have hjn : Nat.find hex ≤ n := Nat.find_min' hex hn
  have h0 := healing_phase_initial_frontier p c E rho hne
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := by
    cases hjc : Nat.find hex with
    | zero => rw [hjc, h0] at hj; omega
    | succ i => exact ⟨i, rfl⟩
  have hlt : ¬ 2 ≤ frontierAtIdx p c E rho i :=
    Nat.find_min hex (show i < Nat.find hex by rw [hi]; exact Nat.lt_succ_self i)
  obtain ⟨x, hx⟩ := hne
  have hlo : 1 ≤ frontierAtIdx p c E rho i := (boot_one_le_hmax p c E rho i x).trans
    (healing_phase_local_le_frontier p c E rho hx)
  have hi1 : frontierAtIdx p c E rho i = 1 :=
    le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hlt)) hlo
  rw [hi] at hj hjn
  exact ⟨i, hjn, hi1, hj, Or.inl (by rw [hi1]; exact hj)⟩

/-- Blueprint 21:1263–1279; plan S20, H-PHASE r2/Q3 (B3).
DC: INTENTIONAL an effective event after GST at frontier at least two starts a
raise attempt. The phase and served flag are read from the actual run. -/
theorem healing_attemptValid_of_event {i : Nat} {ev : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) (hgst : E.t_GST ≤ ev.time)
    (heff : EffectiveEvent p c E rho i) (hm : 2 ≤ frontierAtIdx p c E rho (i + 1)) :
    ∃ k : AttemptKey, k.start = i ∧ k.frontier = frontierAtIdx p c E rho (i + 1) ∧
      k.task = .raise ∧ AttemptValid p c E rho k := by
  classical
  let m := frontierAtIdx p c E rho (i + 1)
  have hphase : ∃ kind, AttemptPhaseAt p c E rho (i + 1) m kind := by
    by_cases hc : ContestEvidence p c E rho (i + 1) m
    · exact ⟨.contest, hc⟩
    · by_cases ht : TopEvidence p c E rho (i + 1) m
      · exact ⟨.topJ, ht, hc⟩
      · exact ⟨.gap, ht, hc⟩
  obtain ⟨kind, hkind⟩ := hphase
  refine ⟨⟨i, m, kind, .raise, decide (ServedFrontier p c E rho m ev.time)⟩,
    rfl, rfl, rfl, ev, hi, hgst, Or.inl heff, rfl, hm, hkind, decide_eq_true_iff, ?_⟩
  intro h
  cases h

end AvailableChain.FGSA.Run
end
