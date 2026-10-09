module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P1. DC: SAME global cache bound. -/
theorem healing_phase_local_le_frontier {i : Nat} {x : V} (hx : x ∈ rho.honest) :
    (storeAt p c E rho i x).fg.h_max ≤ frontierAtIdx p c E rho i := by
  change (storeAt p c E rho i x).fg.h_max ≤
    rho.honest.sup (fun x => (storeAt p c E rho i x).fg.h_max)
  exact Finset.le_sup (f := fun x => (storeAt p c E rho i x).fg.h_max) hx

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P1.
DC: SAME a top cache persists below a fixed global cap. Assembly supplies RMono. -/
theorem healing_phase_top_persist (mono : RMono p c E rho) (hnr : V2.D.NoRestart rho)
    {i j m : Nat} {x : V} (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx p c E rho j = m)
    (htop : (storeAt p c E rho i x).fg.h_j + 1 = m) :
    (storeAt p c E rho j x).fg.h_j + 1 = m ∧
      (storeAt p c E rho j x).fg.h_max = m := by
  have hlo := KitFG.fst_le_of_lexKey_le (mono hnr i j x hx hij).2.1
  have hhi := healing_phase_justified_lt p c E rho j x
  have hb := healing_phase_local_le_frontier p c E rho (i := j) hx
  (simp only [Height] at *; omega)

/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: SAME two equal-height entries on one path are equal.
At justified height zero both entries are genesis (B21, m = 1). -/
theorem healing_phase_entries_eq {C D W : FGBlock (Fin p.n)}
    (hh : (heightView p C).h_j = (heightView p D).h_j)
    (hC : FGBlock.Preceq (heightView p C).J W)
    (hD : FGBlock.Preceq (heightView p D).J W) :
    (heightView p C).J = (heightView p D).J := by
  exact KitFG.store_entries_eq p.E (heightView p) (finalityView p)
    (fgCertificateLaws p) (fgJustificationLaws p) hh hC hD

/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: INTENTIONAL a contest uses cumulative live evidence.
If the cached J changes, its old carrier supplies the off-J witness. -/
theorem healing_phase_contest_persist_of_crossing (crossing : RXing p c E rho)
    (mono : RMono p c E rho)
    (hnr : V2.D.NoRestart rho) {i j m : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx p c E rho j = m)
    (hH : (R_at p c E rho i x).H = m)
    (hcontest : (R_at p c E rho i x).contest = true) :
    (R_at p c E rho j x).H = m ∧ (R_at p c E rho j x).contest = true := by
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  change (decide (st.fg.h_max = st.fg.h_j + 1) && decide _) = true at hcontest
  obtain ⟨ht, he⟩ := Bool.and_eq_true_iff.mp hcontest
  have ht : st.fg.h_max = st.fg.h_j + 1 := of_decide_eq_true ht
  have he : ∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧ (heightView p W).h = st.fg.h_max ∧
      ¬ FGBlock.Preceq st.fg.J W := of_decide_eq_true he
  have htop : st.fg.h_j + 1 = m := ht.symm.trans hH
  obtain ⟨htop', hmax'⟩ := healing_phase_top_persist p c E rho mono hnr hx hij hcap htop
  refine ⟨hmax', ?_⟩
  change (decide (st'.fg.h_max = st'.fg.h_j + 1) && decide _) = true
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hmax'.trans htop'.symm), decide_eq_true ?_⟩
  have hsub := (fgsa_store_cumulative p c E rho hnr hij x).1
  by_cases hJ : st.fg.J = st'.fg.J
  · obtain ⟨W, hW, _hFW, hh, hn⟩ := he
    have hh' := hh.trans (hH.trans hmax'.symm)
    exact ⟨W, hsub hW,
      (healing_phase_frontier_root p c E rho crossing hx (hsub hW) hh').1,
      hh', hJ ▸ hn⟩
  · obtain ⟨C, hC, _, hjC, hJC⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.pair.1
    obtain ⟨D, _, _, hjD, hJD⟩ := (storeBundle_stateBefore E rho j x).cstore.fg.pair.1
    change st.fg.J = _ at hJC
    change st'.fg.J = _ at hJD
    change st.fg.h_j = _ at hjC
    change st'.fg.h_j = _ at hjD
    change st'.fg.h_j + 1 = m at htop'
    have hhC := (fgCertificateLaws p).height.justified_below_height C
    have hhCm := healing_phase_height_le p c E rho hC
    have hc : (heightView p C).h = st'.fg.h_max := by
      change st.fg.h_j = _ at hjC
      change (heightView p C).h ≤ st.fg.h_max at hhCm
      change st.fg.h_max = m at hH
      change st'.fg.h_max = m at hmax'
      (simp only [Height] at *; omega)
    refine ⟨C, hsub hC,
      (healing_phase_frontier_root p c E rho crossing hx (hsub hC) hc).1, hc, ?_⟩
    intro hDC
    apply hJ
    rw [hJC, hJD]
    apply healing_phase_entries_eq p (W := C)
    · (simp only [Height] at *; omega)
    · exact KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry C)
        ((fgCertificateLaws p).height.entry_preceq C)
    · exact hJD ▸ hDC

/-- Blueprint 21:1091–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: INTENTIONAL gap, top J, contest are the live cumulative phase bits.
This is the first frozen RPhase clause. Assembly supplies RMono. -/
theorem healing_phase_order_of_crossing (crossing : RXing p c E rho)
    (mono : RMono p c E rho) (hnr : V2.D.NoRestart rho)
    (a b m : Nat) (_hab : a ≤ b) (_hb : b ≤ rho.events.length) (_hm : 1 ≤ m)
    (hfixed : ∀ i, a ≤ i → i ≤ b → frontierAtIdx p c E rho i = m) :
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence p c E rho i m → TopEvidence p c E rho j m) ∧
      (ContestEvidence p c E rho i m → ContestEvidence p c E rho j m)) ∧
    (∀ i, a ≤ i → i ≤ b → ContestEvidence p c E rho i m → TopEvidence p c E rho i m) := by
  constructor
  · intro i j hai hij hjb
    have hcap := hfixed j (hai.trans hij) hjb
    constructor
    · rintro ⟨x, hx, ht⟩
      exact ⟨x, hx, (healing_phase_top_persist p c E rho mono hnr hx hij hcap ht).1⟩
    · rintro ⟨x, hx, hH, hc⟩
      exact ⟨x, hx, healing_phase_contest_persist_of_crossing
        p c E rho crossing mono hnr hx hij hcap hH hc⟩
  · rintro i _ _ ⟨x, hx, hH, hc⟩
    have ht : (storeAt p c E rho i x).fg.h_max = (storeAt p c E rho i x).fg.h_j + 1 :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    exact ⟨x, hx, ht.symm.trans hH⟩

end AvailableChain.FGSA.Run
end
