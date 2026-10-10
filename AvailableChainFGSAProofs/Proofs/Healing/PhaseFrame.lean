module
public import AvailableChainKitFG.StoreBounds
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSARun.Proofs.Reachable -- shake: keep (reach API)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4. DC: SAME cache height bound. -/
theorem healing_phase_height_le {i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) :
    (heightView p W).h ≤ (storeAt p c E rho i x).fg.h_max := by
  exact KitFG.store_height_le (heightView p) (finalityView p)
    (storeAt p c E rho i x).fg (storeBundle_stateBefore E rho i x).cstore.fg hW

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4. DC: SAME strict cache bound. -/
theorem healing_phase_justified_lt (i : Nat) (x : V) :
    (storeAt p c E rho i x).fg.h_j < (storeAt p c E rho i x).fg.h_max := by
  exact KitFG.store_justified_lt p.E (heightView p) (finalityView p)
    (fgCertificateLaws p) (storeAt p c E rho i x).fg
    (storeBundle_stateBefore E rho i x).cstore.fg

/-- Blueprint 21:1222–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL the bound reads the accepted W certificate, not the block F. -/
theorem healing_phase_finality_le {i : Nat} {x : V} {K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF)
    (hF : (finalityView p K).F = (storeAt p c E rho i x).fg.F) :
    (finalityView p K).h_F ≤ (storeAt p c E rho i x).fg.h_j := by
  exact KitFG.store_finality_le p.E (heightView p) (finalityView p)
    (fgCertificateLaws p) (storeAt p c E rho i x).fg
    (storeBundle_stateBefore E rho i x).cstore.fg hK hF

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4.
DC: SAME a nonempty cumulative store attains its frontier, including height one. -/
theorem healing_phase_frontier_witness (i : Nat) (x : V) :
    ∃ W ∈ (storeAt p c E rho i x).fg.TF,
      (heightView p W).h = (storeAt p c E rho i x).fg.h_max := by
  exact KitFG.store_frontier_witness p.E (heightView p) (finalityView p)
    (fgCertificateLaws p) (storeAt p c E rho i x).fg
    (storeBundle_stateBefore E rho i x).cstore.fg

/-- Blueprint 21:1153–1171, 1200–1209; plan S20, H-PHASE/P5.
DC: INTENTIONAL live controls and accepted W finality carrier.
Assembly supplies RXing from the foundation final-lock producer. -/
theorem healing_phase_frontier_root (crossing : RXing p c E rho)
    {i : Nat} {x : V} {B : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hB : B ∈ (storeAt p c E rho i x).fg.TF)
    (hh : (heightView p B).h = (R_at p c E rho i x).H) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F B ∧
      FGBlock.Preceq (R_at p c E rho i x).Z B := by
  let st := storeAt p c E rho i x
  obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.Fcar
  have hlt := (healing_phase_finality_le p c E rho hK hKF).trans_lt
    (healing_phase_justified_lt p c E rho i x)
  have hFB : FGBlock.Preceq st.fg.F B := crossing i i x x K B hx le_rfl hK hKF
    ⟨hx, hB⟩ (hlt.trans_eq hh.symm)
  refine ⟨hFB, ?_⟩
  change FGBlock.Preceq (FGSA.controls p st).Z B
  unfold Controls.Z
  split
  · rename_i hroot
    have hr := Bool.and_eq_true_iff.mp hroot
    have ht : st.fg.h_max = st.fg.h_j + 1 := of_decide_eq_true hr.1
    have hn : (FGSA.controls p st).contest = false := by
      simpa using congrArg Bool.not hr.2
    by_contra hnot
    have hc : (FGSA.controls p st).contest = true := by
      change (decide (st.fg.h_max = st.fg.h_j + 1) && decide _) = true
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ht, decide_eq_true ⟨B, hB, hFB, hh, hnot⟩⟩
    rw [hn] at hc
    contradiction
  · exact hFB

/-- Blueprint 21:1153–1171, 1200–1209; plan S20, H-PHASE/P5.
DC: INTENTIONAL membership uses the supplied view and the live controls.
This proves the fifth frozen RPhase clause; its path premise is not needed. -/
theorem healing_frontier_mem (crossing : RXing p c E rho)
    (i : Nat) (x : V) (m : Nat) (X : Finset (FGBlock (Fin p.n))) (B : FGBlock (Fin p.n))
    (hx : x ∈ rho.honest) (_hi : i ≤ rho.events.length) (_hm : 1 ≤ m)
    (hH : (R_at p c E rho i x).H = m) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (hB : B ∈ X) (_hpath : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hh : (heightView p B).h = m) :
    FGBlock.Preceq (R_at p c E rho i x).Z B ∧ B ∈ D_at p c E rho i x X := by
  obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx (hX hB) (hh.trans hH.symm)
  refine ⟨hZ, (KitFG.mem_filteredFromView _ _ _ _).mpr ⟨hB, hF, hZ, B, hB,
    KitFG.preceq_refl B, ?_⟩⟩
  change (if (R_at p c E rho i x).contest then (R_at p c E rho i x).H
    else (R_at p c E rho i x).H - 1) ≤ (heightView p B).h
  rw [hH, hh]
  split <;> (simp only [Height] at *; omega)

/-- Blueprint 21:1193–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL the frame includes a W certificate below its floor.
This local form does not require a settlement time or a height-two bootstrap. -/
theorem healing_phase_frame (crossing : RXing p c E rho)
    {i : Nat} {x : V} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hx : x ∈ rho.honest) (hm : 1 ≤ m)
    (hH : (R_at p c E rho i x).H = m)
    (hc : (R_at p c E rho i x).contest = contested)
    (hr : match J with
      | some B => (R_at p c E rho i x).rootIsJ = true ∧ (R_at p c E rho i x).J = B
      | none => (R_at p c E rho i x).rootIsJ = false) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  let st := storeAt p c E rho i x
  have hj := healing_phase_justified_lt p c E rho i x
  change st.fg.h_max = m at hH
  change (controls p st).contest = contested at hc
  change st.fg.h_j < st.fg.h_max at hj
  refine ⟨hH, hc, ?_, ?_, ?_⟩
  · change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) = _
    rw [hc, hH]
  · cases J with
    | some B =>
      change (controls p st).rootIsJ = true ∧ (controls p st).J = B at hr
      obtain ⟨hr, hJ⟩ := hr
      have hb := Bool.and_eq_true_iff.mp hr
      have ht : st.fg.h_max = st.fg.h_j + 1 := of_decide_eq_true hb.1
      have hn : (FGSA.controls p st).contest = false := by
        simpa using congrArg Bool.not hb.2
      refine ⟨hr, hJ, ?_, ?_, hc.symm.trans hn, ?_⟩
      · change (if (FGSA.controls p st).rootIsJ then _ else _) = B
        rw [hr]
        exact hJ
      · change st.fg.h_j + 1 = m
        (simp only [Height] at *; omega)
      · exact hJ ▸ (storeBundle_stateBefore E rho i x).cstore.fg.FJ
    | none =>
      change (controls p st).rootIsJ = false at hr
      have hZ : (FGSA.controls p st).Z = st.fg.F := by
        change (if (FGSA.controls p st).rootIsJ then _ else _) = _
        rw [hr]
        rfl
      have hcases : (contested = false ∧ st.fg.h_j + 2 ≤ m) ∨
          (contested = true ∧ st.fg.h_j + 1 = m) := by
        cases he : contested with
        | true =>
          have ht : st.fg.h_max = st.fg.h_j + 1 :=
            of_decide_eq_true (Bool.and_eq_true_iff.mp (hc.trans he)).1
          exact Or.inr ⟨rfl, ht.symm.trans hH⟩
        | false =>
          left
          refine ⟨rfl, ?_⟩
          by_contra hnot
          have ht : st.fg.h_max = st.fg.h_j + 1 := by (simp only [Height] at *; omega)
          have hrt : (FGSA.controls p st).rootIsJ = true := by
            change (decide (st.fg.h_max = st.fg.h_j + 1) &&
              !(FGSA.controls p st).contest) = true
            rw [hc, he]
            simp only [ht, decide_true, Bool.not_false, Bool.and_self]
          rw [hr] at hrt
          contradiction
      refine ⟨hr, hZ, ?_, hcases⟩
      obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.Fcar
      refine ⟨K, hK, hKF, ?_⟩
      have hf := healing_phase_finality_le p c E rho hK hKF
      change (finalityView p K).h_F ≤ st.fg.h_j at hf
      change (finalityView p K).h_F <
        (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1)
      rw [hc]
      rcases hcases with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> (simp only [Height] at *; omega)
  · obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho i x
    exact ⟨W, hW, hh.trans hH,
      (healing_phase_frontier_root p c E rho crossing hx hW hh).2⟩

/-- Blueprint 21:1193–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL live settled frame with an accepted finality carrier.
This is the fourth frozen RPhase clause. Assembly supplies RXing. -/
theorem healing_settled_frame (crossing : RXing p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (_hgst : E.t_GST ≤ u) (hp : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  have hui' : V2.D.Run.idxBefore rho u ≤ i := (idxBefore_le_timeIdx rho u).trans hui
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 i x hui' hiv hx
  exact healing_phase_frame p c E rho crossing hx hp.2.2.1 hH hc hr

/-- The fourth RPhase clause uses the joined healing phase domain. -/
theorem healing_settled_frame_ready (crossing : RXing p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (_hready : recoveryStart p E ≤ u) (hp : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  have hui' : V2.D.Run.idxBefore rho u ≤ i := (idxBefore_le_timeIdx rho u).trans hui
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 i x hui' hiv hx
  exact healing_phase_frame p c E rho crossing hx hp.2.2.1 hH hc hr

end AvailableChain.FGSA.Run
end
