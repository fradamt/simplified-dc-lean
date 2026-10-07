module
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainKitFG.StoreBounds

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; the scoped contest conclusion covers
all maximum-height carriers, including those that extend J. -/
theorem outageV_contest_top (p : Params) (st : State p.n) (B : FGBlock (Fin p.n))
    (hBJ : FGBlock.Preceq B (FGSA.controls p st).J)
    (hother : ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H →
      ¬ FGBlock.Preceq (FGSA.controls p st).J W → FGBlock.Preceq B W) :
    ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H →
      FGBlock.Preceq B W := by
  intro W hW hh
  by_cases hJ : FGBlock.Preceq (FGSA.controls p st).J W
  · exact preceq_trans hBJ hJ
  · exact hother W hW hh hJ

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; a contested filter over any subset
of the full store contains only blocks compatible with B. -/
theorem outageV_contested_filter (p : Params) (st : State p.n)
    (hinv : CStoreInv p st) (B : FGBlock (Fin p.n))
    (htop : ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H →
      FGBlock.Preceq B W)
    (hcontest : (FGSA.controls p st).contest = true)
    (view : Finset (FGBlock (Fin p.n))) (hview : view ⊆ st.fg.TF)
    {X : FGBlock (Fin p.n)}
    (hX : X ∈ KitFG.filteredFromView (heightView p) (FGSA.controls p st) view) :
    FGBlock.Preceq X B ∨ FGBlock.Preceq B X := by
  obtain ⟨_, _, _, W, hW, hXW, hlo⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) view X).mp hX
  have he : (FGSA.controls p st).lo = (FGSA.controls p st).H := by
    change (if (FGSA.controls p st).contest then (FGSA.controls p st).H
      else (FGSA.controls p st).H - 1) = _
    rw [hcontest]
    rfl
  rw [he] at hlo
  have hhi := KitFG.store_height_le (heightView p) (finalityView p) st.fg hinv.fg (hview hW)
  have hh : (heightView p W).h = (FGSA.controls p st).H := Nat.le_antisymm hhi hlo
  exact preceq_total_of_common hXW (htop W (hview hW) hh)

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; a compatible entry at least as high
as a retained entry Q above B must itself extend B. -/
theorem outageV_entry_above (p : Params) {B Q X : FGBlock (Fin p.n)}
    (hBQ : FGBlock.Preceq B Q) (hQ : (heightView p Q).T_h = Q)
    (hX : (heightView p X).T_h = X) (hh : (heightView p Q).h ≤ (heightView p X).h)
    (hcompat : FGBlock.Preceq X B ∨ FGBlock.Preceq B X) :
    FGBlock.Preceq B X := by
  rcases hcompat with hXB | hBX
  · have hXQ := preceq_trans hXB hBQ
    have he := (fgCertificateLaws p).height.entry_plateau hXQ
      (Nat.le_antisymm ((fgCertificateLaws p).height.h_mono hXQ) hh)
    rw [hX, hQ] at he
    exact he.symm ▸ hBQ
  · exact hBX

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; every taller carrier extends B
when its crossed entries are compatible with B. Progress crossings suffice. -/
theorem outageV_taller_carrier (p : Params) {B Q W : FGBlock (Fin p.n)}
    (hBQ : FGBlock.Preceq B Q) (hQ : (heightView p Q).T_h = Q)
    (hh : (heightView p Q).h < (heightView p W).h)
    (hcross : ∀ U, FGBlock.Preceq U W → (heightView p U).h < (heightView p W).h →
      FGBlock.Preceq (heightView p U).T_h B ∨ FGBlock.Preceq B (heightView p U).T_h) :
    FGBlock.Preceq B W := by
  have H := (fgCertificateLaws p).height
  obtain ⟨U, hUW, hU, _⟩ := H.height_crossing W (heightView p Q).h (H.one_le_h Q) hh
  have hBU := outageV_entry_above p hBQ hQ (H.entry_idem U)
    (by rw [H.entry_same_height, hU]) (hcross U hUW (hU ▸ hh))
  exact preceq_trans hBU (preceq_trans (H.entry_preceq U) hUW)

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; receipt of a carrier raises the
selected justified height when its entry remains above F. -/
theorem outageV_received_height (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {P : FGBlock (Fin p.n)} (hP : P ∈ st.fg.TF)
    (hFP : FGBlock.Preceq st.fg.F (heightView p P).J) :
    (heightView p P).h_j ≤ st.fg.h_j :=
  KitFG.fst_le_of_lexKey_le (hinv.fg.pair.2 P hP hFP)

/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; a contest supplies an actual stored
carrier at height j+1 with a nonzero justified entry. -/
theorem outageV_contest_carrier (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    (ht : (FGSA.controls p st).contest = true) :
    st.fg.h_j ≠ 0 ∧ ∃ P ∈ st.fg.TF,
      (heightView p P).h_j = st.fg.h_j ∧ (heightView p P).J = st.fg.J ∧
      (heightView p P).h = st.fg.h_j + 1 := by
  change (decide (st.fg.h_max = st.fg.h_j + 1) &&
    decide (∃ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max ∧
      ¬ FGBlock.Preceq st.fg.J W)) = true at ht
  obtain ⟨htop, W, _, _, hnW⟩ :=
    (show st.fg.h_max = st.fg.h_j + 1 ∧
      ∃ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max ∧ ¬ FGBlock.Preceq st.fg.J W by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht)
  obtain ⟨P, hP, _, hj, hJ⟩ := hinv.fg.pair.1
  have hn : st.fg.h_j ≠ 0 := by
    intro hz
    have hzero := (fgJustificationLaws p).J_zero P (hj.symm.trans hz)
    exact hnW ((hJ.trans hzero).symm ▸ genesis_preceq W)
  refine ⟨hn, P, hP, hj.symm, hJ.symm, ?_⟩
  have hlo := (fgCertificateLaws p).height.justified_below_height P
  have hhi := store_height_le (heightView p) (finalityView p) st.fg hinv.fg hP
  rw [← hj] at hlo
  rw [htop] at hhi
  change (_ : Nat) < _ at hlo
  change (_ : Nat) ≤ _ at hhi
  change (_ : Nat) = _
  omega

/-- OUTPUT-DIRECT §5. DC: INTENTIONAL; after the marker is received,
either the FG root covers B or every filtered block is compatible with B.
The view may be any subset of the cumulative store. -/
theorem outageV_marker_frame (p : Params) (st : State p.n) (hinv : CStoreInv p st)
    {B Q : FGBlock (Fin p.n)} (hBQ : FGBlock.Preceq B Q)
    (hQ : (heightView p Q).T_h = Q) (hmark : (heightView p Q).h ≤ st.fg.h_j)
    (hJcomp : FGBlock.Preceq st.fg.J B ∨ FGBlock.Preceq B st.fg.J)
    (htop : (FGSA.controls p st).contest = true →
      ∀ W ∈ st.fg.TF, (heightView p W).h = (FGSA.controls p st).H → FGBlock.Preceq B W)
    (hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      (heightView p U).h < (heightView p W).h →
      FGBlock.Preceq (heightView p U).T_h B ∨ FGBlock.Preceq B (heightView p U).T_h)
    (view : Finset (FGBlock (Fin p.n))) (hview : view ⊆ st.fg.TF) :
    FGBlock.Preceq B (FGSA.controls p st).Z ∨
      ∀ X ∈ KitFG.filteredFromView (heightView p) (FGSA.controls p st) view,
        FGBlock.Preceq X B ∨ FGBlock.Preceq B X := by
  by_cases ht : (FGSA.controls p st).contest = true
  · exact Or.inr (fun _ hX => outageV_contested_filter p st hinv B (htop ht) ht view hview hX)
  have hn : (FGSA.controls p st).contest = false := Bool.eq_false_iff.mpr ht
  by_cases hnext : st.fg.h_max = st.fg.h_j + 1
  · obtain ⟨P, _, _, hheight, hentry⟩ := hinv.fg.pair.1
    have hnonzero : (heightView p P).h_j ≠ 0 := by
      have hpos := (fgCertificateLaws p).height.one_le_h Q
      change (1 : Nat) ≤ _ at hpos
      change (_ : Nat) ≤ _ at hmark
      change (_ : Nat) = _ at hheight
      change (_ : Nat) ≠ 0
      omega
    have hJ : (heightView p st.fg.J).T_h = st.fg.J := by
      rw [hentry]
      exact (fgJustificationLaws p).J_entry P
    have hhJ : (heightView p st.fg.J).h = st.fg.h_j := by
      rw [hentry, (fgJustificationLaws p).J_height P hnonzero]
      exact hheight.symm
    have hBJ := outageV_entry_above p hBQ hQ hJ (hhJ.symm ▸ hmark) hJcomp
    have hr : (FGSA.controls p st).rootIsJ = true := by
      change (decide (st.fg.h_max = st.fg.h_j + 1) && !(FGSA.controls p st).contest) = true
      simp only [hnext, hn, decide_true, Bool.not_false, Bool.and_self]
    left
    change FGBlock.Preceq B
      (if (FGSA.controls p st).rootIsJ then st.fg.J else st.fg.F)
    rw [hr]
    exact hBJ
  · right
    intro X hX
    obtain ⟨_, _, _, W, hW, hXW, hlo⟩ :=
      (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) view X).mp hX
    have hfloor : (FGSA.controls p st).lo = st.fg.h_max - 1 := by
      change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) = _
      rw [hn]
      rfl
    rw [hfloor] at hlo
    have hlt := KitFG.store_justified_lt p.E (heightView p) (finalityView p)
      (fgCertificateLaws p) st.fg hinv.fg
    have hhigh : (heightView p Q).h < (heightView p W).h := by
      change (_ : Nat) < _ at hlt ⊢
      change (_ : Nat) ≤ _ at hlo hmark
      change ¬ ((_ : Nat) = _) at hnext
      omega
    exact preceq_total_of_common hXW
      (outageV_taller_carrier p hBQ hQ hhigh (hcross W (hview hW)))

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; instantiate the subset result at
an actual honest event cut from scoped original row provenance. -/
theorem outageV_contested_frame_from_rows {p : Params} {In V : Type}
    [DecidableEq V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hstore : RStore p c E rho)
    (hframe : RFrameExact p c E rho) (hstrat : RStrat p c E rho)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (hx : x ∈ rho.honest)
    (hrows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) →
      FGBlock.Preceq e B ∨ FGBlock.Preceq B e)
    (hcontest : (R_at p c E rho i x).contest = true)
    (view : Finset (FGBlock (Fin p.n))) (hview : view ⊆ (storeAt p c E rho i x).fg.TF)
    {X : FGBlock (Fin p.n)}
    (hX : X ∈ KitFG.filteredFromView (heightView p) (R_at p c E rho i x) view) :
    FGBlock.Preceq X B ∨ FGBlock.Preceq B X := by
  have hc := (cpCompat_of_scopedFrame p c E rho hstore hframe hstrat i x B hx hrows).2.2.2.2
    hcontest
  exact outageV_contested_filter p (storeAt p c E rho i x) (hstore i x hx).1 B
    (outageV_contest_top p _ B hc.1 hc.2) hcontest view hview hX

end AvailableChain.FGSA.Run
end
