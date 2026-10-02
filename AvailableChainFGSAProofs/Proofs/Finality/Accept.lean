module
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSARun.Proofs.Reachable

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- DC: INTENTIONAL window height projection, using the owner's equations. -/
private theorem accept_height (W : FGBlock (Fin p.n)) :
    heightView p W = Window.projectHeight (Window.derive p p.K_W W) :=
  heightView_def p W

/-- DC: INTENTIONAL window finality projection, using the owner's equations. -/
private theorem accept_finality (W : FGBlock (Fin p.n)) :
    (finalityView p W).F = (Window.derive p p.K_W W).F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def]

/-- DC: SAME entry comparison on one path; FG-SA uses the window height view. -/
private theorem accept_J_path (st : Store (Fin p.n))
    (hI : KitFG.FGStoreInvariant (heightView p) (finalityView p) st)
    (W : FGBlock (Fin p.n)) (hpath : FGBlock.Preceq st.J W) :
    FGBlock.Preceq (heightView p W).J st.J ∨ st.h_j < (heightView p W).h_j := by
  have hH := (fgCertificateLaws p).height
  have hJ := fgJustificationLaws p
  have hJW := KitFG.preceq_trans (hH.justified_preceq_entry W) (hH.entry_preceq W)
  rcases KitFG.preceq_total_of_common hJW hpath with h | h
  · exact Or.inl h
  by_cases hz : (heightView p W).h_j = 0
  · exact Or.inl (hJ.J_zero W hz ▸ KitFG.genesis_preceq st.J)
  by_cases hs : st.h_j = 0
  · right
    rw [hs]
    exact Nat.pos_of_ne_zero hz
  obtain ⟨C, _, _, hc, he⟩ := hI.pair.1
  have hsh : (heightView p st.J).h = st.h_j := by
    rw [he, hJ.J_height C (fun h => hs (hc.trans h)), ← hc]
  have hwh := hJ.J_height W hz
  have hle := hH.h_mono h
  rw [hsh, hwh] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  left
  have hp := hH.entry_plateau h (hsh.trans (heq.trans hwh.symm))
  rw [he, hJ.J_entry C, hJ.J_entry W] at hp
  rw [he, hp]
  exact KitFG.preceq_refl _

/-- DC: INTENTIONAL selected handler guards accept the window finality. -/
private theorem accept_update (st : Store (Fin p.n))
    (hI : KitFG.FGStoreInvariant (heightView p) (finalityView p) st)
    (W : FGBlock (Fin p.n))
    (hF : FGBlock.Preceq st.F (Window.derive p p.K_W W).F)
    (hmem : (Window.derive p p.K_W W).F ∈ insert W st.TF)
    (hj : FGBlock.Preceq st.J W ∨ st.h_j < (Window.derive p p.K_W W).h_j)
    (hcap : max st.h_max ((heightView p W).h) ≤ (heightView p W).h + 1) :
    FGBlock.Preceq (Window.derive p p.K_W W).F
      (Window.update_finality p p.K_W { st with TF := insert W st.TF } W).F := by
  classical
  have hheight := accept_height p W
  have hσJ : FGBlock.Preceq (Window.derive p p.K_W W).F
      (Window.derive p p.K_W W).J := Window.window_F_preceq_J p p.K_W p.kWLarge W
  have hFJ := KitFG.preceq_trans hF hσJ
  have hj' : FGBlock.Preceq (Window.derive p p.K_W W).J st.J ∨
      st.h_j < (Window.derive p p.K_W W).h_j := by
    rcases hj with hj | hj
    · simpa only [hheight, Window.projectHeight_def] using accept_J_path p st hI W hj
    · exact Or.inr hj
  have hread : (heightView p W).h = (Window.derive p p.K_W W).h := by
    rw [hheight, Window.projectHeight_def]
  have hJW : FGBlock.Preceq (Window.derive p p.K_W W).J W := by
    simpa only [hheight, Window.projectHeight_def] using
      KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry W)
        ((fgCertificateLaws p).height.entry_preceq W)
  let st1 : Store (Fin p.n) :=
    { st with TF := insert W st.TF, h_max := max st.h_max ((heightView p W).h) }
  let st2 := if FGBlock.preceq st.F (Window.derive p p.K_W W).J &&
      decide (lexKey (st.h_j, st.J) <
        lexKey ((Window.derive p p.K_W W).h_j, (Window.derive p p.K_W W).J))
    then { st1 with
      J := (Window.derive p p.K_W W).J
      h_j := (Window.derive p p.K_W W).h_j } else st1
  have h2F : st2.F = st.F := by dsimp only [st2]; split_ifs <;> rfl
  have h2T : st2.TF = insert W st.TF := by dsimp only [st2]; split_ifs <;> rfl
  have h2H : st2.h_max = max st.h_max ((heightView p W).h) := by
    dsimp only [st2]; split_ifs <;> rfl
  have h2J : FGBlock.Preceq (Window.derive p p.K_W W).F st2.J := by
    dsimp only [st2]
    split_ifs with hu
    · exact hσJ
    · rcases hj' with hj | hj
      · exact KitFG.preceq_trans hσJ hj
      · exfalso
        apply hu
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hFJ, Prod.Lex.left _ _ hj⟩
  have hv : (Window.derive p p.K_W W).F ∈ Window.acceptViable p p.K_W st2 := by
    rw [Window.acceptViable_def]
    apply Finset.mem_filter.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h2T.symm ▸ hmem, ?_, ?_⟩
    · exact h2F.symm ▸ hF
    · refine ⟨W, h2T.symm ▸ Finset.mem_insert_self _ _, KitFG.preceq_trans hσJ hJW, ?_⟩
      rw [h2H, ← hread]
      simp only [Height] at hcap ⊢
      omega
  rw [Window.update_finality_def]
  change FGBlock.Preceq (Window.derive p p.K_W W).F
    (if FGBlock.preceq st2.F (Window.derive p p.K_W W).F &&
      decide (st2.F ≠ (Window.derive p p.K_W W).F) &&
      FGBlock.preceq (Window.derive p p.K_W W).F st2.J &&
      decide ((Window.derive p p.K_W W).F ∈ Window.acceptViable p p.K_W st2)
    then { st2 with F := (Window.derive p p.K_W W).F } else st2).F
  by_cases he : st2.F = (Window.derive p p.K_W W).F
  · simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
      Bool.false_and]
    rw [ite_eq_right (by decide)]
    exact he.symm ▸ KitFG.preceq_refl _
  · have ht : (FGBlock.preceq st2.F (Window.derive p p.K_W W).F &&
        decide (st2.F ≠ (Window.derive p p.K_W W).F) &&
        FGBlock.preceq (Window.derive p p.K_W W).F st2.J &&
        decide ((Window.derive p p.K_W W).F ∈ Window.acceptViable p p.K_W st2)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨h2F.symm ▸ hF, he⟩, h2J⟩, hv⟩
    rw [ht, ite_eq_left rfl]
    exact KitFG.preceq_refl _

variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- DC: INTENTIONAL actual receipt and ancestor-closed inserted tree. -/
private theorem accept_ready (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (t : Time)
    (hr : Ready_W p c E rho i x W t) :
    (storeAt p c E rho (i + 1) x).fg =
      Window.update_finality p p.K_W
        { (storeAt p c E rho i x).fg with TF := insert W (storeAt p c E rho i x).fg.TF } W ∧
    (Window.derive p p.K_W W).F ∈ insert W (storeAt p c E rho i x).fg.TF := by
  classical
  rw [Ready_W_def] at hr
  obtain ⟨o, s, raw, support, rows, P, he, hd, hp, ha, hw⟩ := hr
  let st := storeAt p c E rho i x
  have hI : CStoreInv p st := cstoreInv_stateBefore E rho i x
  have hPT := ((parentFG_spec st hI.rootInj (eraseFG W) P).mp hp).1
  have hparent : W.parent = P := by rw [← hw, fgBlock_parent]
  have hclosed : ∀ B ∈ insert W st.fg.TF, B.parent ∈ insert W st.fg.TF := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Finset.mem_insert_of_mem (hparent ▸ hPT)
    · exact Finset.mem_insert_of_mem (hI.fg.closed B hB)
  have hFW : FGBlock.Preceq (Window.derive p p.K_W W).F W := by
    rw [← accept_finality p W]
    exact KitFG.preceq_trans ((fgCertificateLaws p).finalized_preceq_justified W)
      (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry W)
        ((fgCertificateLaws p).height.entry_preceq W))
  refine ⟨?_, KitFG.ancestor_closed_of_parent_closed _ hclosed W
    (Finset.mem_insert_self _ _) _ hFW⟩
  have hstep : storeAt p c E rho (i + 1) x = FGSA.process p st (toWire p o) := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho he]
    simp only [V2.D.World.step, Function.update_self]
    rfl
  rw [hstep]
  change (match (toWire p o).decode with
    | some (.vote r j b) => admitHead p st r j b
    | some (.row _ body) => admitRow p st ⟨(toWire p o).auth, body⟩
    | some (.block r b raw sup rows) => admitBlock p st r b raw sup rows
    | none => st).fg = _
  rw [hd]
  dsimp only
  obtain ⟨pool, hpool, _⟩ := admitBlock_accepted_eq p st s (eraseFG W) raw support P rows hp ha
  rw [hpool]
  dsimp only
  split_ifs
  · rw [fg_on_block_accepts p st s (eraseFG W) P rows hp ha, hw]
  · rw [reconcile_fg, fg_on_block_accepts p st s (eraseFG W) P rows hp ha, hw]

/-- DC-CS/W4FKChainSecondCheckpoint.lean:43 (W4CommonFinalityAtConfirmationPin).
INTENTIONAL: FG-SA uses the selected W receipt and a strict supplied deadline. -/
theorem fgsa_acceptBefore_W : AcceptBefore_W p := by
  rw [AcceptBefore_W_def]
  intro V _ _ In c E rho W K a₀ d h x hx
  classical
  let w := h.deliver.selected x hx
  obtain ⟨htime, hbefore, hreceipt⟩ := h.deliver.witness x hx
  have hcover : FGBlock.Preceq K (storeAt p c E rho (w.index + 1) x).fg.F := by
    rcases hreceipt with hc | ⟨_, hr⟩
    · exact hc
    by_cases hc : FGBlock.Preceq K (storeAt p c E rho w.index x).fg.F
    · exact KitFG.preceq_trans hc
        (by
          obtain ⟨he, _⟩ := accept_ready p c E rho w.index x W w.time hr
          rw [he]
          rcases Window.window_update_finality_F_cases p p.K_W
            { (storeAt p c E rho w.index x).fg with
              TF := insert W (storeAt p c E rho w.index x).fg.TF } W with hs | ⟨hf, _, _, hn⟩
          · rw [hs]
            exact KitFG.preceq_refl _
          · rw [hn]
            exact hf)
    have hf : FGBlock.Preceq (storeAt p c E rho w.index x).fg.F K :=
      (h.guards.finCmp x hx hr).resolve_right hc
    obtain ⟨he, hm⟩ := accept_ready p c E rho w.index x W w.time hr
    rw [he]
    apply KitFG.preceq_trans h.finalized
    apply accept_update p _ (cstoreInv_stateBefore E rho w.index x).fg W
      (KitFG.preceq_trans hf h.finalized) hm (h.guards.jPath x hx hr hc)
    have hcap := h.guards.cap x hx hr hc
    rw [receiptInsert_W_def] at hcap
    exact hcap
  apply acceptsFinalBefore_of_idx p c E rho h.base.noRestart h.base.valid.toScheduleWellFormed
  change Option.map V2.Event.time rho.events[w.index]? = some w.time at htime
  obtain ⟨e, he, het⟩ := Option.map_eq_some_iff.mp htime
  obtain ⟨hi, hie⟩ := List.getElem?_eq_some_iff.mp he
  refine ⟨w.index + 1, by omega, ?_, hcover⟩
  intro k hk
  have hki : k ≤ w.index := by omega
  have hkl : k < rho.events.length := lt_of_le_of_lt hki hi
  refine ⟨rho.events[k], List.getElem?_eq_getElem hkl, ?_⟩
  apply lt_of_le_of_lt (b := w.time) _ hbefore
  by_cases hke : k = w.index
  · subst k
    rw [hie]
    exact le_of_eq het
  · have hkey := (List.pairwise_iff_getElem.mp h.base.valid.sorted)
      k w.index hkl hi (by omega)
    have ht := V2.D.Engine.time_le_of_key_le _ _ hkey
    rw [hie, het] at ht
    exact ht

/-- DC-CS/W4FKChainFinalityWrite.lean:177 followed by acceptance at :43.
INTENTIONAL: the existing adapter uses the same selected receipt and strict deadline.
Conditional on FinalizePrem_W.deliver; not a deadline result. -/
theorem fgsa_finalizePending_W (ΔF : Time) : FinalizePending_W p ΔF :=
  finalizePending_of_acceptBefore_W p ΔF (fgsa_acceptBefore_W p)

end AvailableChain.FGSA.Run
end
