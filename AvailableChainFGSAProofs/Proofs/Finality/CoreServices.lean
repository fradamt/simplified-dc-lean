module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSA.Proofs.Head.Walk
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 01:137–140,166–182; 22 I5:538–581. Class (iii).
DC b241081: INTENTIONAL: the FG-SA live root selects a live lease in the
FJ filtered tree, or the active root Z. The reachable lease bound supplies output. -/
theorem fgsa_tStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    TStart p c E rho := by
  constructor
  · intro i x hx row hr ht
    exact leaseBelowOutput_honest E rho i x hx row hr ht
  · intro i x _
    let st := storeAt p c E rho i x
    change liveRoot p st = _ ∨ _
    unfold liveRoot
    dsimp only
    rcases foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
        (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
    · exact Or.inl he
    · obtain ⟨row, hr, hrow⟩ := List.mem_filterMap.mp hm
      split at hrow
      · next hc =>
        obtain ⟨ht, hb⟩ := Bool.and_eq_true_iff.mp hc
        have ht := of_decide_eq_true ht
        have hb := of_decide_eq_true hb
        refine Or.inr ⟨row, hr, ht, (Option.some.inj hrow), hb, ?_⟩
        exact leaseBelowOutput_stateBefore E rho i x row hr ht
      · cases hrow

private theorem core_lift_prefix {n : Nat} (B : FGBlock (Fin n)) (a : Block)
    (ha : Block.Preceq a (eraseFG B)) :
    ∃ A, FGBlock.Preceq A B ∧ eraseFG A = a := by
  induction B with
  | genesis =>
      have he : a = .genesis := by simpa [eraseFG, Block.Preceq, Block.preceq] using ha
      exact ⟨.genesis, KitFG.preceq_refl _, he.symm⟩
  | node P s r rs ih =>
      change (decide (a = eraseFG (.node P s r rs)) || Block.preceq a (eraseFG P)) = true at ha
      rcases Bool.or_eq_true_iff.mp ha with he | hp
      · exact ⟨.node P s r rs, KitFG.preceq_refl _, (of_decide_eq_true he).symm⟩
      · obtain ⟨A, hA, he⟩ := ih hp
        exact ⟨A, KitFG.preceq_trans hA (KitFG.preceq_parent_node _ _ _ _), he⟩

private theorem core_full_mem (st : State p.n) (B : FGBlock (Fin p.n)) :
    B ∈ fullTree p st ↔ B ∈ st.fg.TF ∧ FGBlock.Preceq (controls p st).F B ∧
      FGBlock.Preceq (controls p st).Z B ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq B W ∧ (controls p st).lo ≤ (heightView p W).h :=
  KitFG.mem_filteredFromView (heightView p) (controls p st) st.fg.TF B

/-- Blueprint 01:158–164,184–199; 22 I8:637. Class (iii).
DC b241081: Protocol/ForkChoice/Goldfish/Adoption.lean:415 and
Protocol/ForkChoice/Goldfish/Walk.lean:184,197,433.
INTENTIONAL: the FJ tree and live root supply the path; Batch supplies the
score bounds. An unsupported path block can use only the slot or low-parent arm. -/
theorem fgsa_tWalk (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    TWalk p c E rho := by
  intro i x s raw support Q seats m hx hb st hQ hanchor hwalk
  obtain ⟨hsub, hlabel, hseats, hother, hclean⟩ := hwalk
  have hi : CStoreInv p st := cstoreInv_stateBefore E rho i x
  have hQT := ((core_full_mem st Q).mp hQ).1
  have hinj := viewRootInj_TF p st hi
  have hbatch : ∀ a ∈ seats, Gen.AC.poolSupports st.base.blocks support a (eraseFG Q) = true := by
    intro a ha
    obtain ⟨_, o, ho, hor, hseat, H, ht, hH, hs, hQH⟩ := hseats a ha
    apply (Gen.AC.vote_pool_support_witness _ _ _ _).mpr
    refine ⟨o, ho, hseat, ?_⟩
    rw [Gen.AC.voteSupports_def, ht]
    simp only [hH, hlabel o hor, Option.getD_some, hs, decide_true, Bool.true_and]
    exact hQH
  obtain ⟨_, _, hpath, hconflict, hunsupported⟩ := Gen.AC.batch_counts
    st.base.blocks raw raw support seats seats.card m (eraseFG Q)
    (fun _ ho => ho) hsub rfl hclean hbatch hother hb
  have hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C (eraseFG Q) →
      C ∈ erasedList st (fullTree p st) := by
    intro C hac hcQ
    obtain ⟨A, hAQ, rfl⟩ := core_lift_prefix Q C hcQ
    have hAT := KitFG.ancestor_closed_of_parent_closed _ hi.fg.closed Q hQT A hAQ
    obtain ⟨_, hFQ, hZQ, W, hWT, hQW, hlo⟩ := (core_full_mem st Q).mp hQ
    have hZA : FGBlock.Preceq (controls p st).Z A :=
      preceq_of_eraseFG_preceq hinj ⟨Q, hQT, hZQ⟩ ⟨Q, hQT, hAQ⟩
        (block_preceq_trans (fgsa_Z_preceq_liveRoot p st) (Bool.and_eq_true_iff.mp hac).2)
    have hFZ : FGBlock.Preceq (controls p st).F (controls p st).Z := by
      unfold Controls.Z
      split
      · exact hi.fg.FJ
      · exact KitFG.preceq_refl _
    have hA := (core_full_mem st A).mpr
      ⟨hAT, KitFG.preceq_trans hFZ hZA, hZA, W, hWT, KitFG.preceq_trans hAQ hQW, hlo⟩
    exact List.mem_filter.mpr ⟨(hi.baseTree _).mpr ⟨A, hAT, rfl⟩,
      decide_eq_true ⟨A, hA, rfl⟩⟩
  have hcover : Block.Preceq (eraseFG Q) (getHead p st raw support) := by
    apply fgsa_headInTree_covers_of_transfer p st _ raw support (eraseFG Q)
      hanchor hkeep (hpath _ (block_preceq_refl _)).2
    intro D hd
    have := hconflict D hd
    have := (hpath _ (block_preceq_refl _)).1
    have := hb.lt
    omega
  refine ⟨hcover, ?_, ?_⟩
  · intro hmax
    have terminal (B : FGBlock (Fin p.n)) (hB : B ∈ fullTree p st)
        (he : eraseFG B = getHead p st raw support) : getHead p st raw support = eraseFG Q := by
      have hQB := preceq_of_eraseFG_preceq hinj ⟨Q, hQT, KitFG.preceq_refl _⟩
        ⟨B, ((core_full_mem st B).mp hB).1, KitFG.preceq_refl _⟩ (he.symm ▸ hcover)
      rw [← he, hmax B hB hQB]
    rcases fgsa_headInTree_mem_or_anchor p st (erasedList st (fullTree p st)) raw support
      with he | hm
    · change getHead p st raw support = liveRoot p st at he
      rcases (fgsa_tStart E rho).2 i x hx with hz | ⟨_, _, _, hr, hm, _⟩
      · have hZQ := eraseFG_preceq ((core_full_mem st Q).mp hQ).2.2.1
        exact block_preceq_antisymm (by rw [he, hz]; exact hZQ) hcover
      · obtain ⟨B, hB, hBr⟩ := hm
        exact terminal B hB (hBr.trans (hr.trans he.symm))
    · obtain ⟨B, hB, hBe⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
      exact terminal B hB hBe
  · intro B hac hBH hnone
    have hrest : ∀ a ∈ seats, Gen.AC.poolSupports st.base.blocks support a B = false := by
      intro a ha
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨o, ho, hs, hv⟩ := (Gen.AC.vote_pool_support_witness _ _ _ _).mp h
      rw [Gen.AC.voteSupports_def] at hv
      cases ht : GridCO.headTarget? o with
      | none => simp only [ht, Bool.false_eq_true] at hv
      | some H =>
          have hBH := (Bool.and_eq_true_iff.mp (ht ▸ hv)).2
          exact hnone a ha o ho hs H ht hBH
    have hscore := hunsupported B hrest
    have hel : eligible p st raw support B = true := by
      cases B with
      | genesis =>
          have hg := (Bool.and_eq_true_iff.mp hac).2
          have he : liveRoot p st = .genesis := of_decide_eq_true hg
          have hn := (Bool.and_eq_true_iff.mp hac).1
          change (!decide (liveRoot p st = .genesis)) = true at hn
          simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
      | node P t id =>
          have hAP : Block.Preceq (liveRoot p st) P := by
            have hne : liveRoot p st ≠ .node P t id := by
              intro he
              have hn := (Bool.and_eq_true_iff.mp hac).1
              change (!decide (liveRoot p st = .node P t id)) = true at hn
              simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
            have hp := (Bool.and_eq_true_iff.mp hac).2
            change (decide (liveRoot p st = .node P t id) ||
              Block.preceq (liveRoot p st) P) = true at hp
            simp only [hne, decide_false, Bool.false_or] at hp
            exact hp
          obtain ⟨C, hp, hCB, _, hc, _⟩ := walk_best_ancestry_of_cover (liveRoot p st)
            (.node P t id) (erasedList st (fullTree p st))
            (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)
            hBH P hAP (by
              have hne : P ≠ .node P t id := by
                intro he
                have hd := congrArg Block.depth he
                change P.depth = P.depth + 1 at hd
                omega
              change ((!decide (P = .node P t id)) &&
                (decide (P = .node P t id) || Block.preceq P P)) = true
              simp only [hne, decide_false, Bool.not_false, Bool.false_or, Bool.true_and]
              exact block_preceq_refl P)
          have hdepth : C.depth = (Block.node P t id).depth := by
            cases C with
            | genesis => cases hp
            | node D u jd =>
                have hD := Option.some.inj hp
                subst D
                rfl
          have hC : C = .node P t id := prefix_eq_of_depth C (.node P t id)
            hCB (Nat.le_of_eq hdepth.symm)
          exact hC ▸ hc
    change (_ || decide (_ < 2 * _) || _) = true at hel
    have hn : ¬ GridCO.voterCount raw <
        2 * GridCO.goldfishScore st.base.blocks raw support B := by omega
    simp only [hn, decide_false, Bool.or_false, Bool.or_eq_true_iff,
      decide_eq_true_eq, beq_iff_eq] at hel
    exact hel.elim Or.inr Or.inl

end AvailableChain.FGSA.Run
end
