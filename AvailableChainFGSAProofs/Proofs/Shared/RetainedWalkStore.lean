module
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainGeneric.Proofs.Pure.Walk
public import AvailableChainGeneric.Proofs.Pure.Fold

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG
open Gen.Pure

/-- Blueprint 21:783–795, 2818–2825; spec 648–655, 1086–1098.
Class (iii). DC: INTENTIONAL; DC has no FJ live-root selector.
Local proof of `geometry_Z_liveRoot` in FGSA/Proofs/Head/Walk.lean:213,
from the Frame definition and KitFG store facts. -/
private theorem retained_store_root_live (p : Params) (st : State p.n) :
    Block.Preceq (eraseFG (controls p st).Z) (liveRoot p st) := by
  have lift {A B : FGBlock (Fin p.n)} (h : FGBlock.Preceq A B) :
      Block.Preceq (eraseFG A) (eraseFG B) := by
    induction B with
    | genesis =>
        rw [KitFG.preceq_genesis] at h
        subst h
        exact block_preceq_refl _
    | node P s v data ih =>
        change (decide (A = .node P s v data) || FGBlock.preceq A P) = true at h
        rcases Bool.or_eq_true_iff.mp h with he | h
        · have he' := of_decide_eq_true he
          subst A
          exact block_preceq_refl _
        · change (decide (eraseFG A = eraseFG (.node P s v data)) ||
            Block.preceq (eraseFG A) (eraseFG P)) = true
          exact Bool.or_eq_true_iff.mpr (Or.inr (ih h))
  unfold liveRoot
  dsimp only
  rcases foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · rw [he]
    exact block_preceq_refl _
  · obtain ⟨entry, -, hr⟩ := List.mem_filterMap.1 hm
    split at hr
    · next hc =>
      obtain ⟨B, hB, he⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
      rw [← Option.some.inj hr, ← he]
      exact lift ((KitFG.mem_filteredFrom_of_bridge
        p.E p.cfg (heightView p) (heightView_bridge p) _ _ B).mp hB).2.2.1
    · cases hr

/-- Blueprint 21:783–795, 878–883, 1401–1427, 1998–2019, 2119–2148,
2818–2825; spec 1109–1114. Class (iii).
DC: INTENTIONAL; ProposalWalkTransportCore.lean:169 has the source result;
FG-SA first proves equality of the ordinary and live-root walks.
The best-ancestry conjunction is inline until the Gen predicate is available. -/
theorem fgsa_ordinary_parent_of_live_prefix
    (p : Params) (src : State p.n) (raw sup : List (GridCO.Wire p.n)) (A : Block)
    (hparent : getHead p src raw sup = A)
    (hprefix :
      let z := eraseFG (controls p src).Z
      let ap := liveRoot p src
      let S := src.base.blocks.filter (fun b =>
        decide (∃ B ∈ storeFrame p.E p.cfg src.fg src.fg.TF, eraseFG B = b))
      let ss := GridCO.goldfishScore src.base.blocks raw sup
      let es := eligible p src raw sup
      ∀ X, Block.Preceq z X → Block.Prec X ap →
        ∃ C, C.parent? = some X ∧ Block.Preceq C ap ∧ C ∈ S ∧
          es C = true ∧ ∀ D ∈ S, D.parent? = some X → es D = true →
            ss D ≤ ss C ∧ (ss D = ss C → D.root ≤ C.root)) :
    let z := eraseFG (controls p src).Z
    let S := src.base.blocks.filter (fun b =>
      decide (∃ B ∈ storeFrame p.E p.cfg src.fg src.fg.TF, eraseFG B = b))
    let ss := GridCO.goldfishScore src.base.blocks raw sup
    let es := eligible p src raw sup
    GridCO.ghost z S ss es = getHead p src raw sup ∧
      GridCO.ghost z S ss es = A := by
  have he := walk_reanchor_of_best_ancestry _ _ _ _ _
    (retained_store_root_live p src) hprefix
  exact ⟨he, he.trans hparent⟩

/-- Blueprint 21:783–795, 2818–2825; spec 1109–1114. Class (iii).
DC: INTENTIONAL; ProposalWalkTransportCore.lean:162 extracts source steps.
Coverage of the live root supplies the ordinary best prefix. -/
theorem fgsa_ordinary_parent_of_live_cover
    (p : Params) (src : State p.n) (raw sup : List (GridCO.Wire p.n)) (A : Block)
    (hparent : getHead p src raw sup = A)
    (hcover : Block.Preceq (liveRoot p src)
      (GridCO.ghost (eraseFG (controls p src).Z)
        (src.base.blocks.filter (fun b =>
          decide (∃ B ∈ storeFrame p.E p.cfg src.fg src.fg.TF, eraseFG B = b)))
        (GridCO.goldfishScore src.base.blocks raw sup) (eligible p src raw sup))) :
    GridCO.ghost (eraseFG (controls p src).Z)
      (src.base.blocks.filter (fun b =>
        decide (∃ B ∈ storeFrame p.E p.cfg src.fg src.fg.TF, eraseFG B = b)))
      (GridCO.goldfishScore src.base.blocks raw sup) (eligible p src raw sup) = A := by
  exact (fgsa_ordinary_parent_of_live_prefix p src raw sup A hparent
    (walk_best_ancestry_of_cover _ _ _ _ _ hcover)).2

/-- Blueprint 21:728–758, 798–809; spec 1063–1072. Class (iii).
DC: INTENTIONAL; DC transport takes eligibility as a parameter.
A common immutable parent and equal floors preserve the stored-parent band. -/
theorem fgsa_band_eq_of_same_floor
    (p : Params) (src dst : State p.n) (C : Block) (P : FGBlock (Fin p.n))
    (hsrc : P ∈ src.fg.TF) (hdst : P ∈ dst.fg.TF) (hP : eraseFG P = C.parent)
    (hlo : (controls p src).lo = (controls p dst).lo) :
    (∃ Q ∈ src.fg.TF, eraseFG Q = C.parent ∧
      hOf p.E p.cfg Q < (controls p src).lo) ↔
    (∃ Q ∈ dst.fg.TF, eraseFG Q = C.parent ∧
      hOf p.E p.cfg Q < (controls p dst).lo) := by
  have root (B : FGBlock (Fin p.n)) : (eraseFG B).root = B.root := by
    induction B with
    | genesis => rfl
    | node B s v data ih =>
        change nodeRoot (eraseFG B).root s _ = nodeRoot B.root s _
        rw [ih]
  have unique (Q : FGBlock (Fin p.n)) (he : eraseFG Q = C.parent) : Q = P := by
    apply KitFG.viewRootInj_all ({Q, P} : Finset (FGBlock (Fin p.n)))
      Q P ⟨Q, by simp, KitFG.preceq_refl Q⟩ ⟨P, by simp, KitFG.preceq_refl P⟩
    rw [← root Q, ← root P, he, hP]
  constructor
  · rintro ⟨Q, -, he, hh⟩
    have hQP := unique Q he
    subst Q
    exact ⟨P, hdst, hP, hlo ▸ hh⟩
  · rintro ⟨Q, -, he, hh⟩
    have hQP := unique Q he
    subst Q
    exact ⟨P, hsrc, hP, hlo.symm ▸ hh⟩

/-- Blueprint 21:728–758, 798–809, 2836–2845; spec 1063–1072.
Class (iii). DC: INTENTIONAL; FG-SA eligibility has stored-parent band,
majority and current-slot arms, while DC transport abstracts eligibility. -/
theorem fgsa_eligible_eq_of_band_score
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n)) (C : Block)
    (hband : (∃ P ∈ src.fg.TF, eraseFG P = C.parent ∧
        hOf p.E p.cfg P < (controls p src).lo) ↔
      (∃ P ∈ dst.fg.TF, eraseFG P = C.parent ∧
        hOf p.E p.cfg P < (controls p dst).lo))
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C := by
  rw [fgsa_eligible_eq, fgsa_eligible_eq]
  simp only [propext hband, hcount, hscore, hslot]

/-- Blueprint 21:1422–1425, 1937–1939, 2112–2116, 2836–2845;
spec 1063–1072. Class (iii). DC: INTENTIONAL; the FG-SA band arm is false
on both sides of this floor-neutral eligibility adapter. -/
theorem fgsa_eligible_eq_of_no_band_score
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n)) (C : Block)
    (hsrc : ¬ ∃ P ∈ src.fg.TF, eraseFG P = C.parent ∧
      hOf p.E p.cfg P < (controls p src).lo)
    (hdst : ¬ ∃ P ∈ dst.fg.TF, eraseFG P = C.parent ∧
      hOf p.E p.cfg P < (controls p dst).lo)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C := by
  exact fgsa_eligible_eq_of_band_score p src dst raw sup raw' sup' C
    ⟨fun h => (hsrc h).elim, fun h => (hdst h).elim⟩ hcount hscore hslot

end AvailableChain.FGSA
