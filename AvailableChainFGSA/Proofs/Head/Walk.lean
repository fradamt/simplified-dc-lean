module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainGeneric.Proofs.AC.Support
public import AvailableChainGeneric.Proofs.Pure.Walk

public section

namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
open Gen.Pure

/-- P3 F1b.4a:4857–4859; bp02 §4.1. Class (iii), store instance.
DC: Adoption.goldfish_fork_choice_captures_supporter_majority:415.
INTENTIONAL: liveRoot and FJ eligibility replace the SG controls;
P3:4845–4853 fixes these arguments. The keep supplier is a parameter (M6). -/
theorem fgsa_getHead_covers_of_dominated_suffix
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hkeep : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      C ∈ erasedList st (fullTree p st))
    (helig : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      eligible p st raw support C = true)
    (hdom : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B →
      ∀ D ∈ erasedList st (fullTree p st), D.parent? = C.parent? →
        eligible p st raw support D = true → D ≠ C →
        GridCO.goldfishScore st.base.blocks raw support D <
          GridCO.goldfishScore st.base.blocks raw support C) :
    Block.Preceq B (getHead p st raw support) := by
  apply walk_covers_of_dominated_suffix _ _ _ _ _ hanchor
  rw [DominatedSuffix_def]
  exact fun C hac hcb => ⟨hkeep C hac hcb, helig C hac hcb, hdom C hac hcb⟩

/-- P3 F1b.4a W3:4860–4863; bp02 §4.1. Class (iii), store instance.
DC: Walk.ghost_reaches:433 and Walk.ghost_step_none:197.
INTENTIONAL: the dominated suffix packages DC's selected path; the
terminal target remains a premise, as required by P3 W3. -/
theorem fgsa_getHead_exact_of_dominated_suffix
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) (B : Block)
    (hanchor : Block.Preceq (liveRoot p st) B)
    (hkeep : DominatedSuffix (liveRoot p st) B (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support))
    (hstop : NoEligibleChild (erasedList st (fullTree p st)) (eligible p st raw support) B) :
    getHead p st raw support = B :=
  walk_exact_of_dominated_suffix _ _ _ _ _ hanchor hkeep hstop

/-- P3 F1b.4a W6:4864–4867; bp02 §4.1. Class (iii), store instance.
DC: ProposalWalkTransportCore.ghost_transport_of_source:162.
INTENTIONAL: P3 W6 fixes one view and moves its anchor along the dominated
suffix. No cross-view fact follows from this equality. -/
theorem fgsa_getHead_reanchor_of_dominated_suffix
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) (B : Block)
    (hanchor : Block.Preceq (liveRoot p st) B)
    (hkeep : DominatedSuffix (liveRoot p st) B (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support)) :
    getHead p st raw support = GridCO.ghost B (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support) :=
  walk_reanchor_of_dominated_suffix _ _ _ _ _ hanchor hkeep

/-- P3 F1b.4a:4878–4881; bp02 §4.1. Class (iii), store instance.
DC: Walk.ghost_step_child:184 and Walk.ghost_eligible:281 (path ingredients).
INTENTIONAL: FJ has three eligibility arms; P3 requires exclusion of
all three, including the low-parent and current-slot arms. -/
theorem fgsa_getHead_avoids_unsupported_child
    (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) (B C : Block)
    (hanchor : Block.Preceq (liveRoot p st) B) (hparent : C.parent? = some B)
    (hfloor : ¬ ∃ P ∈ st.fg.TF, eraseFG P = C.parent ∧
      hOf p.E p.cfg P < (controls p st).lo)
    (hscore : 2 * GridCO.goldfishScore st.base.blocks raw support C ≤ GridCO.voterCount raw)
    (hslot : C.slot ≠ st.slot p) : ¬ Block.Preceq C (getHead p st raw support) := by
  apply walk_avoids_unsupported_child _ B _ _ _ _ hanchor hparent
  change (decide _ || decide _ || _) = false
  simp only [hfloor, decide_false, Nat.not_lt.mpr hscore, Bool.false_or,
    beq_eq_false_iff_ne.mpr hslot]

/-- P3 F1b.4a G11:4882–4889; bp02 §4.3. Class (iii), store instance.
DC: ProposalWalkTransportCore.ghost_transport_of_source:162.
INTENTIONAL: G11 preserves a prefix using candidate-local scores and
suffix persistence, not an exact terminal head (GLY G11). The common
live root is explicit; the keep supplier remains a parameter (M6). -/
theorem fgsa_getHead_covers_of_suffix_transfer
    (p : Params) (st st' : State p.n)
    (raw support raw' support' : List (GridCO.Wire p.n)) (B : Block)
    (hroot : liveRoot p st' = liveRoot p st)
    (hanchor : Block.Preceq (liveRoot p st) B)
    (hcover : Block.Preceq B (getHead p st raw support))
    (hkeep : SuffixPersists (liveRoot p st) B
      (erasedList st (fullTree p st)) (erasedList st' (fullTree p st'))
      (GridCO.goldfishScore st.base.blocks raw support)
      (eligible p st raw support) (eligible p st' raw' support'))
    (hreflect : SuffixReflects (liveRoot p st) B
      (erasedList st (fullTree p st)) (erasedList st' (fullTree p st'))
      (eligible p st raw support) (eligible p st' raw' support'))
    (hscore : SuffixScoresAgree (liveRoot p st) B (erasedList st' (fullTree p st'))
      (GridCO.goldfishScore st.base.blocks raw support)
      (GridCO.goldfishScore st'.base.blocks raw' support') (eligible p st' raw' support')) :
    Block.Preceq B (getHead p st' raw' support') := by
  change Block.Preceq B (GridCO.ghost (liveRoot p st') _ _ _)
  rw [hroot]
  exact ghost_transfer_sfx _ _ _ _ _ _ _ _ hanchor hcover hkeep hreflect hscore

/-- P3 F1b.4a W8:4868–4874; bp02 §4.1. Class (iii), store instance.
DC: Walk.ghost_reaches:433; GSTZeroPreparedWalk.
preparedConfirmationWalk_preceq_voteDutyHead_of_gstZero:546 (genuine test).
INTENTIONAL: the F-anchored optional result tests its final block. At the
anchor, eligibility is an explicit premise; a strict suffix supplies it (P3 W8). -/
theorem fgsa_confirmationFrom_exact_of_dominated_suffix
    (p : Params) (v : GridCO.State p.n) (a B : Block) (s : Slot)
    (hanchor : Block.Preceq a B)
    (hkeep : DominatedSuffix a B v.blocks (SA.prefixSupport p.toParams v s)
      (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s C)))
    (hstop : NoEligibleChild v.blocks
      (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s C)) B)
    (helig : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.prefixSupport p.toParams v s a ∨ Block.Prec a B) :
    SA.confirmationFrom p.toParams a v s = some B := by
  have hexact := walk_exact_of_dominated_suffix _ _ _ _ _ hanchor hkeep hstop
  have hb : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.prefixSupport p.toParams v s B := by
    rcases helig with ha | hab
    · by_cases he : a = B
      · simpa only [← he] using ha
      · have hab : Block.Prec a B := by
          change ((!decide (a = B)) && Block.preceq a B) = true
          simp only [he, decide_false, Bool.not_false, Bool.true_and]
          exact hanchor
        exact of_decide_eq_true (hkeep B hab (block_preceq_refl B)).2.1
    · exact of_decide_eq_true (hkeep B hab (block_preceq_refl B)).2.1
  change (if GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.prefixSupport p.toParams v s
        (GridCO.ghost a v.blocks (SA.prefixSupport p.toParams v s)
          (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
            2 * SA.prefixSupport p.toParams v s C))) then
      some (GridCO.ghost a v.blocks (SA.prefixSupport p.toParams v s)
        (fun C => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
          2 * SA.prefixSupport p.toParams v s C))) else none) = some B
  rw [hexact]
  exact ite_eq_left hb

/-- P3 F1b.4a and F2.3; bp02 §4.1–4.2. Class (iii), store instance.
DC: Adoption.goldfish_fork_choice_captures_supporter_majority:415 and
Adoption.goldfish_fork_choice_captures_of_confirmation:441.
INTENTIONAL: FJ eligibility and liveRoot replace SG controls (P3:4845–4853).
This is the common store proof for transfer and batch callers; suffix
membership is supplied as a parameter (M6). -/
theorem fgsa_headInTree_covers_of_transfer
    (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n)) (B : Block)
    (hanchor : Block.Compatible (liveRoot p st) B)
    (hpath : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C B → C ∈ tree)
    (hmajority : GridCO.voterCount raw <
      2 * GridCO.goldfishScore st.base.blocks raw support B)
    (hdominance : ∀ D, Block.compatible B D = false →
      GridCO.goldfishScore st.base.blocks raw support D <
        GridCO.goldfishScore st.base.blocks raw support B) :
    Block.Preceq B (headInTree p st tree raw support) := by
  apply walk_covers_of_dominated_suffix _ _ _ _ _ hanchor
  rw [DominatedSuffix_def]
  intro C hac hcb
  have hm := Gen.AC.goldfishScore_antitone st.base.blocks
    raw support C B hcb
  refine ⟨hpath C hac hcb, ?_, ?_⟩
  · change (_ || decide (_ < 2 * _) || _) = true
    have hmaj : GridCO.voterCount raw <
        2 * GridCO.goldfishScore st.base.blocks
          raw support C := by omega
    simp only [hmaj, decide_true, Bool.or_true, Bool.true_or]
  · intro D _ hp _ hne
    have he : D.depth = C.depth := by
      cases D with
      | genesis => cases C with
        | genesis => rfl
        | node P s id => cases hp
      | node P s id => cases C with
        | genesis => cases hp
        | node Q t jd =>
          have heq : P = Q := Option.some.inj hp
          subst Q
          rfl
    have hn : ¬ Block.Compatible D C := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hne (prefix_eq_of_depth D C h (Nat.le_of_eq he.symm))
      · exact hne (prefix_eq_of_depth C D h (Nat.le_of_eq he)).symm
    have hd : Block.compatible B D = false := by
      rw [block_compatible_comm]
      exact Bool.eq_false_iff.mpr (block_incompatible_of_preceq hn hcb)
    exact lt_of_lt_of_le (hdominance D hd) hm

end AvailableChain.FGSA
