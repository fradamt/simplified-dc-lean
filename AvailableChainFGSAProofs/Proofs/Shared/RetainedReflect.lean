module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedScores

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure
open RetainedWalk

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1350–1360.
Class (iii). DC: INTENTIONAL; the FG-SA stored-parent band is a separate arm. -/
def retainedBand (p : Params) (st : State p.n) (C : Block) : Prop :=
  ∃ P ∈ st.fg.TF, eraseFG P = C.parent ∧ (heightView p P).h < (controls p st).lo

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1290–1297, 1350–1360.
Class (iii). DC: INTENTIONAL; D3-1 removes caller-supplied source F/Z bounds.
The witness is stored at the source or strictly frozen at the target. -/
def ReflectedDomainWitness (p : Params) (src dst : State p.n)
    (s : Slot) (C : Block) : Prop :=
  ∃ B W : FGBlock (Fin p.n), B ∈ dst.fg.TF ∧ eraseFG B = C ∧
    FGBlock.Preceq B W ∧ (controls p src).lo ≤ (heightView p W).h ∧
    (W ∈ src.fg.TF ∨ (W ∈ dst.fg.TF ∧
      GridCO.stampBlock dst.base (eraseFG W) < SA.freezeTime p.toParams (s - 1)))

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1350–1360.
Class (iii). DC: INTENTIONAL; equation for this module's band predicate. -/
theorem retainedBand_def (p : Params) (st : State p.n) (C : Block) :
    retainedBand p st C = (∃ P ∈ st.fg.TF,
      eraseFG P = C.parent ∧ (heightView p P).h < (controls p st).lo) := by
  apply propext
  constructor <;> exact fun h => h

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1290–1297.
Class (iii). DC: INTENTIONAL; equation for this module's witness predicate. -/
theorem ReflectedDomainWitness_def (p : Params) (src dst : State p.n) (s : Slot) (C : Block) :
    ReflectedDomainWitness p src dst s C =
      (∃ B W : FGBlock (Fin p.n), B ∈ dst.fg.TF ∧ eraseFG B = C ∧
        FGBlock.Preceq B W ∧ (controls p src).lo ≤ (heightView p W).h ∧
        (W ∈ src.fg.TF ∨ (W ∈ dst.fg.TF ∧
          GridCO.stampBlock dst.base (eraseFG W) < SA.freezeTime p.toParams (s - 1)))) := by
  apply propext
  constructor <;> exact fun h => h

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1290–1297, 1330–1360.
Class (iii). DC: INTENTIONAL; actual starts, internal witnesses and band data.
D2-1 permits the parent or the proposal as the target height witness. -/
structure RetainedReadPremises (p : Params) (src dst : State p.n)
    (s : Slot) (D : FGBlock (Fin p.n)) (b Kc : Block) : Prop where
  pivot_parent : Block.Preceq (eraseFG D) b.parent
  ordinary_prefix : BestAncestry (z p src) (ap p src) (S p src) (ss src s) (es p src s)
  target_parent : Block.Preceq (ay p dst) b.parent
  source_cut : Block.Preceq (z p src) Kc
  target_cut : Block.Preceq (ay p dst) Kc
  cut_parent : Block.Preceq Kc b.parent
  target_prefix : BestAncestry (ay p dst) Kc (T p dst s) (ts p dst s) (et p dst s)
  parent_height : ∃ W : FGBlock (Fin p.n),
    ((W ∈ src.fg.TF ∧ eraseFG W = b.parent) ∨ (W ∈ dst.fg.TF ∧ eraseFG W = b)) ∧
    (controls p dst).lo ≤ (heightView p W).h
  reflected_witness : ∀ X C, Block.Preceq Kc X → Block.Preceq X b.parent →
    C ∈ T p dst s → C.parent? = some X → C.slot < s → et p dst s C = true →
    ReflectedDomainWitness p src dst s C
  band_agrees : ∀ X C, Block.Preceq Kc X → Block.Preceq X b.parent →
    C ∈ S p src → C ∈ T p dst s → C.parent? = some X → C.slot < s →
    (retainedBand p src C ↔ retainedBand p dst C)

/-- Blueprint 21:798–809, 2832–2845; spec 1290–1297.
Class (iii). DC: INTENTIONAL; converse S3 gives a witness in the same view.
No store invariant is needed. -/
theorem fgsa_domain_witness_of_mem (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n))) (C : Block)
    (hm : C ∈ erasedList st (KitFG.storeFrameView (heightView p) st.fg Vw)) :
    ∃ B ∈ Vw, eraseFG B = C ∧ FGBlock.Preceq st.fg.F B ∧
      FGBlock.Preceq (controls p st).Z B ∧
      ∃ W ∈ Vw, FGBlock.Preceq B W ∧ (controls p st).lo ≤ (heightView p W).h := by
  obtain ⟨B, hB, he⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  obtain ⟨hv, hf, hz, hw⟩ :=
    (KitFG.mem_filteredFromView (heightView p) (controls p st) Vw B).mp hB
  exact ⟨B, hv, he, hf, hz, hw⟩

/-- Blueprint 03:371–373; 21:798–814; spec 1290–1297.
Class (iii). DC: INTENTIONAL; view-form full-domain SR adapter. -/
theorem fgsa_walkRun_full_domain_view (p : Params) (st : State p.n)
    (h : CStoreInv p st) (D : FGBlock (Fin p.n)) (C : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ (heightView p D).h)
    (hC : C ∈ st.base.blocks) (hDC : Block.Preceq (eraseFG D) C) :
    C ∈ S p st := by
  exact fgsa_walkRun_full_domain p st h D C hF hZ
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using hlo) hC hDC

/-- Blueprint 03:350–354, 364–366; 21:798–809; spec 1290–1297.
Class (iii). DC: INTENTIONAL; view-form path-domain SR adapter. -/
theorem fgsa_walkRun_path_domain_view (p : Params) (st : State p.n)
    (h : CStoreInv p st) (s : Slot) (D : FGBlock (Fin p.n)) (C P : Block)
    (hF : Block.Preceq (eraseFG st.fg.F) (eraseFG D))
    (hZ : FGBlock.Preceq (controls p st).Z D)
    (hlo : (controls p st).lo ≤ (heightView p D).h)
    (hP : P ∈ st.base.blocks) (hs : P.slot = s)
    (hDC : Block.Preceq (eraseFG D) C) (hCP : Block.Preceq C P) :
    C ∈ T p st s := by
  dsimp only [T]
  rw [← KitFG.storeFrame_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  exact fgsa_walkRun_path_domain p st h s D C P hF hZ
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using hlo) hP hs hDC hCP

/-- Blueprint 03:356–360, 373; 21:747–758; spec 1350–1360.
Class (iii). DC: INTENTIONAL; view-form majority-only SR adapter. -/
theorem fgsa_walkRun_eligible_iff_view (p : Params) (st : State p.n)
    (raw sup : List (GridCO.Wire p.n)) (D : FGBlock (Fin p.n)) (C : Block)
    (hlo : (controls p st).lo ≤ (heightView p D).h)
    (hparent : Block.Preceq (eraseFG D) C.parent) (hs : C.slot ≠ st.slot p) :
    eligible p st raw sup C = true ↔
      GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup C := by
  exact fgsa_walkRun_eligible_iff p st raw sup D C
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using hlo) hparent hs

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1350–1360.
Class (iii). DC: INTENTIONAL; all three eligibility arms in view form. -/
theorem fgsa_eligible_eq_of_retainedBand_score
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n)) (C : Block)
    (hband : retainedBand p src C ↔ retainedBand p dst C)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C := by
  rw [fgsa_eligible_eq, fgsa_eligible_eq]
  simp only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  have hb := propext hband
  dsimp only [retainedBand] at hb
  simp only [hb, hcount, hscore, hslot]

/-- Blueprint 21:783–795, 2847–2867; spec 616–633, 1290–1297.
Class (iii). DC: INTENTIONAL; D3-1 derives the source admission floor from FJ. -/
private theorem reflect_F_Z (p : Params) (st : State p.n) (h : CStoreInv p st) :
    FGBlock.Preceq st.fg.F (controls p st).Z := by
  unfold Controls.Z
  split
  · exact h.fg.FJ
  · exact KitFG.preceq_refl _

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1290–1297.
Class (iii). DC: INTENTIONAL; lift the immutable erased ancestry. -/
private theorem reflect_lift {n : Nat} {A B : FGBlock (Fin n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  preceq_of_eraseFG_preceq (Vw := {A, B}) (KitFG.viewRootInj_all _)
    ⟨A, by simp, KitFG.preceq_refl _⟩ ⟨B, by simp, KitFG.preceq_refl _⟩ h

/-- Blueprint 21:747–758, 798–814; spec 1290–1297.
Class (iii). DC: INTENTIONAL; parent ancestry for a retained FG-SA candidate. -/
private theorem reflect_parent {C X : Block} (hp : C.parent? = some X) :
    Block.Preceq X C := by
  cases C with
  | genesis => cases hp
  | node P s r =>
    have he : P = X := Option.some.inj hp
    subst P
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 21:747–758, 798–814, 2847–2867; spec 1290–1297.
Class (iii). DC: INTENTIONAL; the actual clock preserves stored receipt stamps. -/
private theorem reflect_clock_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (y : V) (t : Time) (B : Block)
    (hm : B ∈ (rho.stateBefore E k y).st.base.blocks) :
    GridCO.stampBlock (clock p (rho.stateBefore E k y).st t).base B =
      GridCO.stampBlock (rho.stateBefore E k y).st.base B := by
  rw [← (metaInv_stateBefore E rho k y).stampKeys] at hm
  obtain ⟨⟨b, u⟩, hv, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  unfold GridCO.stampBlock
  rw [(clock_cumulative p _ _).2.2.1]
  cases hf : (rho.stateBefore E k y).st.base.blockStamp.find? (fun row => row.1 == B) with
  | none =>
    have hn := List.find?_eq_none.mp hf (B, u) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- Blueprint 21 H.5:747–758, H.6:798–814, H.17:2847–2867;
spec 1290–1297, 1330–1360. Class (iii). DC: INTENTIONAL; inclusive S4.
The witness itself reaches the source. Closure then gives the candidate,
including candidates below lo. Neither source F/Z bound is a premise. -/
private theorem reflect_witness_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (Kc X C : Block)
    (hcut : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKX : Block.Preceq Kc X) (hp : C.parent? = some X)
    (hm : C ∈ T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C) :
    C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  obtain ⟨B, W, -, heB, hBW, hlo, hW⟩ := hw
  have hZB : FGBlock.Preceq (controls p src).Z B :=
    reflect_lift (heB ▸ block_preceq_trans hcut (block_preceq_trans hKX (reflect_parent hp)))
  have hFB := KitFG.preceq_trans (reflect_F_Z p src hs) hZB
  have hWsrc : W ∈ src.fg.TF := by
    rcases hW with hW | ⟨hW, hstamp⟩
    · exact hW
    · obtain ⟨Q, -, heQ, hFQ, -⟩ := fgsa_domain_witness_of_mem p dst _ C hm
      have hFdst : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := by
        rw [heB, ← heQ]
        exact eraseFG_preceq hFQ
      have hmW : eraseFG W ∈ (rho.stateBefore E ih y).st.base.blocks := by
        have hb := (ht.baseTree _).mpr ⟨W, hW, rfl⟩
        change eraseFG W ∈ (clock p _ _).base.blocks at hb
        rwa [clock_base_blocks] at hb
      rw [reflect_clock_stamp E rho ih y _ (eraseFG W) hmW] at hstamp
      have hgeom : ScoreRunGeometry src dst (eraseFG B) := ⟨eraseFG_preceq hFB, hFdst⟩
      have hr := fgsa_walkRun_frozen_block E rho hE hN hDelta s hSync hx hy hip
        (eraseFG B) (eraseFG W) hgeom (eraseFG_preceq hBW) hmW
        (by simpa only [Nat.add_sub_cancel] using hstamp)
      have hb := ((actView_blocks src (eraseFG W)).mp hr).1
      obtain ⟨Q, hQ, heQ⟩ := (hs.baseTree _).mp hb
      exact (eraseFG_injective heQ) ▸ hQ
  obtain ⟨Q, hQ, heQ⟩ := eraseFG_ancestor_mem hs.fg.closed hWsrc (eraseFG_preceq hBW)
  have hBsrc : B ∈ src.fg.TF := (eraseFG_injective heQ) ▸ hQ
  rw [← heB]
  exact List.mem_filter.mpr ⟨(hs.baseTree _).mpr ⟨B, hBsrc, rfl⟩,
    decide_eq_true ⟨B, (KitFG.mem_filteredFromView (heightView p) (controls p src)
      src.fg.TF B).mpr ⟨hBsrc, hFB, hZB, W, hWsrc, hBW, hlo⟩, rfl⟩⟩

/-- Blueprint 21 H.5:747–758, H.6:798–814, H.17:2847–2867;
spec 1290–1297, 1330–1360. Class (iii). DC: INTENTIONAL; S4 at X ≤ A.
The old-slot guard includes X = A and excludes the current proposal.
The stronger witness relay needs no strict-parent split. -/
theorem fgsa_walkRun_reflected_old_child
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (_hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (_hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (_hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Kc X C : Block)
    (hcut : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKX : Block.Preceq Kc X) (_hXA : Block.Preceq X b.parent)
    (hp : C.parent? = some X) (_hold : C.slot < s + 1)
    (hm : C ∈ T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C) :
    C ∈ S p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))) :=
  reflect_witness_on_run E rho hE hN hDelta s hSync hx hy hip Kc X C hcut hKX hp hm hw

/-- Blueprint 21 H.5:747–758, H.6:798–814, H.17:2847–2867;
spec 1290–1297, 1330–1360. Class (iii). DC: INTENTIONAL; supplies exactly
W.reflects and E.old_reflects. Strict-parent rivals are old by the landed
raw reflection and proposal-slot bound. G25 then compares each common
candidate, and the band adapter transports all eligibility arms. -/
theorem fgsa_retained_old_child_reflects_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hWalkSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : b ∈ (rho.stateBefore E ih y).st.base.blocks)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D b Kc) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    SuffixReflects Kc b.parent (S p src) (T p dst (s + 1))
      (es p src (s + 1)) (et p dst (s + 1)) ∧
    (∀ C ∈ T p dst (s + 1), C.parent? = some b.parent → C.slot < s + 1 →
      et p dst (s + 1) C = true → C ∈ S p src ∧ es p src (s + 1) C = true) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hK : ScoreRunGeometry src dst Kc :=
    ⟨block_preceq_trans (eraseFG_preceq (reflect_F_Z p src hs)) h.source_cut,
      block_preceq_trans (F_preceq_liveRoot p dst ht) h.target_cut⟩
  have hA : ScoreRunGeometry src dst b.parent :=
    ⟨block_preceq_trans hK.source_floor h.cut_parent,
      block_preceq_trans hK.target_floor h.cut_parent⟩
  have scores := fgsa_score_eq_on_candidates_on_run E rho hE hN hDelta (s + 1)
    hScoreSync hx hy hip hih hseat b raw sup rows hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1)) hA
    (fun C hm => fgsa_score_geometry_of_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2)
  have reflect (X C : Block) (hKX : Block.Preceq Kc X) (hXA : Block.Preceq X b.parent)
      (hm : C ∈ T p dst (s + 1)) (hp : C.parent? = some X) (hold : C.slot < s + 1)
      (he : et p dst (s + 1) C = true) : C ∈ S p src ∧ es p src (s + 1) C = true := by
    have hc := fgsa_walkRun_reflected_old_child E rho hE hN hDelta s hWalkSync
      hx hy hip hih hseat b raw sup rows hem Kc X C h.source_cut hKX hXA hp hold hm
      (h.reflected_witness X C hKX hXA hm hp hold he)
    refine ⟨hc, ?_⟩
    have hel := fgsa_eligible_eq_of_retainedBand_score p src dst
      (proposerVotes src (s + 1)) (proposerSupport src (s + 1))
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) C
      (h.band_agrees X C hKX hXA hc hm hp hold) scores.1 (scores.2 C ⟨hc, hm⟩)
      ((fgsa_proposal_slot (c := c) _ (s + 1)).trans
        (fgsa_vote_slot (c := c) _ (s + 1)).symm)
    exact hel.trans he
  constructor
  · intro X C hKX hXA hm hp he
    have hmOld := hm
    dsimp only [T] at hmOld
    rw [← KitFG.storeFrame_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hmOld
    have hc := fgsa_walkRun_reflected_block E rho hE hN hDelta s hWalkSync hx hy hip
      hseat b raw sup rows hem Kc X C hK hKX hXA hp hmOld
    have hold := (fgsa_stored_block_slots E rho hE.toScheduleWellFormed hip
      (Nat.succ_pos s)).2.1 C hc
    exact reflect X C hKX (Bool.and_eq_true_iff.mp hXA).2 hm hp hold he
  · intro C hm hp hold he
    exact reflect b.parent C h.cut_parent (block_preceq_refl _) hm hp hold he

end AvailableChain.FGSA.Run
end
