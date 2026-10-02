module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalk
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalkStore
public import AvailableChainFGSAProofs.Proofs.Shared.ScoreRun

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

/-- Blueprint 21 H.5:856–886 (design citation 728–758); spec 1350–1360.
Class (iii). DC: INTENTIONAL; the stored-parent band needs the same
immutable parent in both stores and equal floors at these two reads. -/
theorem fgsa_eligible_eq_of_same_floor
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n)) (C : Block) (P : FGBlock (Fin p.n))
    (hsrc : P ∈ src.fg.TF) (hdst : P ∈ dst.fg.TF) (hP : eraseFG P = C.parent)
    (hlo : (controls p src).lo = (controls p dst).lo)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C :=
  fgsa_eligible_eq_of_band_score p src dst raw sup raw' sup' C
    (fgsa_band_eq_of_same_floor p src dst C P hsrc hdst hP hlo) hcount hscore hslot

/-- Blueprint 21 HG.1:1558–1565, L2-W:2068–2088, L4-R:2250–2265,
H.17:2976–2985 (design 1422–1425,1937–1939,2112–2116,2836–2845);
spec 1350–1360. Class (iii). DC: INTENTIONAL; parent height witnesses
exclude the band arm separately at each read, without equal floors. -/
theorem fgsa_eligible_eq_of_parent_height
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n)) (C : Block)
    (hsrc : ∀ P ∈ src.fg.TF, eraseFG P = C.parent →
      (controls p src).lo ≤ (heightView p P).h)
    (hdst : ∀ P ∈ dst.fg.TF, eraseFG P = C.parent →
      (controls p dst).lo ≤ (heightView p P).h)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C := by
  apply fgsa_eligible_eq_of_no_band_score p src dst raw sup raw' sup' C
    ?_ ?_ hcount hscore hslot
  · rintro ⟨P, hm, he, hh⟩
    exact Nat.not_lt_of_ge (hsrc P hm he) hh
  · rintro ⟨P, hm, he, hh⟩
    exact Nat.not_lt_of_ge (hdst P hm he) hh

/-- Blueprint 21 H.5:886–914, H.17:2987–3009; spec 1290–1297,1520–1523.
Class (iii). DC: INTENTIONAL; each common candidate supplies its own two
F bounds. Membership can come from fgsa_walk_domain_of_witness; the height
witness stays inside its duty view. No bound on a paper pivot is used. -/
theorem fgsa_score_geometry_of_domains
    (p : Params) (src dst : State p.n)
    (Vs Vt : Finset (FGBlock (Fin p.n))) (C : Block)
    (hsrc : C ∈ erasedList src (KitFG.storeFrameView (heightView p) src.fg Vs))
    (hdst : C ∈ erasedList dst (KitFG.storeFrameView (heightView p) dst.fg Vt)) :
    ScoreRunGeometry src dst C := by
  have floor (st : State p.n) (V : Finset (FGBlock (Fin p.n)))
      (hm : C ∈ erasedList st (KitFG.storeFrameView (heightView p) st.fg V)) :
      Block.Preceq (eraseFG st.fg.F) C := by
    obtain ⟨B, hB, he⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
    rw [← he]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p)
        (KitFG.storeControlsView (heightView p) st.fg) V B).mp hB).2.1
  exact ⟨floor src Vs hsrc, floor dst Vt hdst⟩

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 03:293–331; 21 H.5:886–914, H.17:2987–3009;
spec 1530–1538,1554–1577. Class (iii). DC: INTENTIONAL;
ProposalWalkTransportCore.lean:185 compares common candidates. The parent
instance supplies the count even for an empty candidate set. Each candidate
uses G25 at itself. Signed proposal metadata passes through unchanged. -/
theorem fgsa_score_eq_on_candidates_on_run
    (E) (rho)
    (hE : V2.D.ExecutionValid (V := V) (P := fgsa p c) E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : b ∈ (rho.stateBefore E ih y).st.base.blocks)
    (Candidates : Block → Prop)
    (hA : ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) b.parent)
    (hCandidates : ∀ C, Candidates C → ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) C) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
    GridCO.voterCount (proposerVotes src s) = GridCO.voterCount (headVotes p dst s) ∧
      ∀ C, Candidates C → RetainedWalk.ss src s C = RetainedWalk.ts p dst s C := by
  refine ⟨(fgsa_score_eq_on_run E rho hE hN hDelta s hSync hx hy hip hih hseat
    b raw sup rows hem hadm b.parent hA).2.2.1, ?_⟩
  intro C hC
  exact (fgsa_score_eq_on_run E rho hE hN hDelta s hSync hx hy hip hih hseat
    b raw sup rows hem hadm C (hCandidates C hC)).2.2.2 C (block_preceq_refl C)

/-- Blueprint 21 H.5:886–914, H.17:2987–3009; spec 1330–1360.
Class (iii). DC: INTENTIONAL; selected retained children and reflected
eligible rivals use candidate-local G25. The inclusive candidate set also
serves old-child endpoint reflection. This supplies exactly the scores field
of RetainedWalkRunGeometry, with no assertion about a removed trunk. -/
theorem fgsa_retained_scores_of_candidates
    (p : Params) (src dst : State p.n) (s : Slot) (Kc A : Block)
    (hscore : ∀ C, (∃ X, Block.Preceq Kc X ∧ Block.Preceq X A ∧
      C ∈ RetainedWalk.T p dst s ∧ C.parent? = some X ∧
      RetainedWalk.et p dst s C = true ∧ (Block.Prec X A ∨ C.slot < s)) →
      RetainedWalk.ss src s C = RetainedWalk.ts p dst s C) :
    SuffixScoresAgree Kc A (RetainedWalk.T p dst s)
      (RetainedWalk.ss src s) (RetainedWalk.ts p dst s) (RetainedWalk.et p dst s) := by
  intro X C hK hX hm hp he
  exact (hscore C ⟨X, hK, (Bool.and_eq_true_iff.mp hX).2, hm, hp, he, Or.inl hX⟩).symm

end AvailableChain.FGSA.Run
end
