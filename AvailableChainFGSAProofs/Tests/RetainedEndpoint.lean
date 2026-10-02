module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedEndpoint

open AvailableChain.SimplexFG
open Gen.Pure
open RetainedWalk

/-- Blueprint 21 H.5:891–902, H.6:942–958 (design 747–758,798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; finite parameters for the witness tests. -/
private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; retained cut and live lease target. -/
private def cutFG : FGBlock (Fin 1) := .node .genesis 1 0 []
/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; parent strictly above the retained cut. -/
private def parentFG : FGBlock (Fin 1) := .node cutFG 2 0 []
/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; old child at the inclusive endpoint. -/
private def oldFG : FGBlock (Fin 1) := .node parentFG 3 0 []

/-- Blueprint 21 H.17:3008–3011 (design 2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; the admitted current proposal shares A with the old child. -/
private def proposalFG : FGBlock (Fin 1) := .node parentFG 4 0 []

/-- Blueprint 21 H.6:927–958 (design 783–814); spec 1373–1385, 1290–1297. Class (iii).
DC: INTENTIONAL; a source with a live lease above its root. -/
private def source : State 1 :=
  { initial 1 with
    base := { (initial 1).base with
      now := 16
      votes := [⟨.seat 3 0, .head (eraseFG parentFG)⟩]
      voteStamp := [(⟨.seat 3 0, .head (eraseFG parentFG)⟩, 0)]
      blocks := [.genesis, eraseFG cutFG, eraseFG parentFG]
      blockStamp := [(.genesis, 0), (eraseFG cutFG, 0), (eraseFG parentFG, 0)]
      obligations := [(eraseFG cutFG, 0, 100)] }
    fg := {
      TF := {.genesis, cutFG, parentFG}
      F := .genesis
      J := .genesis
      h_j := 0
      h_max := 1 } }

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; the frozen old child is absent from the source fixture. -/
private def target : State 1 :=
  { source with
    base := { source.base with
      blocks := source.base.blocks ++ [eraseFG oldFG, eraseFG proposalFG]
      obligations := []
      blockStamp := source.base.blockStamp ++ [(eraseFG oldFG, 0), (eraseFG proposalFG, 16)] }
    fg := { source.fg with TF := {.genesis, cutFG, parentFG, oldFG, proposalFG} } }

/-- Blueprint 21 H.6:942–953 (design 798–809); spec 1290–1297. Class (iii).
DC: INTENTIONAL; use the height-law bridge without reducing the active view. -/
private theorem fixture_height (st : State 1) (hmax : st.fg.h_max = 1)
    (W : FGBlock (Fin 1)) : (controls params st).lo ≤ (heightView params W).h := by
  have hlo : (controls params st).lo ≤ 1 := by
    unfold Controls.lo
    change (if _ then st.fg.h_max else st.fg.h_max - 1) ≤ 1
    rw [hmax]
    split <;> decide
  apply hlo.trans
  rw [(KitFG.heightBridge_fields params.E params.cfg
    (heightView params) (heightView_bridge params) W).1]
  exact KitFG.one_le_h params.E params.cfg W

/-- Blueprint 21 H.6:927–958 (design 783–814); spec 616–633. Class (iii).
DC: INTENTIONAL; both branches select the common genesis F/J, without height reduction. -/
private theorem fixture_root (st : State 1) (hF : st.fg.F = .genesis)
    (hJ : st.fg.J = .genesis) : (controls params st).Z = .genesis := by
  unfold Controls.Z
  change (if _ then st.fg.J else st.fg.F) = .genesis
  rw [hF, hJ]
  split <;> rfl

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1290–1297. Class (iii).
DC: INTENTIONAL; concrete full-domain membership from the internal witness. -/
private theorem fixture_full_mem (st : State 1) (hF : st.fg.F = .genesis)
    (hJ : st.fg.J = .genesis) (hmax : st.fg.h_max = 1)
    (B : FGBlock (Fin 1)) (hB : B ∈ st.fg.TF) : B ∈ fullTree params st := by
  apply (KitFG.mem_filteredFromView (heightView params) (controls params st) st.fg.TF B).mpr
  refine ⟨hB, ?_, ?_, B, hB, KitFG.preceq_refl _, fixture_height st hmax B⟩
  · change FGBlock.Preceq st.fg.F B
    rw [hF]
    exact KitFG.genesis_preceq B
  · rw [fixture_root st hF hJ]
    exact KitFG.genesis_preceq B

/-- Blueprint 21 H.6:942–953, H.17:3008–3011
(design 798–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; finite erasure correspondence without computing heightView. -/
private theorem target_base (C : Block) :
    C ∈ target.base.blocks ↔ ∃ B ∈ target.fg.TF, eraseFG B = C := by
  simp only [target, source, Finset.mem_insert, Finset.mem_singleton, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((rfl | rfl | rfl) | rfl | rfl)
    all_goals first | exact ⟨.genesis, by simp, rfl⟩ | exact ⟨cutFG, by simp, rfl⟩ |
      exact ⟨parentFG, by simp, rfl⟩ | exact ⟨oldFG, by simp, rfl⟩ |
      exact ⟨proposalFG, by simp, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    rcases hB with rfl | rfl | rfl | rfl | rfl <;> simp [eraseFG]

/-- Blueprint 21 H.6:942–953, H.17:3008–3011
(design 798–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; the admitted finite path is parent closed. -/
private theorem target_parent_mem : ∀ B ∈ target.fg.TF, B.parent ∈ target.fg.TF := by
  intro B hB
  have hb : B = .genesis ∨ B = cutFG ∨ B = parentFG ∨ B = oldFG ∨ B = proposalFG := by
    simpa only [target, source, Finset.mem_insert, Finset.mem_singleton] using hB
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- Blueprint 21 H.6:927–953 (design 783–809); spec 1373–1385. Class (iii).
DC: INTENTIONAL; the target has no leases, so its live start is Z. -/
private theorem target_start : ay params target = .genesis := by
  unfold ay liveRoot
  rw [fixture_root target rfl rfl]
  rfl

/-- Blueprint 21 H.6:942–953, H.17:3008–3011
(design 798–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; source A is the first permitted witness choice. -/
private theorem parent_witness :
    ∃ W : FGBlock (Fin 1),
      ((W ∈ source.fg.TF ∧ eraseFG W = (eraseFG proposalFG).parent) ∨
        (W ∈ target.fg.TF ∧ eraseFG W = eraseFG proposalFG)) ∧
      (controls params target).lo ≤ (heightView params W).h :=
  ⟨parentFG, Or.inl ⟨by decide +kernel, rfl⟩, fixture_height target rfl parentFG⟩

/-- Blueprint 21 H.6:935–953, H.17:3008–3011
(design 791–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; E.proposal_mem instance with source A, absent new b at source. -/
private theorem proposal_mem_source_parent :
    eraseFG proposalFG ∈ T params target 4 ∧ proposalFG ∉ source.fg.TF := by
  refine ⟨fgsa_retained_proposal_mem params source target target_base target_parent_mem
    ?_ 4 (eraseFG proposalFG) (by decide +kernel) rfl ?_ parent_witness, by decide +kernel⟩
  all_goals rw [target_start]; exact block_genesis_preceq _

/-- Blueprint 21 H.6:935–953, H.17:3008–3011
(design 791–809,2869–2872); spec 1286–1293. Class (iii).
DC: INTENTIONAL; E.proposal_mem instance with admitted target b itself. -/
private theorem proposal_mem_target_proposal : eraseFG proposalFG ∈ T params target 4 := by
  apply fgsa_retained_proposal_mem params source target target_base target_parent_mem
    ?_ 4 (eraseFG proposalFG) (by decide +kernel) rfl ?_
    ⟨proposalFG, Or.inr ⟨by decide +kernel, rfl⟩, fixture_height target rfl proposalFG⟩
  all_goals rw [target_start]; exact block_genesis_preceq _

/-- Blueprint 21 H.6:942–958 (design 798–814); spec 1286–1293. Class (iii).
DC: INTENTIONAL; an old child exists at A in the actual target domain. -/
private theorem old_endpoint :
    (eraseFG oldFG).parent? = some (eraseFG parentFG) ∧ (eraseFG oldFG).slot < 4 ∧
    eraseFG oldFG ∈ T params target 4 := by
  refine ⟨rfl, by decide, ?_⟩
  apply fgsa_walk_domain_of_witness_view params target (voterBlocks params target 4) oldFG oldFG
    (fun B hB => (target_base _).mpr ⟨B, hB, rfl⟩)
    (fun _ h => (Finset.mem_filter.mp h).1) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ (KitFG.preceq_refl _) (fixture_height target rfl oldFG)
  rw [fixture_root target rfl rfl]
  exact KitFG.genesis_preceq _

/-- Blueprint 21 H.6:927–939, H.17:2957–2964
(design 783–795,2818–2825); spec 1373–1385. Class (iii).
DC: INTENTIONAL; the actual source start differs from its FG root. -/
private theorem source_start_above_root :
    RetainedWalk.ap params source ≠ RetainedWalk.z params source := by
  have hm := fixture_full_mem source rfl rfl rfl cutFG (by decide +kernel)
  have ht : decide (∃ B ∈ fullTree params source, eraseFG B = eraseFG cutFG) = true :=
    decide_eq_true ⟨cutFG, hm, rfl⟩
  have hz := fixture_root source rfl rfl
  change liveRoot params source ≠ eraseFG (controls params source).Z
  unfold liveRoot
  rw [hz]
  change ([ (eraseFG cutFG, (0 : Time), (100 : Time)) ].filterMap
    (fun row => if source.base.now < row.2.2 &&
      decide (∃ B ∈ fullTree params source, eraseFG B = row.1) then some row.1 else none)).foldl
      (fun best b => if best.depth < b.depth || (best.depth == b.depth && best.root < b.root)
        then b else best) .genesis ≠ .genesis
  simp only [List.filterMap_cons, List.filterMap_nil, ht]
  decide +kernel

/-- Blueprint 21 H.6:947–958 (design 798–814); spec 1276–1302. Class (iii).
DC: INTENTIONAL; the retained interval is nonempty. -/
private theorem strict_cut : Block.Prec (eraseFG cutFG) (eraseFG parentFG) := by decide +kernel

/-- Blueprint 21 H.6:956–958 (design 812–814); spec 1276–1302. Class (iii).
DC: INTENTIONAL; the old rival is in the target domain but is not eligible.
The band arm is excluded through the height bridge, without height reduction. -/
private theorem old_ineligible : et params target 4 (eraseFG oldFG) = false := by
  have hband : ¬ ∃ P ∈ target.fg.TF, eraseFG P = (eraseFG oldFG).parent ∧
      (heightView params P).h < (controls params target).lo := by
    rintro ⟨P, -, -, hh⟩
    exact Nat.not_lt_of_ge (fixture_height target rfl P) hh
  unfold et eligible
  simp only [hband, decide_false, Bool.false_or]
  decide +kernel

/-- Blueprint 21 H.6:956–958 (design 812–814); spec 1276–1302. Class (iii).
DC: INTENTIONAL; all eight endpoint fields for the concrete finite stores. -/
private theorem endpoint_instance :
    RetainedEndpointGeometry params source target 4 (eraseFG proposalFG) := by
  have members (C : Block) (hm : C ∈ T params target 4) :
      C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG ∨
        C = eraseFG oldFG ∨ C = eraseFG proposalFG := by
    have hb := (List.mem_filter.mp hm).1
    simpa only [target, source, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc] using hb
  refine ⟨?_, proposal_mem_target_proposal, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro C hm hp hs he
    rcases members C hm with rfl | rfl | rfl | rfl | rfl
    · cases hp
    · have hn : (eraseFG cutFG).parent? ≠ some (eraseFG proposalFG).parent := by decide +kernel
      exact (hn hp).elim
    · have hn : (eraseFG parentFG).parent? ≠ some (eraseFG proposalFG).parent := by decide +kernel
      exact (hn hp).elim
    · rw [old_ineligible] at he
      cases he
    · exact (Nat.lt_irrefl 4 hs).elim
  · intro C hm hs
    rcases members C hm with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | (exfalso; revert hs; decide +kernel)
  · intro C hm
    rcases members C hm with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro C hm hp
    rcases members C hm with rfl | rfl | rfl | rfl | rfl
    all_goals exfalso; revert hp; decide +kernel

/-- Blueprint 21 H.6:956–958 (design 812–814); spec 1276–1302. Class (iii).
DC: INTENTIONAL; apply S7 to a terminal source with a real old target child. -/
private theorem exact_geometry_instance :
    ExactHeadGeometry params target 4 (eraseFG proposalFG) := by
  apply fgsa_exactHeadGeometry_of_retained_endpoint params source target 4 _ ?_ endpoint_instance
  intro C hm hp
  have hb := (List.mem_filter.mp hm).1
  have hc : C = .genesis ∨ C = eraseFG cutFG ∨ C = eraseFG parentFG := by
    simpa only [source, List.mem_cons, List.not_mem_nil, or_false] using hb
  rcases hc with rfl | rfl | rfl
  all_goals exfalso; revert hp; decide +kernel

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 00:126–142; 21 H.22:3109–3114. Class (iii).
DC: INTENTIONAL; compile the full supplier-to-schedule application.
This is a conditional run instance; the fixture has no certified heights. -/
private theorem scheduled_instance
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hWalkSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s))
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D b Kc) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b := by
  exact exactService_head_of_retained_proposal E rho hE hDelta s hip b raw sup rows hem D
    (fgsa_retainedExactHead_geometry_on_run E rho hE hN hDelta s hWalkSync hScoreSync
      hx hip hseat b raw sup rows hem D hreads)

end AvailableChain.FGSA.Run.Tests.RetainedEndpoint
