module
public import AvailableChainFGCompose.Statements.CoreReads
public import AvailableChainFGCompose.Statements.Selection
public import AvailableChainFGSARun.Proofs.FGSource
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainFGSAClaims.Statements.Fold
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSA.Proofs.Head

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
def fgsaCoreReads (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }
theorem fgsaCoreReads_def (p : Params) {In : Type} (c : AppCodec In) : fgsaCoreReads p c =
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none } := by
  rfl
theorem fgsa_eventReads_eq_compose {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) :
    (@cutPred V In P t = @FGCompose.cutPred V In P t) ∧
    afterTicksIdx rho t = FGCompose.afterTicksIdx rho t ∧ timeIdx rho t = FGCompose.timeIdx rho t ∧
    afterTicks E rho t = FGCompose.afterTicks E rho t ∧
    preTick E rho x t = FGCompose.preTick E rho x t ∧
    postClock E rho x t = FGCompose.postClock E rho x t ∧
    postTick E rho x t = FGCompose.postTick E rho x t :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem fgsa_chainRows_eq_compose (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (X : FGBlock (Fin p.n)) (cut : Time) :
    ChainRowsBefore p c E rho X cut =
      FGCompose.ChainRowsBefore (fgsaCoreReads p c) E rho X cut := by
  rw [fgsaCoreReads_def]
  rfl
theorem fgsaCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (fgsaCoreReads p c) where
  clock_fg nd t := FGSA.clock_fg p nd.st t
  clock_proposals nd t := FGSA.clock_proposals p nd.st t
  clock_rowPool nd t := FGSA.clock_rowPool p nd.st t
  process_tf nd o := (FGSA.process_cumulative p nd.st (toWire p o)).1
  process_proposals nd o := (FGSA.process_cumulative p nd.st (toWire p o)).2.2.2.2.1
  process_rowPool nd o := (FGSA.process_cumulative p nd.st (toWire p o)).2.2.2.2.2
  own_core nd o := rfl
  source_mem nd C h := by
    change FGSA.fgSource p nd.st = some C at h
    change C ∈ nd.st.fg.TF
    have hsource : FGSA.fgSource p nd.st = jointSource p nd.st := by
      rw [jointSource_def, domainR_def, frameR_def, treeT_def]
      change FGSA.deepest ((FGSA.fullTree p nd.st).filter _) =
        FGSA.deepest ((FGSA.fullTree p nd.st).filter _)
      apply congrArg (FGSA.deepest (n := p.n))
      apply Finset.filter_congr
      intro B _
      rw [sourceCandidates_def, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
        Finset.mem_filter, List.mem_toFinset]
      cases leaseOf nd.st (eraseFG B) <;> rfl
    rw [hsource, jointSource_def] at h
    have hm := (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ h).1).1
    rw [domainR_def, KitFG.mem_filteredFromView, treeT_def] at hm
    exact hm.1
  erase_inj := eraseFG_injective
theorem fgsaHeadLaws (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    FGCompose.FGHeadLaws (fgsaCoreReads p c) E rho where
  head_mem i x t s := by
    have hinv := (storeBundle_postClock E rho i x t).cstore
    have hm := headVote_stored p _ hinv s
    obtain ⟨B, hB, hBe⟩ := (hinv.baseTree _).mp hm
    exact ⟨B, hB, hBe⟩
  parent_closed i x B hB := (cstoreInv_stateBefore E rho i x).fg.closed B hB

open Gen.Pure

private def p0c1_observations (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0c1_selection (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionReads (fgsa p c) p.n where
  select nd := (FGSA.fgSource p nd.st, fgBlockOf nd.st (fgHead p nd.st))
  clientInputs nd := fgInputs p nd.st

private def p0c1_deeper (a b : Block) : Block :=
  if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a

private theorem p0c1_deeper_depth (a b : Block) :
    a.depth ≤ (p0c1_deeper a b).depth ∧ b.depth ≤ (p0c1_deeper a b).depth := by
  unfold p0c1_deeper
  split
  · next h =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact ⟨Nat.le_of_lt (of_decide_eq_true h), le_rfl⟩
    · exact ⟨(beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1).le, le_rfl⟩
  · next h =>
    have hn : ¬ a.depth < b.depth := by
      intro hab
      exact h (by simp only [hab, decide_true, Bool.true_or])
    exact ⟨le_rfl, Nat.le_of_not_gt hn⟩

private theorem p0c1_fold_depth (xs : List Block) (init : Block) :
    init.depth ≤ (xs.foldl p0c1_deeper init).depth ∧
      ∀ b ∈ xs, b.depth ≤ (xs.foldl p0c1_deeper init).depth := by
  induction xs generalizing init with
  | nil => exact ⟨le_rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons x xs ih =>
    obtain ⟨hi, hb⟩ := ih (p0c1_deeper init x)
    refine ⟨(p0c1_deeper_depth init x).1.trans hi, ?_⟩
    intro b hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (p0c1_deeper_depth init b).2.trans hi
    · exact hb b hm


private theorem p0c1_fold_covers (xs : List Block) (init B : Block) (hB : B ∈ xs)
    (hinit : Block.Compatible init B)
    (hxs : ∀ b ∈ xs, Block.Compatible b B) :
    Block.Preceq B (xs.foldl (fun a b =>
      if a.depth < b.depth || (a.depth == b.depth && a.root < b.root) then b else a) init) := by
  change Block.Preceq B (xs.foldl p0c1_deeper init)
  have hdepth := (p0c1_fold_depth xs init).2 B hB
  have hmem := foldl_select_mem (fun (a b : Block) =>
    a.depth < b.depth || (a.depth == b.depth && a.root < b.root)) xs init
  change xs.foldl p0c1_deeper init = init ∨ xs.foldl p0c1_deeper init ∈ xs at hmem
  have hcompat : Block.Compatible (xs.foldl p0c1_deeper init) B := by
    rcases hmem with he | hm
    · rw [he]; exact hinit
    · exact hxs _ hm
  rcases Bool.or_eq_true_iff.mp hcompat with h | h
  · have he := prefix_eq_of_depth _ _ h hdepth
    rw [he]
    exact block_preceq_refl _
  · exact h


private theorem p0c1_liveRoot_of_lease (p : Params) (st : State p.n) {B : Block}
    (hBS : Block.Preceq B st.base.stableRecord)
    (hbelow : LeaseBelowOutputStore p st) {dl : Time}
    (hlease : FGSA.leaseOf st B = some dl) (hlive : st.base.now < dl)
    (hdom : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B) :
    Block.Preceq B (FGSA.liveRoot p st) := by
  obtain ⟨β, hβ, hβB⟩ := hdom
  have hZB : Block.Preceq (eraseFG (FGSA.controls p st).Z) B := by
    rw [← hβB]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p) _ _ β).mp hβ).2.2.1
  obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hlease
  have hrow := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have hkey : row.1 = B := beq_iff_eq.mp hp
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ β ∈ FGSA.fullTree p st, eraseFG β = row.1)
    then some row.1 else none)
  have hBm : B ∈ targets := by
    apply List.mem_filterMap.mpr
    refine ⟨row, hrow, ?_⟩
    have htime : st.base.now < row.2.2 := hdl ▸ hlive
    have hdB : ∃ β ∈ FGSA.fullTree p st, eraseFG β = B := ⟨β, hβ, hβB⟩
    simp only [htime, decide_true, hkey, hdB, Bool.and_self, ite_true]
  change Block.Preceq B (targets.foldl p0c1_deeper (eraseFG (FGSA.controls p st).Z))
  apply p0c1_fold_covers targets _ B hBm
  · exact block_compatible_of_common hZB (block_preceq_refl B)
  · intro b hb
    obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hb
    split at he
    · next hc =>
      have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
      have hbe : row.1 = b := Option.some.inj he
      rw [← hbe]
      exact block_compatible_of_common (hbelow row hr hl) hBS
    · cases he


private theorem p0c1_source_head (p : Params) (st : State p.n)
    (hReach : Reachable p st) {C H : FGBlock (Fin p.n)}
    (hC : FGSA.fgSource p st = some C) (hH : fgBlockOf st (fgHead p st) = some H) :
    FGBlock.Preceq C H := by
  have hmem := Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1
  have hguard := Bool.and_eq_true_iff.mp hmem.2
  have hlive := hguard.2
  cases hl : leaseOf st (eraseFG C) with
  | none => simp only [hl, Bool.false_eq_true] at hlive
  | some dl =>
    simp only [hl, decide_eq_true_eq] at hlive
    have hbelow := leaseBelowOutputStore_of_reachable p st hReach
    obtain ⟨row, hfind, hdl⟩ := Option.map_eq_some_iff.mp hl
    have hp := List.find?_some hfind
    have hkey : row.1 = eraseFG C := beq_iff_eq.mp hp
    have hCS : Block.Preceq (eraseFG C) st.base.stableRecord := by
      rw [← hkey]
      exact hbelow row (List.mem_of_find?_eq_some hfind) (hdl ▸ hlive)
    have hroot := p0c1_liveRoot_of_lease p st hCS hbelow hl hlive ⟨C, hmem.1, rfl⟩
    have hhead : Block.Preceq (liveRoot p st) (fgHead p st) :=
      liveRoot_preceq_headInTree p st _ _ _
    have hHe := ((fgBlockOf_spec p st (storeBundle_of_reachable p st hReach).cstore
      (fgHead p st) H).mp hH).2
    exact eraseFG_preceq_iff.mp (hHe ▸ block_preceq_trans hroot hhead)

private theorem p0c1_selection_laws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSelectionLaws (fgsaCoreReads p c) (p0c1_observations p c)
      (p0c1_selection p c) (fun nd => Reachable p nd.st) (Window.headFields p p.K_W) where
  source_eq _ _ := rfl
  head_eq _ _ := rfl
  head_held nd hReach := by
    have hinv := (storeBundle_of_reachable p nd.st hReach).cstore
    obtain ⟨H, hm, he⟩ := (hinv.baseTree _).mp (fgHead_stored p nd.st hinv)
    exact ⟨H, (fgBlockOf_spec p nd.st hinv _ H).mpr ⟨hm, he⟩, hm⟩
  source_viable nd C _ hC := by
    exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hC).1).1
  source_head nd C H hReach he := by
    exact p0c1_source_head p nd.st hReach (congrArg Prod.fst he) (congrArg Prod.snd he)
  client_eq nd H _ hH := by
    change (fgSource p nd.st, _) = (fgSource p nd.st, Window.headFields p p.K_W H)
    change fgBlockOf nd.st (fgHead p nd.st) = some H at hH
    simp only [hH]

private theorem p0c1_action_selection_laws (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hvalid : V2.D.ExecutionValid E rho) :
    FGCompose.FGActionSelectionLaws E rho (p0c1_selection p c) p.actionTime
      (fun x r _ => x ∈ rho.honest ∧ E.awake x (p.actionTime r) = true)
      (fun _ _ nd => joinedNow p nd.st = true) where
  nonempty_joined x r nd C hread _ hC := by
    obtain ⟨pre, hpre, rfl⟩ := Option.map_eq_some_iff.mp hread
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hpre
    have ht := V2.D.Run.tickIdx?_spec hi
    cases hj : joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
        (p.actionTime r)).st with
    | true => rfl
    | false =>
      have hn := fgsa_fgAction_unjoined_source_none E rho hvalid ht hj
      change FGSA.fgSource p _ = some C at hC
      rw [hn] at hC
      cases hC

#print axioms p0c1_source_head
#print axioms p0c1_selection_laws
#print axioms p0c1_action_selection_laws

end AvailableChain.FGSA.Run

end
