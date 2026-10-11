module
public import AvailableChainFGCompose.Statements.CoreReads
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
end AvailableChain.FGSA.Run

end
