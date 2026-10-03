module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint

public section

/-! S5 J6 A3, H.17 exact HEAD and its retained carrier.
A2 STOP: the allowed inputs do not supply `ExactServiceGateGeometry` at
post-reset gate ticks. In particular, the cone has no gate lease guard or
retained opening representative. `exactService_of_head_recovery` needs this
additional fact; no such premise is added here.
A4 STOP: H6GateService also covers labels with no honest proposal. The
proposal cone does not supply the guard for the whole raw result required
by `fgsa_gate_of_coveringBatch`. No full H0, frontier, or service input is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- H.17: produce retained geometry at actual HEAD ticks. Recovery supplies
synchrony through the explicit HEAD horizon. H0Reset supplies only the GST
bound. There is no additional standing port or INLINE input on this route. -/
theorem healing_postReset_headGeometry [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (v : Slot) (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams v)))
    (hseat : rho.seatOf (.prop v) ⟨0, Nat.one_pos⟩ = x)
    (Q : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop v) ⟨0, Nat.one_pos⟩, .proposal Q raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip) :
    ∃ D : FGBlock (Fin p.n), RetainedExactHeadRunGeometry E rho ip x v D Q := by
  have hGST := postReset_synchronous_window p c E rho w hreset hv
  have hDelta := hrec.base.delta
  have hWalkDeadline : SA.proposalTime p.toParams v - p.Δ + E.Δ ≤
      SA.proposalTime p.toParams v := by rw [hDelta]; exact le_of_eq (sub_add_cancel _ _)
  have hScoreDeadline : SA.proposalTime p.toParams v - p.Δ + E.Δ ≤
      SA.voteTime p.toParams v := by
    rw [hDelta, sub_add_cancel]
    change 4 * p.Δ * (v : Int) ≤ 4 * p.Δ * (v : Int) + p.Δ
    linarith [p.deltaPos]
  have hWalkSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) _ _ hrec.sync (fgsaDelay_nonrow E.Δ _) hGST
    hWalkDeadline (postReset_proposal_horizon p c rho hHeadHorizon)
  have hScoreSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) _ _ hrec.sync (fgsaDelay_nonrow E.Δ _) hGST
    hScoreDeadline hHeadHorizon
  have hs : w.sStar ≤ v := (postReset_source_label_le_sub_two w hv).trans (Nat.sub_le _ _)
  obtain ⟨D, hreads⟩ := healing_postReset_retainedReads p c E rho hrec.base.valid
    hrec.base.noRestart hDelta w hcone v hs hHeadHorizon hScoreSync hx hip hseat
    Q raw sup rows hem
  exact ⟨D, fgsa_retainedExactHead_geometry_on_run E rho hrec.base.valid
    hrec.base.noRestart hDelta v hWalkSync hScoreSync hx hip hseat Q raw sup rows hem D hreads⟩

/-- A3: the HEAD clause of H3, for every honest proposal at v ≥ sStar + 2.
The HEAD deadline is explicit and separate from the later gate deadline. -/
theorem healing_postReset_exactHead [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) :
    ∀ v Q, HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
      SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q := by
  intro v Q hp hv hHeadHorizon
  obtain ⟨ip, x, raw, sup, rows, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  obtain ⟨D, hgeom⟩ := healing_postReset_headGeometry E rho hrec w hreset hcone
    v hv hHeadHorizon hx hip hseat Q raw sup rows hem
  exact exactService_head_of_retained_proposal E rho hrec.base.valid hrec.base.delta
    v hip Q raw sup rows hem D hgeom hHeadHorizon

/-- A3 carrier at the HEAD read: the proposal has an exact erased FG
representative in that reader's retained voter domain. This is the HEAD
carrier; the opening-source projection at the later gate is stopped with A2. -/
theorem healing_postReset_headCarrier [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {y : V} {ih : Nat} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams v))) :
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams v)
    ∃ C : FGBlock (Fin p.n), eraseFG C = Q ∧ C ∈ domainR p dst (voterBlocks p dst v) := by
  intro dst
  obtain ⟨ip, x, raw, sup, rows, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  obtain ⟨D, hgeom⟩ := healing_postReset_headGeometry E rho hrec w hreset hcone
    v hv hHeadHorizon hx hip hseat Q raw sup rows hem
  have hm : Q ∈ erasedList dst (domainR p dst (voterBlocks p dst v)) := by
    rw [fgsa_domainR_eq_storeFrameView]
    exact (hgeom.endpoint y hy ih hih).proposal_mem
  obtain ⟨C, hC, heC⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
  exact ⟨C, heC, hC⟩

end AvailableChain.FGSA.Run
end
