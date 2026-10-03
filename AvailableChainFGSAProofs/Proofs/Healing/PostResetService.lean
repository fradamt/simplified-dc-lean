module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant

public section

/-! S5 J6 / J6-2, H.17 exact HEAD and its retained carrier.
S1 STOP: `ExactServiceGateGeometry.opening_domain` needs a retained
representative at the gate. `PostResetFProv` gives the source of a high J,
but gives no retained-domain floor for the proposal at that later read.
The cone supplies its domain bounds only at HEAD ticks. The fields
`PostResetLeaseSafe`, `PostResetRawTransfer`, and `PostResetFProv` at the cut
do not supply this missing gate fact. No extra geometry premise is added.
S2 projects H3 from the named `PostResetService` field at a complete cut.
It does not prove that field; S1 remains open.
S3 is proved in `PostResetGate`: raw transfer at the complete cut gives
the whole-result guard through lease persistence from the source release
read. The H6 adapter does not use the cone or an honest proposal. -/

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
  obtain ⟨D, hreads⟩ := healing_postReset_retainedReads p c E rho hrec.base.valid
    hrec.base.noRestart hDelta w hcone v hv hHeadHorizon hScoreSync hx hip hseat
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
carrier; the opening-source projection at the later gate is the open S1 item
(ExactServiceGateGeometry.opening_domain). -/
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

/-- J6-2: exact HEAD gives the covered-prefix field of the gate receipt.
This derivation does not give the gate's active F floor or retained domain. -/
theorem healing_postReset_gate_covered_prefix [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hGateHorizon : SA.gateTime p.toParams v ≤ rho.horizon) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head v)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true →
      ∀ K, V2.D.Run.emits E rho (rho.seatOf (.base (.head v)) q)
        (ofHead p ⟨.seat (.head v) q, K⟩) (SA.voteTime p.toParams v) →
        Block.Preceq Q K := by
  intro q hy _ K he
  have hhead := healing_postReset_exactHead E rho hrec w hreset hcone v Q hp hv
    (postReset_head_horizon p c rho hGateHorizon)
  have heq := exactService_emitted_head E rho hrec.base.valid.toScheduleWellFormed
    v Q hhead q hy K (SA.voteTime p.toParams v) he
  rw [heq]
  exact block_preceq_refl Q

/-- J6-2 S2: project exact service from the named carrier at its cut.
The proposal, HEAD, and post-gate cuts are explicit. The gate witness
keeps its event and passed guard when its prefix bound is removed. -/
theorem healing_postReset_exactService_at_cut
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (i : Nat) (hservice : PostResetService p c E rho w i)
    {v : Slot} {Q : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hProposalCut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i)
    (hHeadCut : SA.voteTime p.toParams v ≤ rho.horizon →
      timeIdx rho (SA.voteTime p.toParams v) ≤ i)
    (hGateCut : SA.gateTime p.toParams v ≤ rho.horizon →
      afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i) :
    ExactService p c E rho v Q := by
  rw [PostResetService_def] at hservice
  obtain ⟨hhead, hgate⟩ := hservice v Q hp hv hProposalCut
  refine ⟨fun hh => hhead hh (hHeadCut hh), ?_⟩
  intro hg x hx
  obtain ⟨hraw, ⟨j, _, ht, hpass⟩, hfast, hstable, hsource⟩ :=
    hgate hg (hGateCut hg) x hx
  exact ⟨hraw, ⟨j, ht, hpass⟩, hfast, hstable, hsource⟩

/-- J6-2 S2: a carrier cut at or after the run's length gives the H3 shape.
The cut may exceed the run's length. Each time cut is bounded by the length
of the event list; the two horizon guards remain in ExactService. -/
theorem healing_postReset_exactService
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (i : Nat) (hcomplete : rho.events.length ≤ i)
    (hservice : PostResetService p c E rho w i) : H3 p c E rho w := by
  intro v Q hp hv
  have hProposalCut : timeIdx rho (SA.proposalTime p.toParams v) ≤ i :=
    (List.length_filter_le _ _).trans hcomplete
  have hHeadCut : timeIdx rho (SA.voteTime p.toParams v) ≤ i :=
    (List.length_filter_le _ _).trans hcomplete
  have hGateCut : afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i :=
    (List.length_filter_le _ _).trans hcomplete
  exact healing_postReset_exactService_at_cut E rho w i hservice hp hv
    hProposalCut (fun _ => hHeadCut) (fun _ => hGateCut)

end AvailableChain.FGSA.Run
end
