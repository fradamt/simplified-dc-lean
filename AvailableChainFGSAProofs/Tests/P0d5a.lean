module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGCompose.Statements.FrontierSearch

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5aAuditCore (p : Params) {In : Type} (c : AppCodec In) :
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


private theorem p0d5aAuditCoreEq (p : Params) {In : Type} (c : AppCodec In) :
    p0d5aAuditCore p c = fgsaCoreReads p c := by
  rw [fgsaCoreReads_def]
  rfl

private def p0d5aAuditTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5aAuditTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5aAuditTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5aAuditObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5aAuditCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d5aAuditSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

-- The frozen exact-service producer supplies the semantic projection.
-- No post-reset service envelope or generic StrongServed premise is used.
private theorem p0d5aAuditStrong (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (frontier : TFrontier p c E rho) {m : Nat} {t : Time}
    (served : StrongServed p c E rho m t) :
    FGCompose.StrongServed (p0d5aAuditCore p c) (p0d5aAuditSafety p c) E rho
      (p0d5aAuditObs p c) (p0d5aAuditTiming p) (fgsaInterface p c)
      (fun a => a.payload.height_pair) (recoveryStart p E) p.k m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hu, hp, he, hh, hs, hseed, hq, hphase,
    hg, hhor, hcap⟩ := (strongServed_iff p c E rho m t).mp served
  have hseed0 := (frontierSeedQualification_iff p E u q).mp hseed
  obtain ⟨htransfer, hrepair, hopen⟩ :=
    frontier u t m J contested q Q Qfg hu hp he hh hs hseed0 hq hphase hg hhor hcap
  refine ⟨u, J, contested, q, Q, Qfg, hu, hp, he, hh, hs.1, hseed0, hq,
    ?_, hg, hhor, hcap, ?_⟩
  · cases J <;> simpa only [FGCompose.PhaseInterval, PhaseInterval, R_at, frameR_def,
      p0d5aAuditObs, p0d5aAuditTiming, storeAt, FGCompose.timeIdx_def, timeIdx] using hphase
  · refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
    · intro s B hqs hgate hprop
      exact (hrepair s B hqs hgate hprop).1
    · intro r hqr hrt
      obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
      refine ⟨?_, hent, hheight, htime⟩
      intro x hx
      obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := hcov x hx
      have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
      exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

-- Exercise the adapter and retain the same selected non-genesis proposal.
private theorem p0d5aAuditAdapterUse (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (frontier : TFrontier p c E rho)
    {m : Nat} {t : Time} (served : StrongServed p c E rho m t)
    (positive : 1 ≤ m) :
    ∃ q Q Qfg, HonestProposal E rho (fgsaInterface p c) q Q ∧ eraseFG Qfg = Q ∧
      (heightView p Qfg).h = m ∧
      FGCompose.FrontierProposalService (p0d5aAuditCore p c) E rho
        (p0d5aAuditTiming p) q Q ∧
      FGCompose.FrontierLocalService (p0d5aAuditCore p c) (p0d5aAuditSafety p c)
        E rho (p0d5aAuditObs p c) (p0d5aAuditTiming p) (fgsaInterface p c)
        (fun a => a.payload.height_pair) q Q Qfg m t ∧ 1 ≤ m := by
  obtain ⟨_, _, _, q, Q, Qfg, _, hp, he, hh, hs, _, _, _, _, _, _, hl⟩ :=
    p0d5aAuditStrong E rho frontier served
  exact ⟨q, Q, Qfg, hp, he, hh, hs, hl, positive⟩

#print axioms p0d5aAuditCoreEq
#print axioms p0d5aAuditStrong
#print axioms p0d5aAuditAdapterUse
end AvailableChain.FGSA.Run
end
