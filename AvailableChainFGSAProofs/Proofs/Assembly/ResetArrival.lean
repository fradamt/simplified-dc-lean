module
public import AvailableChainFGSAProofs.Proofs.Healing.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum

public section

/-! Blueprint 21 H.11:1572–1595; S5 J8 R2. Assembly of the frozen reset-arrival
statement: the Healing reset witness (R1) with the Foundations source producer.
DC: INTENTIONAL row-delay bound; H0Reset and SA clocks unchanged. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Blueprint 21 H.11:1757–1759; S5 J8 R1/R2 INLINE discharge.
DC: SAME the frozen F1.5 source-discipline package (sourceDiscipline_base),
with heights already read through heightView; no old derive read. -/
theorem healing_reset_emittedName (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : BaseSet p c E rho)
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    (ha : HonestRowAt p c E rho j x r a) (he : namedEntry a.payload.height_pair = some e) :
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = ((heightView p C).h, (heightView p C).T_h.root) ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
  have hsd : SourceDisciplineBaseAt p c E rho :=
    sourceDiscipline_base p c E rho (pt := ()) ⟨hb⟩
  delta SourceDisciplineBaseAt at hsd
  obtain ⟨e', C, G, he', hC, hh, _, hG, hCG, hf⟩ := hsd.2.2 j x r a ha
  obtain rfl : e = e' := Option.some.inj (he.symm.trans he')
  exact ⟨C, G, hC, hh, hG, hCG, hf⟩

/-- Blueprint 21 H.11:1572–1595; S5 J8 R2. Frozen ResetArrivalStatement.
DC: INTENTIONAL row-delay bound; H0Reset and SA clocks unchanged.
Named HG.5 input `hsearch` (all runs): producer healing_frontierSearch_of_set below;
reset_row and reset_first come from it. -/
theorem healing_resetArrival (p : Params) (G ΔF : Time)
    (hsearch : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      FrontierSearchStatement p c E rho G ΔF) :
    ResetArrivalStatement p G ΔF := by
  intro hδ V _ _ In c E rho hset hbound hhor
  exact healing_resetWitness p c E rho
    (healing_reset_emittedName p c E rho hset.base)
    hset hδ hbound (hsearch c E rho hset hbound) hhor

/-- Blueprint 21 HG.5, H.11:1695–1800; plan S5 HG5-BRIDGE (J8 review should-fix 2).
DC: SAME HG.5 on every healing run. HealingSet supplies recovery; named producers
discharge every standing port of healing_frontierSearch. -/
theorem healing_frontierSearch_of_set (p : Params) {V : Type} [DecidableEq V] [Fintype V]
    {In : Type} (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hset : HealingSet p c E rho G ΔF) :
    FrontierSearchStatement p c E rho G ΔF := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMono p c E rho
  have crossing := fgsa_rXing p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have qc := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  have rowCoverage := rowPermission_covered E rho hset.base hset.fault
  exact healing_frontierSearch E rho hset mono crossing
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ) qc
    (healing_tRepair E rho hset mono crossing qc writes)
    (healing_tCommon E rho hset mono crossing writes rowCoverage)
    (healing_tPerm E rho hset mono crossing writes) writes rowCoverage
    (fgsa_tRowsReceipt p c E rho ΔF hset.base.delta hset.base.valid
      hset.base.noRestart hset.sync hset.deltaF)
    (fgsa_batchCoverage p ΔF .progress c E rho)
    (fgsa_foldTrichotomy_progress p) faultQ
    (kmid_honest_quorum p c rho hset.base.linked hset.fault)

/-- Blueprint 21 H.11:1572–1595; plan S5 HG5-BRIDGE. Frozen ResetArrivalStatement.
DC: SAME R2 with the HG.5 producer; no named input remains. -/
theorem healing_resetArrivalStatement (p : Params) (G ΔF : Time) :
    ResetArrivalStatement p G ΔF :=
  healing_resetArrival p G ΔF fun c E rho hset _ => healing_frontierSearch_of_set p c E rho hset

end AvailableChain.FGSA.Run
end
