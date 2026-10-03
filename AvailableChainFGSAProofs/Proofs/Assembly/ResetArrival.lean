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

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W2/W4.
DC: SAME all-cut invariant. HealingSet supplies each standing run port.
The cone is used only in the adjacent J6-3 step producers below. -/
private theorem healing_postReset_inv_of_open (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w)
    (stepRL : ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ i, PostResetRawStep p c E rho w i)
    (hcone : PostResetRetainedCone p c E rho w) :
    ∀ i, PostResetInv p c E rho w i := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMono p c E rho
  have crossing := fgsa_rXing p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
  -- O-CONE: the only use site is this pair of J6-3 step producers.
  have steps := fun i => And.intro
    (healing_postReset_openingDomainStep E rho hset w h0r hcone cap
      (rowPermission_covered E rho) crossing origin i)
    (healing_postReset_serviceStep E rho hset w h0r hcone cap
      (rowPermission_covered E rho) mono writes i)
  exact postReset_inv_all p c E rho hset mono
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
    crossing origin cap
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
      hset.base.valid.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
    (cap_finality_head p c E rho) h0r stepRL stepLease stepRaw
    (fun i => (steps i).1) (fun i => (steps i).2)

section HTime
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (hcone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      PostResetRetainedCone p c E rho w)

include stepRL stepLease stepRaw hcone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W2.
DC: SAME strict reset arrival. J7 changes only u and QStar for full H0.
The four inputs have the exact joint-step and retained-cone types. -/
theorem healing_resetArrivalFull_of_open (G ΔF : Time) :
    ResetArrivalFullStatement p G ΔF := by
  intro hClock V _ _ In c E rho hset hbound hhor
  have hΓ : Γ p G = G := hset.gamma_eq
  have hG := hset.gapPos
  have hd := p.deltaPos
  obtain ⟨w, h0r, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
    hset hbound (by linarith)
  have inv := healing_postReset_inv_of_open p c E rho hset h0r
    (stepRL c E rho hset h0r) (stepLease c E rho hset h0r)
    (stepRaw c E rho hset h0r) (hcone c E rho hset h0r)
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have carrier := postReset_tCarrier_reset p c E rho hset
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho) h0r inv
  obtain ⟨u, Q, h0, _⟩ := healing_h0_of p c E rho hset carrier h0r (by linarith)
  exact ⟨{w with u := u, QStar := Q}, h0, harrival⟩

omit stepRL stepLease stepRaw hcone in
/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W3.
DC: SAME statement under HealingTimePrem. The package supplies HealingSet,
LivenessBoundW, and the healing horizon at the original G and ΔF. -/
theorem healing_hTimeClaim_of_statement
    (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact hTime G ΔF hClock c E rho h.set h.bound h.hhor

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W4.
DC: SAME HTimeClaim. The only open inputs are J5-A reset lease and raw steps,
J4A2-2 lease steps, and G-H17 retained cone, under HealingSet and H0Reset. -/
theorem healing_hTimeClaim_of_open : HTimeClaim p := by
  apply healing_hTimeClaim_of_statement p
  intro G ΔF
  have timeBound := healing_timeBound_of_resetArrival p G ΔF
    (healing_resetArrivalStatement p G ΔF)
  have hInput : HealingInputOfH0Statement p G ΔF := by
    apply healing_healingInputOfH0 p G ΔF
    case timeBound => exact timeBound
    case sourcePrefix =>
      intro _ V _ _ In c E rho _ _ _ w h0
      exact h0.source_prefix
    case rows =>
      intro _ V _ _ In c E rho hset _ _
      exact fgsa_tRows p c E rho ΔF hset.base.delta hset.base.valid
        hset.base.noRestart hset.sync hset.deltaF
    all_goals intro hClock V _ _ In c E rho hset hbound hhor w h0
    all_goals
      have inv := healing_postReset_inv_of_open p c E rho hset h0.toH0Reset
        (stepRL c E rho hset h0.toH0Reset) (stepLease c E rho hset h0.toH0Reset)
        (stepRaw c E rho hset h0.toH0Reset) (hcone c E rho hset h0.toH0Reset)
      have faultQ := fgsa_faultQ_of_count p hset.fault
      have mono := fgsa_rMono p c E rho
      have crossing := fgsa_rXing p c E rho hset.base.linked
        (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
      have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
        (fgsa_rStore p c E rho)
      have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
      have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
      have source := sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed
      have high := postReset_tHigh_reset p c E rho hset mono
        (sourceDiscipline_emittedNonempty p c E rho)
        (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
        crossing origin h0.toH0Reset cap source (rowPermission_covered E rho) inv
      have carrier := postReset_tCarrier_reset p c E rho hset cap source
        (rowPermission_covered E rho) h0.toH0Reset inv
      have h2a := postReset_h2A_reset p c E rho hset cap source
        (rowPermission_covered E rho) h0.toH0Reset inv
      have h2p := postReset_h2Prime_reset p c E rho hset cap source
        (rowPermission_covered E rho) h0.toH0Reset crossing origin inv
      have h3 := healing_postReset_exactService E rho w rho.events.length le_rfl
        (inv rho.events.length).service
      have h5 := postReset_h5RawTransfer_body p c E rho h0.toH0Reset
        (fun i => (inv i).raw_transfer)
      have h6 := healing_postReset_h6GateService E rho hset w rho.events.length le_rfl
        (inv rho.events.length).raw_transfer writes
      first
      | exact high
      | exact carrier
      | exact h2a
      | exact h2p
      | exact h3
      | exact h5
      | exact h6
      | have ht := timeBound hClock c E rho hset hbound hhor w h0
        have hΓ : Γ p G = G := hset.gamma_eq
        have hG := hset.gapPos
        have hd := p.deltaPos
        obtain ⟨w₀, h0r, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
          hset hbound (by linarith)
        have hr := healing_reset_rStar_unique p c E rho h0.toH0Reset h0r
        rw [hr] at ht
        have start := healing_postResetStart_of_h0 p c E rho h0
        have h4 := healing_h4 p c E rho hset start h2a h3 h5 inv (by linarith)
        first
        | exact h4
        | exact healing_healed p c E rho start h4 h3
  exact healing_hTime_of p G ΔF
    (healing_resetArrivalFull_of_open p stepRL stepLease stepRaw hcone G ΔF) hInput

end HTime

end AvailableChain.FGSA.Run
end
