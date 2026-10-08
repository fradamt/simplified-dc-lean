module
public import AvailableChainPCSAProofs.Proofs.Clean.Export
public import AvailableChainPCSAProofs.Proofs.PC.Export
public import AvailableChainPCSAProofs.Proofs.Clean.FormationExport
public section

/-! Formation source composition with the C1 uniqueness export. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}
/-- The stamped Formation PC supplies the source with C1 connected. -/
theorem pcsa_formation_source_of_stamped_pc_c1 (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (r : Nat) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho (r * p.R) N ΔF)
    (hPC : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams (r * p.R)) (r * p.R) N.erase) :
    ∀ y ∈ rho.honest, ∃ B : SimplexFG.FGBlock (Fin p.n),
      actionSourceAt p c E rho y r = some (some B) ∧ eraseFG B = N.erase := by
  have hf : FaultsBelowQA p c rho := by
    rw [FaultsBelowQA_def]
    have hq := (QuarterCap_def p c rho).mp h.quarterCap
    have hn := p.nPos
    change (Gen.V2.Duty.faulty rho).card < (p.n + 1) / 2
    omega
  apply pcsa_formation_source_of_stamped_pc E rho r N ΔF h hPC
  intro y hy A hA B hB hs
  exact pcsa_pcUniqueness p c m E rho h.base hf y hy y hy
    (SA.freezeTime p.toParams (r * p.R)) (SA.freezeTime p.toParams (r * p.R)) A hA B hB hs

/-- C7 composition from the shorter Formation result and the named late counts.
The whole FormationClaim stays open until the run input producers are connected. -/
theorem pcsa_formation (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hInputs : FormationPreFreezeInputs E rho s N)
    (hGateCounts : ∀ y ∈ rho.honest, ∀ st, gateInAt p c E rho y s = some st →
      ∃ H, (awakeHonestLabel p c E rho s).card ≤ H ∧
        FormationGateCounts p st s N.erase H (Gen.V2.Duty.faulty rho).card) :
    FormationConcl p c E rho s N := by
  obtain ⟨hh, hn, ha, hp⟩ := pcsa_formation_preFreeze E rho s N ΔF
    (h.toPreFreeze p c E rho) hInputs
  rw [FormationConcl_def]
  exact ⟨hh, hn, ha, hp, pcsa_formation_gate_of_counts E rho s N ΔF h hGateCounts⟩

/-- Formation parts 1–4 supply the stamped PC for the C1 source connection. -/
theorem pcsa_formation_source_of_preFreeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (r : Nat) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho (r * p.R) N ΔF)
    (hInputs : FormationPreFreezeInputs E rho (r * p.R) N) :
    ∀ y ∈ rho.honest, ∃ B : SimplexFG.FGBlock (Fin p.n),
      actionSourceAt p c E rho y r = some (some B) ∧ eraseFG B = N.erase := by
  have hp := (pcsa_formation_preFreeze E rho (r * p.R) N ΔF
    (h.toPreFreeze p c E rho) hInputs).2.2.2
  exact pcsa_formation_source_of_stamped_pc_c1 E rho r N ΔF h hp


/-- C7 now needs the reduced run inputs and the late gate-count producer. -/
theorem pcsa_formation_of_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hRun : FormationRunInputs E rho s N)
    (hGateCounts : ∀ y ∈ rho.honest, ∀ st, gateInAt p c E rho y s = some st →
      ∃ H, (awakeHonestLabel p c E rho s).card ≤ H ∧
        FormationGateCounts p st s N.erase H (Gen.V2.Duty.faulty rho).card) :
    FormationConcl p c E rho s N := by
  exact pcsa_formation E rho s N ΔF h
    (pcsa_formation_inputs_of_run E rho s N ΔF (h.toPreFreeze p c E rho) hRun) hGateCounts

/-- The reduced run inputs also give the source with C1 already connected. -/
theorem pcsa_formation_source_of_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (r : Nat) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho (r * p.R) N ΔF)
    (hRun : FormationRunInputs E rho (r * p.R) N) :
    ∀ y ∈ rho.honest, ∃ B : SimplexFG.FGBlock (Fin p.n),
      actionSourceAt p c E rho y r = some (some B) ∧ eraseFG B = N.erase := by
  exact pcsa_formation_source_of_preFreeze E rho r N ΔF h
    (pcsa_formation_inputs_of_run E rho (r * p.R) N ΔF (h.toPreFreeze p c E rho) hRun)

/-- C7 with its named OPEN inputs: the frozen raw relay
(`FormationFrozenRawOpen`) and the late gate counts. Early HEAD receipt,
ack admission and the five retained HEAD facts are proved from them. -/
theorem pcsa_formation_of_open (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho s N ΔF)
    (hFrozen : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams s) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams s) = some dst →
      FormationFrozenRawOpen p src dst s)
    (hGateCounts : ∀ y ∈ rho.honest, ∀ st, gateInAt p c E rho y s = some st →
      ∃ H, (awakeHonestLabel p c E rho s).card ≤ H ∧
        FormationGateCounts p st s N.erase H (Gen.V2.Duty.faulty rho).card) :
    FormationConcl p c E rho s N :=
  pcsa_formation E rho s N ΔF h
    (pcsa_formation_preFreeze_inputs_of_frozen E rho s N ΔF (h.toPreFreeze p c E rho) hFrozen)
    hGateCounts

/-- The Formation source with C1 connected needs only the frozen raw
relay. -/
theorem pcsa_formation_source_of_open (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (r : Nat) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPrem p c E rho (r * p.R) N ΔF)
    (hFrozen : ∀ src dst y,
      pcsa_postClock E rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface (r * p.R))
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface (r * p.R)) = some src →
      y ∈ rho.honest → E.awake y (SA.voteTime p.toParams (r * p.R)) = true →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r * p.R)) = some dst →
      FormationFrozenRawOpen p src dst (r * p.R)) :
    ∀ y ∈ rho.honest, ∃ B : SimplexFG.FGBlock (Fin p.n),
      actionSourceAt p c E rho y r = some (some B) ∧ eraseFG B = N.erase :=
  pcsa_formation_source_of_preFreeze E rho r N ΔF h
    (pcsa_formation_preFreeze_inputs_of_frozen E rho (r * p.R) N ΔF (h.toPreFreeze p c E rho)
      hFrozen)

end AvailableChain.PCSA.Run
end
