module
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
end AvailableChain.PCSA.Run
end
