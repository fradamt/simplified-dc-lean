module
public import AvailableChainPCSAClaims.Claims.Clean
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit
public import AvailableChainPCSAProofs.Proofs.Clean.CommonResolution
public import AvailableChainPCSAProofs.Proofs.Clean.HeadPersistence
public import AvailableChainPCSAProofs.Proofs.Clean.HeadStamps
public import AvailableChainPCSAProofs.Proofs.Clean.HeadReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.HeadTransport
public import AvailableChainPCSAProofs.Proofs.Clean.HeadRelay
public import AvailableChainPCSAProofs.Proofs.Clean.BodyStamps
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport
public import AvailableChainPCSAProofs.Proofs.Clean.ResolutionDomain
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBody
public import AvailableChainPCSAProofs.Proofs.Clean.BodyReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPersistence
public import AvailableChainPCSAProofs.Proofs.Clean.TreeReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.BodyAdmission
public import AvailableChainPCSAProofs.Proofs.Clean.TargetCollect
public import AvailableChainPCSAProofs.Proofs.Clean.StepVote
public import AvailableChainPCSAProofs.Proofs.Clean.StepAck
public import AvailableChainPCSAProofs.Proofs.Clean.AckRun
public import AvailableChainPCSAProofs.Proofs.Clean.StepGate
public import AvailableChainPCSAProofs.Proofs.Clean.StepPC
public import AvailableChainPCSAProofs.Proofs.Shared.Dissemination
public import AvailableChainPCSAProofs.Proofs.Shared.CleanPC

public import AvailableChainPCSAProofs.Proofs.Clean.BackwardInputs

public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt

public import AvailableChainPCSAProofs.Proofs.Clean.CountTransport

public import AvailableChainPCSAProofs.Proofs.Clean.GateCounts

public import AvailableChainPCSAProofs.Proofs.Clean.GateReads

public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths

public import AvailableChainPCSAProofs.Proofs.Clean.ResultPaths

public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport

public import AvailableChainPCSAProofs.Proofs.Clean.HeadEvidence

public import AvailableChainPCSAProofs.Proofs.Clean.HeadBody

public section

/-! Clean store support and snapshot claim exports (pcsa34-r4.3; proof plan §5). -/

namespace AvailableChain.PCSA.Run

/-- The snapshot contains exactly the PCs held after the freeze ticks. -/
theorem pcsa_snapshotStamp (p : Params) : PCSnapshotStampClaim p := by
  intro V _ _ In c m E rho h y hy s hs
  exact snapshot_afterTicks E rho h.valid.toScheduleWellFormed h.delta y hy s hs

end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- CI at the predecessor supplies the root premise for the next honest HEADs. -/
theorem pcsa_clean_next_head_above [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (s : Slot) (hCI : CleanInvariantAt p c E rho s)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (x y : V) (hx : x ∈ rho.honest) (X H : Block)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hH : HonestHeadAt p c E rho y (s + 1) H) : Block.Preceq X H := by
  exact pcsa_next_head_above_result_of_root E rho h.base hF h.healthy x y hx s X H hc hX hH
    (fun R hR => hCI.roots y hH.1 R hR x hx X hX)
end AvailableChain.PCSA.Run

end
