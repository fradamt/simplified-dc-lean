module
public import AvailableChainPCSAProofs.Proofs.Shared.FGStore
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient
public import AvailableChainPCSA.Statements.Invariants
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.StoreLaws

public section
namespace AvailableChain.PCSA
open AvailableChain.SimplexFG
variable {n : Nat}

/-- The carried-PC deletion is before the FG update and changes only leases. -/
theorem pcsa_safety_delete_core (st : State n) (cert : PC n) :
    (deleteConflictingLeases st cert).fg = st.fg ∧
    (deleteConflictingLeases st cert).proposals = st.proposals ∧
    (deleteConflictingLeases st cert).rowPool = st.rowPool := by
  rw [deleteConflictingLeases_def]
  exact ⟨rfl, rfl, rfl⟩

end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose
variable {p : Params}

theorem pcsa_safety_finalityView_eq (p : Params) :
    pcsa_finalityView p = FGSA.finalityView p := rfl

theorem pcsaSafetyCertificateLaws (p : Params) :
    KitFG.FGCertificateLaws p.E (FGSA.heightView p) (pcsa_finalityView p) := by
  rw [pcsa_safety_finalityView_eq]
  exact FGSA.fgCertificateLaws p

theorem pcsa_safety_initial_tf (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (B : FGBlock (Fin p.n)) (h : B ∈ ((pcsaCoreReadsWith m p c).core (pcsaWith m p c).init).fg.TF) :
    B = .genesis := by
  rw [pcsaCoreReadsWith_def] at h
  change B ∈ ({.genesis} : Finset (FGBlock (Fin p.n))) at h
  exact Finset.mem_singleton.mp h

theorem pcsa_safety_restart_tf (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (B : FGBlock (Fin p.n))
    (h : B ∈ ((pcsaCoreReadsWith m p c).core
      ((pcsaWith m p c).restore ((pcsaWith m p c).durable nd))).fg.TF) : B = .genesis := by
  rw [pcsaCoreReadsWith_def] at h
  change B ∈ ({.genesis} : Finset (FGBlock (Fin p.n))) at h
  exact Finset.mem_singleton.mp h

/-- The two independent order fields remain valid in both modes. -/
theorem pcsa_safety_erase_prefix (A B : FGBlock (Fin p.n)) (h : FGBlock.Preceq A B) :
    Block.Preceq (PCSA.eraseFG A) (PCSA.eraseFG B) := by
  rw [pcsa_eraseFG_eq]
  exact FGSA.eraseFG_preceq h

theorem pcsa_safety_output_eq (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) : (pcsaSafetyReads m p c).finalizedOut nd =
      (pcsaCoreReadsWith m p c).erase ((pcsaCoreReadsWith m p c).core nd).fg.F := by
  rw [pcsaSafetyReads_def, pcsaCoreReadsWith_def]

/-- Store processing is independent of the honest FG duty mode. -/
theorem pcsa_safety_process_F (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (nd : Node p) (o : Obj p) :
    FGBlock.Preceq ((pcsaCoreReadsWith m p c).core nd).fg.F
      ((pcsaCoreReadsWith m p c).core ((pcsaWith m p c).process nd o)).fg.F := by
  rw [pcsaCoreReadsWith_def]
  change FGBlock.Preceq nd.st.fg.F (PCSA.process p nd.st (toWire p o)).fg.F
  exact pcsa_process_F_mono p nd.st (toWire p o)

/-- All three order fields hold in both FG duty modes. -/
theorem pcsaSafetyOrderLaws (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c) where
  process_F := pcsa_safety_process_F m p c
  erase_prefix := by
    intro A B h
    rw [pcsaCoreReadsWith_def]
    exact pcsa_safety_erase_prefix (p := p) A B h
  output_eq := pcsa_safety_output_eq m p c

/-- The mode-general store producer has the required type. No law is assumed. -/
example (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyStoreLaws (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c)
    (FGSA.heightView p) (pcsa_finalityView p) (fun nd => Reachable p nd.st)

end AvailableChain.PCSA.Run
end
