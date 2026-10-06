module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.FormationWalk
public import AvailableChainPCSAProofs.Proofs.Clean.FormationProposal
public import AvailableChainPCSAProofs.Proofs.Clean.FormationStore
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame
public import AvailableChainPCSAProofs.Proofs.Clean.FormationGate
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCount
public import AvailableChainPCSAProofs.Proofs.Clean.FormationAck
public import AvailableChainPCSAProofs.Proofs.Clean.FormationPC
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSource
public import AvailableChainPCSAProofs.Proofs.Clean.FormationTime

public section

/-! Formation boundaries (pcsa34-r4.3b §§5.3, 5.7).
Corrected F4 reanchors the proposer walk at the common base root and
bounds each actual voter root by the emitted proposal parent.
FormationWalk transfers the path under retained input hypotheses.
FormationStore proves the base/FG domain and stage-1 frame filter facts.
FormationTime proves the local clock bounds. FormationSource proves the
opening, frame activity of held targets, and the unique structural FG lift.
FormationClaim is still false: Tests.FormationAckCounterexample passes
corrected F1–F7 and the four current-slot C3 checks, but a node that wakes
only at e_s refuses the ack because its frozen view conflicts with P.
F3 constrains only nodes awake at v_s. The old release witness fails new F4.
FormationSourceClaim is not refuted by the new run: its source is present.
No whole claim is exported. Source selection still needs an own-slot PC
in the action snapshot, its target identity, and retained target membership.
The C3 inputs remain hAckAdmit, hAckPoolMono, hPCCollect, and hFreezeKeep.
The main Clean.Export module is owned by the other Clean writer. -/

end
