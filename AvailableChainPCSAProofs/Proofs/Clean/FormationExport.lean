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
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRelay

public section

/-! Formation boundaries (pcsa34-r4.3b §§5.3, 5.7).
Corrected F4 reanchors the proposer walk at the common base root and
bounds each actual voter root by the emitted proposal parent.
FormationWalk transfers the path under retained input hypotheses.
FormationStore proves the base/FG domain and stage-1 frame filter facts.
FormationTime proves the local clock bounds. FormationSource proves the
opening, frame activity of held targets, and the unique structural FG lift.
Tests.FormationAckCounterexample labels the old missing-PC run as a relay
regression. The old split fails current F1. The repaired run gives the old
PC to every honest node before the proposal and all seven nodes ack its child.
F3 constrains only nodes awake at v_s. C7 still needs the relay-derived
view bound at every honest early reader. Tests.FormationPcAliasCounterexample
passes the current finite F1–F4 audit but has an early ack split. A PC wire
with a different declared target body can install a real PC without handling
it for relay. Named collision freedom omits unheld PC targets. This is the
current C7 blocker. The old release witness fails F4.
No whole claim is exported. Source selection still needs an own-slot PC
in the action snapshot, its target identity, and retained target membership.
The C3 inputs remain hAckAdmit, hAckPoolMono, hPCCollect, and hFreezeKeep.
The main Clean.Export module is owned by the other Clean writer. -/

end
