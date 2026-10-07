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
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCollect
public import AvailableChainPCSAProofs.Proofs.Clean.FormationView
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFreeze
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSourceRetention

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
view bound at every honest early reader. Root-form carriage closes the PC
target alias gap: its installing call now handles the real PC for relay.
The alias regression checks installation, handling and all seven early acks.
FormationView proves signed proposal metadata uniqueness and conditional
receipt, early-view and A2 facts. Frozen receipt and carried presence remain
explicit inputs. The proposer lists and root-mode score transport are proved.
The old release witness fails F4.
No whole claim is exported. FormationSourceRetention derives snapshot and
target retention. The stamped-PC part of C7 supplies the source when
connected to C1 PC target uniqueness. No source retention input remains.
FormationRetention closes hAckPoolMono from NoRestart.
FormationFreeze closes hFreezeKeep and supplies PC consumers.
The C3 inputs remain hAckAdmit and hPCCollect.
The main Clean.Export module is owned by the other Clean writer. -/

end
