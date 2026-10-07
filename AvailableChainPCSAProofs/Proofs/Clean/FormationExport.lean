module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationInputs
public import AvailableChainPCSAProofs.Proofs.Clean.FormationHeads
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCompose
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
public import AvailableChainPCSAProofs.Proofs.Clean.FormationOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCollect
public import AvailableChainPCSAProofs.Proofs.Clean.FormationView
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFreeze
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSourceRetention
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCollection
public import AvailableChainPCSAProofs.Proofs.Clean.FormationTerminal

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
receipt, early-view and A2 facts. FormationInputs derives frozen identity
receipt from target-body receipt.
It derives carried presence from exact metadata and PC validity.
Shared body relay closes the old frozen targets. Shared honest-proposal
receipt gives the metadata; stored metadata gives the vote-read body.
pcsa_formation_preFreeze_of_prem needs the premise, the retained path,
early HEAD receipt and ack admission. The proposer lists
and root-mode score transport are proved.
The old release witness fails F4.
FormationCompose proves parts 1–4 with named run inputs.
Assembly.Formation composes them with the named late gate counts.
No whole claim is exported. FormationSourceRetention derives snapshot and
target retention. The stamped-PC part of C7 supplies the source when
connected to C1 PC target uniqueness. No source retention input remains.
FormationRetention closes hAckPoolMono from NoRestart.
FormationFreeze closes hFreezeKeep and supplies PC consumers.
FormationTerminal closes hStop from handler slot bounds and sorted run times.
The retained HEAD consumer still needs the receipt, resolution, path and child inputs.
FormationOrigins closes hFrozenPCOrigin at the actual early read.
FormationCollection closes hPCCollect from the required early N counts.
Its PC consumers need only hAckAdmit from C3. FormationHeads closes honest pool non-equivocation.
FormationInputs now needs early resolved HEAD receipt, without an equivocation input.
Raw-HEAD carriage and the current child follow from body/metadata receipt.
Seven retained path/support inputs and late gate counts remain open.
The main Clean.Export module is owned by the other Clean writer. -/

end
