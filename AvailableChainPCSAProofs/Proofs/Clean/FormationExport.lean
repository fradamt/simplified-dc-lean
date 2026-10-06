module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationWalk
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame
public import AvailableChainPCSAProofs.Proofs.Clean.FormationGate
public import AvailableChainPCSAProofs.Proofs.Clean.FormationCount
public import AvailableChainPCSAProofs.Proofs.Clean.FormationAck
public import AvailableChainPCSAProofs.Proofs.Clean.FormationPC
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSource

public section

/-! Formation boundary exports (pcsa34-r4.3a §§5.3, 5.7).
Neither FormationClaim nor FormationSourceClaim is exported.
Tests.FormationCounterexample checks a finite run satisfying F1–F7
in which both conclusions fail. F4 lacks the retained target_prefix
(BestAncestry) needed to reach the proposer's lock-selected parent.
The imported conditional helpers remain valid. The C3 store inputs are
hAckAdmit, hAckPoolMono, hPCCollect, and hFreezeKeep.
The main Clean.Export module is owned by the other Clean writer. -/

end
