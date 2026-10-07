module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose -- shake: keep (store-law signature example)
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGCompose.Statements.SafetyClient -- shake: keep (client-law signature example)
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (store-law signature example)

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- PROVISIONAL. These are the actual protocol reads. -/
def fgsaSafetyReads (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut
theorem fgsaSafetyReads_def (p : Params) {In : Type} (c : AppCodec In) :
    fgsaSafetyReads p c =
      { proposalErase := safetyProposalErase p
        proposalRows := safetyProposalRows p
        encode := ofRow p
        decode := RowWire.toRow?
        decodeObject := decodeRowObject p
        fgLabel := .base .fg
        fgSeats := Equiv.refl _
        record := Node.record
        inputs := fun nd => fgInputs p nd.st
        enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
        finalizedOut := finalizedOut } := by
  rfl

/-- The producer fits the provisional store-law signature. No law is assumed. -/
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyStoreLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
    (heightView p) (finalityView p) (fun nd => Reachable p nd.st)

example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (fgsaSafetyReads p c) p.E p.cfg

end AvailableChain.FGSA.Run
end
