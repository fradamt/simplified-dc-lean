module
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.FGSA.Run.fgsaSafetyReads
#print axioms AvailableChain.FGSA.Run.fgsa_safetyProposalErase_def
#print axioms AvailableChain.FGSA.Run.fgsa_safetyProposalRows_def
#print axioms AvailableChain.FGSA.Run.safetyProposalErase
#print axioms AvailableChain.FGSA.Run.safetyProposalRows

namespace AvailableChain.FGSA.Run
open AvailableChain.FGCompose
example (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (fgsaCoreReads p c) := fgsaCoreLaws p c
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyWireLaws (fgsaSafetyReads p c)
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (fgsaSafetyReads p c) p.E p.cfg
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyOrderLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
end AvailableChain.FGSA.Run

end
