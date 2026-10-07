module
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient -- shake: keep (#print axioms)
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.PCSA.Run.decodeSafetyRow
#print axioms AvailableChain.PCSA.Run.pcsaCoreReadsWith
#print axioms AvailableChain.PCSA.Run.pcsaCoreReadsWith_def
#print axioms AvailableChain.PCSA.Run.pcsaCoreReadsWith_on
#print axioms AvailableChain.PCSA.Run.pcsaSafetyCertificateLaws
#print axioms AvailableChain.PCSA.Run.pcsaSafetyReads
#print axioms AvailableChain.PCSA.Run.pcsaSafetyReads_def
#print axioms AvailableChain.PCSA.Run.pcsaSafetyWireLaws
#print axioms AvailableChain.PCSA.Run.pcsa_decodeSafetyRow_def
#print axioms AvailableChain.PCSA.Run.pcsa_safetyEnabled_def
#print axioms AvailableChain.PCSA.Run.pcsa_safetyProposalErase_def
#print axioms AvailableChain.PCSA.Run.pcsa_safetyProposalRows_def
#print axioms AvailableChain.PCSA.Run.pcsa_safety_carried
#print axioms AvailableChain.PCSA.Run.pcsa_safety_clock_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_decode_auth
#print axioms AvailableChain.PCSA.Run.pcsa_safety_decode_encode
#print axioms AvailableChain.PCSA.Run.pcsa_safety_decoded_visible
#print axioms AvailableChain.PCSA.Run.pcsa_safety_encode_injective
#print axioms AvailableChain.PCSA.Run.pcsa_safety_erase_prefix
#print axioms AvailableChain.PCSA.Run.pcsa_safety_finalityView_eq
#print axioms AvailableChain.PCSA.Run.pcsa_safety_initial_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_initial_tf
#print axioms AvailableChain.PCSA.Run.pcsa_safety_output_eq
#print axioms AvailableChain.PCSA.Run.pcsa_safety_own_core
#print axioms AvailableChain.PCSA.Run.pcsa_safety_own_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_process_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_restart_record
#print axioms AvailableChain.PCSA.Run.pcsa_safety_restart_tf
#print axioms AvailableChain.PCSA.Run.pcsa_safety_row_auth
#print axioms AvailableChain.PCSA.Run.pcsa_safety_source_mem
#print axioms AvailableChain.PCSA.Run.safetyEnabled
#print axioms AvailableChain.PCSA.Run.safetyProposalErase
#print axioms AvailableChain.PCSA.Run.safetyProposalRows
#print axioms AvailableChain.PCSA.pcsa_safety_delete_core
#print axioms AvailableChain.PCSA.pcsa_process_F_mono
#print axioms AvailableChain.PCSA.Run.pcsa_safety_process_F
#print axioms AvailableChain.PCSA.Run.pcsaSafetyOrderLaws

#print axioms AvailableChain.PCSA.pcsa_safety_admitBlock_fg_cases
#print axioms AvailableChain.PCSA.pcsa_safety_process_fg_cases
#print axioms AvailableChain.PCSA.pcsa_safety_normalize_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_reconcile_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_collect_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_poolAckRaw_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_fold_poolAckRaw_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_admitRow_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_fold_admitRow_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_poolAck_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_admitBlock_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_process_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_gateFrom_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_clockPre_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_clock_metadata
#print axioms AvailableChain.PCSA.pcsa_safety_decode_block_payload
#print axioms AvailableChain.PCSA.pcsa_safety_process_TF

namespace AvailableChain.PCSA.Run
open AvailableChain.FGCompose AvailableChain.SimplexFG
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyWireLaws (pcsaSafetyReads .on p c) := pcsaSafetyWireLaws .on p c
example (p : Params) {In : Type} (c : AppCodec In) (B : FGBlock (Fin p.n))
    (h : B ∈ ((pcsaCoreReadsWith .on p c).core (pcsaWith .on p c).init).fg.TF) :
    B = .genesis := pcsa_safety_initial_tf .on p c B h
example (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    (pcsaSafetyReads .on p c).record
      ((pcsaWith .on p c).restore ((pcsaWith .on p c).durable nd)) = nd.record :=
  pcsa_safety_restart_record .on p c nd
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyWireLaws (pcsaSafetyReads .idle p c) := pcsaSafetyWireLaws .idle p c
example (p : Params) {In : Type} (c : AppCodec In) (B : FGBlock (Fin p.n))
    (h : B ∈ ((pcsaCoreReadsWith .idle p c).core (pcsaWith .idle p c).init).fg.TF) :
    B = .genesis := pcsa_safety_initial_tf .idle p c B h
example (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    (pcsaSafetyReads .idle p c).record
      ((pcsaWith .idle p c).restore ((pcsaWith .idle p c).durable nd)) = nd.record :=
  pcsa_safety_restart_record .idle p c nd
example (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGCoreLaws (pcsaCoreReadsWith m p c)
example (m : FGMode) (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (pcsaSafetyReads m p c) p.E p.cfg
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (pcsaCoreReadsWith .on p c) (pcsaSafetyReads .on p c) :=
  pcsaSafetyOrderLaws .on p c
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (pcsaCoreReadsWith .idle p c) (pcsaSafetyReads .idle p c) :=
  pcsaSafetyOrderLaws .idle p c
end AvailableChain.PCSA.Run

end
