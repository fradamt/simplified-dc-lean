module
public import AvailableChainPCSAProofs.Proofs.Clean.Export
public import AvailableChainPCSAProofs.Proofs.Outage.Export
public import AvailableChainPCSAProofs.Proofs.PC.Export

public section

/-! Assembly entry for the Outage lane (pcsa34-r4.3 §5.4.1). -/

namespace AvailableChain.PCSA.Run

/-- C8 is available independently of the unfinished claim record. -/
theorem pcsa_armPersistenceClaim (p : Params) : ArmPersistenceClaim p := pcsa_armPersistence p

/-- [pcsa34-r4.3 §5.2.2, §5.2.3, §5.5 step 1] The Clean facts at the pending
labels from the Clean facts at the cut. OPEN: `hK` is a hypothesis (the cone
and the bridge of 5.5 step 2 are not proved). -/
theorem pcsa_cleanCutChainItems_of (p : Params) (hK : CleanCutItems p) :
    CleanCutChainItems p := by
  rw [CleanCutChainItems_def]
  rw [CleanCutItems_def] at hK
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact (hK c m E rho b₀ ΔF hC hf hfr).toCutChain

/-- [pcsa34-r4.3 §5.2.3] CLEAN block receipt, proved in the Outage lane. -/
theorem pcsa_cleanBlockReceipt (p : Params) : CleanBlockReceiptClaim p := by
  rw [CleanBlockReceiptClaim_def]
  intro V _ _ In c m E rho b₀ ΔF hC _ hfr v hv T B _ hTb hB y hy t ht
  exact pcsa_healthy_block_receipt E rho hC hfr v hv T B hTb hB y hy t ht

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (a)] The relay item from block receipt
(`pcsa_cleanBlockReceipt`). -/
theorem pcsa_cleanRelayItems_of (p : Params) : CleanRelayItems p := by
  have hrecv : CleanBlockReceiptClaim p := pcsa_cleanBlockReceipt p
  rw [CleanRelayItems_def]
  rw [CleanBlockReceiptClaim_def] at hrecv
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact pcsa_heldPCRelay_of E rho hC hfr (hrecv c m E rho b₀ ΔF hC hf hfr)

/-- [pcsa34-r4.3 §5.4.2] C8, ARM-healthy, from the relay item and the Clean
facts at the pending labels. The relay item follows from block receipt
(`pcsa_cleanBlockReceipt`, `pcsa_cleanRelayItems_of`). OPEN: `hK` is a
hypothesis (the HEAD cone and pending-label dissemination are not proved). -/
theorem pcsa_armHealthy_of_claims (p : Params) (hK : CleanCutChainItems p) :
    ArmHealthyClaim p :=
  pcsa_armHealthy p (pcsa_cleanArmItems_of p (pcsa_cleanRelayItems_of p) hK)

/-- [pcsa34-r4.3 §5.5] C10, slow P1, from the relay item, the Clean facts at
the pending labels and the slow boundary facts. The relay item follows from
block receipt (`pcsa_cleanBlockReceipt`, `pcsa_cleanRelayItems_of`). OPEN:
`hK` and `hslow` are hypotheses. `pcsa_cleanSlowItems_of` gives `hslow` from
`CleanCutItems` (with the HEAD cone and the clean-gate successor bridge). -/
theorem pcsa_slowP1_of_claims (p : Params) (hK : CleanCutChainItems p)
    (hslow : CleanSlowItems p) : PCSASlowP1Claim p :=
  pcsa_slowP1 p (pcsa_cleanArmItems_of p (pcsa_cleanRelayItems_of p) hK) hslow

end AvailableChain.PCSA.Run
end
