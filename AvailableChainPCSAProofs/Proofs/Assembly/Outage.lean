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
labels from the four pending-label Clean claims. -/
theorem pcsa_cleanCutChainItems_of (p : Params) (hne : CleanResultsNonemptyClaim p)
    (hres : CleanResultsChainPendingClaim p) (hheads : CleanHeadsAbovePendingClaim p)
    (hdis : CleanDisseminationPendingClaim p) : CleanCutChainItems p := by
  rw [CleanCutChainItems_def]
  rw [CleanResultsNonemptyClaim_def] at hne
  rw [CleanResultsChainPendingClaim_def] at hres
  rw [CleanHeadsAbovePendingClaim_def] at hheads
  rw [CleanDisseminationPendingClaim_def] at hdis
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact ⟨hne c m E rho b₀ ΔF hC hf hfr, hres c m E rho b₀ ΔF hC hf hfr,
    hheads c m E rho b₀ ΔF hC hf hfr, hdis c m E rho b₀ ΔF hC hf hfr⟩

/-- [pcsa34-r4.3 §5.2.2, §5.5 steps 1–2] The Clean facts at the cut from CI
(i) on one label, the locks below `S`, the pending-label Clean claims and the
HEAD past the cut. -/
theorem pcsa_cleanCutItems_of (p : Params) (hCI : CleanInvariantClaim p)
    (hLB : LeaseBelowRecordClaim p) (hne : CleanResultsNonemptyClaim p)
    (hres : CleanResultsChainPendingClaim p) (hheads : CleanHeadsAbovePendingClaim p)
    (hdis : CleanDisseminationPendingClaim p) (hpast : CleanHeadsPastCutClaim p) :
    CleanCutItems p := by
  have hK := pcsa_cleanCutChainItems_of p hne hres hheads hdis
  rw [CleanCutItems_def]
  rw [CleanCutChainItems_def] at hK
  rw [CleanInvariantClaim_def] at hCI
  rw [LeaseBelowRecordClaim_def] at hLB
  rw [CleanHeadsPastCutClaim_def] at hpast
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  refine ⟨hK c m E rho b₀ ΔF hC hf hfr, ?_, ?_, hpast c m E rho b₀ ΔF hC hf hfr⟩
  · intro j hj x hx y hy X Y hX hY
    exact ((hCI c m E rho b₀ ΔF hC hf hfr j hj).resultsChain x hx y hy j j X Y le_rfl le_rfl
      hX hY).2 rfl
  · intro x hx t h0 ht ℓ hℓ hl
    exact (hLB c m E rho b₀ ΔF hC hf hfr x hx t h0 ht ℓ hℓ hl).1

/-- [pcsa34-r4.3 §5.2.3] CLEAN block receipt, proved in the Outage lane. -/
theorem pcsa_cleanBlockReceipt (p : Params) : CleanBlockReceiptClaim p := by
  rw [CleanBlockReceiptClaim_def]
  intro V _ _ In c m E rho b₀ ΔF hC _ hfr v hv T B _ hTb hB y hy t ht
  exact pcsa_healthy_block_receipt E rho hC hfr v hv T B hTb hB y hy t ht

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (a)] The relay item from block receipt
(`pcsa_cleanBlockReceipt`). -/
theorem pcsa_cleanRelayItems_of (p : Params) : CleanRelayItems p := by
  have hrecv := pcsa_cleanBlockReceipt p
  rw [CleanRelayItems_def]
  rw [CleanBlockReceiptClaim_def] at hrecv
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact pcsa_heldPCRelay_of E rho hC hfr (hrecv c m E rho b₀ ΔF hC hf hfr)

/-- [pcsa34-r4.3 §5.4.2] C8, ARM-healthy, from the relay item and the four
pending-label Clean claims. The relay item follows from block receipt
(`pcsa_cleanBlockReceipt`, `pcsa_cleanRelayItems_of`). -/
theorem pcsa_armHealthy_of_claims (p : Params)
    (hne : CleanResultsNonemptyClaim p) (hres : CleanResultsChainPendingClaim p)
    (hheads : CleanHeadsAbovePendingClaim p) (hdis : CleanDisseminationPendingClaim p) :
    ArmHealthyClaim p :=
  pcsa_armHealthy p
    (pcsa_cleanArmItems_of p (pcsa_cleanRelayItems_of p)
      (pcsa_cleanCutChainItems_of p hne hres hheads hdis))

/-- [pcsa34-r4.3 §5.5 steps 1–2] The slow boundary facts, under the lag of
`Outage₂`, from CI, `LeaseBelowRecordClaim`, the pending-label Clean claims and
the HEAD past the cut. -/
theorem pcsa_cleanSlowItems_of_claims (p : Params) (hCI : CleanInvariantClaim p)
    (hLB : LeaseBelowRecordClaim p) (hne : CleanResultsNonemptyClaim p)
    (hres : CleanResultsChainPendingClaim p) (hheads : CleanHeadsAbovePendingClaim p)
    (hdis : CleanDisseminationPendingClaim p) (hpast : CleanHeadsPastCutClaim p) :
    CleanSlowItems p :=
  pcsa_cleanSlowItems_of p (pcsa_cleanCutItems_of p hCI hLB hne hres hheads hdis hpast)

/-- [pcsa34-r4.3 §5.5] C10, slow P1, from the relay item, CI,
`LeaseBelowRecordClaim`, the pending-label Clean claims and the HEAD past the
cut. The relay item follows from block receipt (`pcsa_cleanBlockReceipt`,
`pcsa_cleanRelayItems_of`). -/
theorem pcsa_slowP1_of_claims (p : Params)
    (hCI : CleanInvariantClaim p) (hLB : LeaseBelowRecordClaim p)
    (hne : CleanResultsNonemptyClaim p) (hres : CleanResultsChainPendingClaim p)
    (hheads : CleanHeadsAbovePendingClaim p) (hdis : CleanDisseminationPendingClaim p)
    (hpast : CleanHeadsPastCutClaim p) : PCSASlowP1Claim p :=
  pcsa_slowP1 p (pcsa_cleanArmItems_of p (pcsa_cleanRelayItems_of p)
      (pcsa_cleanCutChainItems_of p hne hres hheads hdis))
    (pcsa_cleanSlowItems_of_claims p hCI hLB hne hres hheads hdis hpast)

end AvailableChain.PCSA.Run
end
