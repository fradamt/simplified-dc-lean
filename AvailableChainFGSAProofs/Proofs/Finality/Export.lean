module
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Finality.CoreServices
public import AvailableChainFGSAProofs.Proofs.Finality.Kernel
public import AvailableChainFGSAProofs.Proofs.Finality.Joined

public import AvailableChainFGSAProofs.Proofs.Finality.Local

public section

namespace AvailableChain.FGSA.Run

/-- Blueprint 01:126–129, plan item 18; lead ruling B30. DC: INTENTIONAL AC service contract.
The Finality lane Export restores the frozen Claims conclusion from the composition
services; Recovery supplies Base₂. The other inputs are not used. -/
theorem fgsa_kernelACSide_W (p : Params) : KernelACSideClaim_W p := by
  intro _ _ _ _ _ _ _ c E rho w hr _ _
  exact fgsa_coreServices E rho hr.base w

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1171–1305 (F1–F9), lead ruling B34: export the forward W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention, exact signed
rows and actual receipt guards. The suppliers retain the lane boundary. -/
theorem fgsa_finalityKernel_W_of (p : Params)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityKernelClaim_W p := by
  intro G ΔF hδ V _ _ In c E rho pt hK
  exact finality_kernel_W_of p c E rho G ΔF hδ pt hK
    (hsel c E rho hK.set.base.valid) (horigin c E rho hK.set.base.valid)
    (hBatch ΔF) (hQC c E rho G ΔF pt hK) (hXing c E rho G ΔF pt hK)
    (hI3 c E rho G ΔF pt hK) (hStrat c E rho G ΔF pt hK)
    (hEmittedSource c E rho G ΔF pt hK) (hcapBefore c E rho G ΔF pt hK)

/-- Paper 00:1119–1134, 22:1171–1305; plan §4: export the joined W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention and receipt.
The joined premise supplies every split supplier premise. -/
theorem fgsa_finalityKernelJoined_W_of (p : Params)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time) (pt : KernelPt),
      KernelPrem_W p c G ΔF E rho pt →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityKernelJoinedClaim_W p := by
  intro G ΔF hδ V _ _ In c E rho pt h
  obtain ⟨w, input, start⟩ := h.start
  let kpt : KernelPt := ⟨w, pt.r⟩
  have hK : KernelPrem_W p c G ΔF E rho kpt := {
    set := h.set
    bound := h.bound
    window := h.window
    start := start
    hhor := h.hhor
    input := input
    services := fgsa_coreServices E rho h.set.base w }
  exact finality_kernel_joined_W_of p c E rho G ΔF hδ pt h
    (hsel c E rho h.set.base.valid) (horigin c E rho h.set.base.valid)
    (hBatch ΔF) (hQC c E rho G ΔF kpt hK) (hXing c E rho G ΔF kpt hK)
    (hI3 c E rho G ΔF kpt hK) (hStrat c E rho G ΔF kpt hK)
    (hEmittedSource c E rho G ΔF kpt hK) (hcapBefore c E rho G ΔF kpt hK)

/-- Paper 22:1371–1400; firstfin plan §5 C. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness. Recovery₂ supplies the inherited kernel suppliers;
the frozen claim keeps its common HealingInput and full horizon. -/
theorem fgsa_finalityLivenessRecFE_W_of (p : Params)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityLivenessRecFEClaim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  exact finality_liveness_FE_W_of p c E rho G ΔF g w hδ pt h
    (hsel c E rho h.set.core.base.valid) (horigin c E rho h.set.core.base.valid)
    (hBatch ΔF) (hQC c E rho G ΔF h.set.core) (hXing c E rho G ΔF h.set.core)
    (hI3 c E rho G ΔF h.set.core) (hStrat c E rho G ΔF h.set.core)
    (hEmittedSource c E rho G ΔF h.set.core) (hcapBefore c E rho G ΔF h.set.core)

/-- Paper 22:1371–1400; firstfin plan §5 C. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness. Recovery₂ supplies the inherited kernel suppliers;
the frozen claim keeps its common HealingInput and full horizon. -/
theorem fgsa_finalityLivenessRecF4_W_of (p : Params)
    (hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho)
    (horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ ΔF, BatchCoverage p ΔF .target)
    (hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    FinalityLivenessRecF4Claim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  exact finality_liveness_F4_W_of p c E rho G ΔF g w hδ pt h
    (hsel c E rho h.set.core.base.valid) (horigin c E rho h.set.core.base.valid)
    (hBatch ΔF) (hQC c E rho G ΔF h.set.core) (hXing c E rho G ΔF h.set.core)
    (hI3 c E rho G ΔF h.set.core) (hStrat c E rho G ΔF h.set.core)
    (hEmittedSource c E rho G ΔF h.set.core) (hcapBefore c E rho G ΔF h.set.core)

end AvailableChain.FGSA.Run
end
