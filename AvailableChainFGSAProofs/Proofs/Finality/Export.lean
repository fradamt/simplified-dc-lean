module
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAProofs.Proofs.Finality.CoreServices
public import AvailableChainFGSAProofs.Proofs.Finality.TailBatch

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Blueprint 01:126–129, plan item 18; lead ruling B30. DC: INTENTIONAL AC service contract.
The Finality lane Export restores the frozen Claims conclusion from the composition
services; Recovery supplies Base₂. The other inputs are not used. -/
theorem fgsa_kernelACSide_W (p : Params) : KernelACSideClaim_W p := by
  intro _ _ _ _ _ _ _ c E rho w hr _ _
  exact fgsa_coreServices E rho hr.base w

/-- Paper 22:1985–2009 (FT-Tail-W): export the full tail kernel as the frozen claim.
DC: INTENTIONAL: Assembly supplies the existing producers at each Tail premise. -/
theorem fgsa_tailKernel_W_of (p : Params)
    (hOrigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (hqc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      RQCOrigin p c E rho)
    (hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      RMono p c E rho)
    (hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
      (G ΔF : Time) (pt : TailKernelPt p), TailKernelPrem_W p c G ΔF E rho pt →
      RXing p c E rho) :
    TailKernelClaim_W p := by
  intro G ΔF _ V _ _ In c E rho pt hT
  exact tail_kernel_W_full_of G ΔF pt hT
    (hOrigin c E rho G ΔF pt hT)
    (hBatch c E rho G ΔF pt hT)
    (hSOCOVTarget c E rho G ΔF pt hT)
    (hqc c E rho G ΔF pt hT)
    (hI3 c E rho G ΔF pt hT)
    (hStrat c E rho G ΔF pt hT)
    (hEmittedSource c E rho G ΔF pt hT)
    (hcapBefore c E rho G ΔF pt hT)
    (hmono c E rho G ΔF pt hT)
    (hXing c E rho G ΔF pt hT)

end AvailableChain.FGSA.Run
end
