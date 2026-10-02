module
public import AvailableChainFGSAClaims.Claims.Healing
public import AvailableChainFGSAProofs.Proofs.Shared.Healed
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

/-! Holds claim → claim implications only; its Claims/* imports are an exact L42 exception.
P3 r3.5.8 R5-66. -/

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}
open Gen.Pure (CompatOn MonoOn)

variable {p : Params}

/-- The family-(0) client claim follows from the Linked-only claim. -/
theorem clientSafety_base (h : ClientSafetyClaim p) : ClientSafetyBaseClaim p :=
  fun c E rho _ hb => h c E rho hb.set.linked

theorem cleanHistory_of_cut (h : CleanCutClaim p) : CleanHistoryClaim p :=
  fun c E rho _ pt hc => (h c E rho pt ⟨hc.set.toCleanCut⟩).1

theorem cleanPrefixTruncation_of_cut (h : CleanCutClaim p) : CleanPrefixTruncationClaim p :=
  fun c E rho _ pt hc => (h c E rho pt ⟨hc.set.toCleanCut⟩).2

theorem cleanSafety_outputs (h : CleanSafetyClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {pt : Unit}
    (hc : CleanPrem p c E rho pt ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) ∧
      MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) (fun _ => True) :=
  (h c E rho pt hc).2.2

/-- Blueprint 21 H.20–H.22; f07w-rulings S4.5 DEFAULT REVISED.
DC: additive internal corollary, not a standalone frozen healing claim.
HTimeConcl supplies the input and both bound links. Restrict its healed suffix
to GST + B_HF; no recovery or service premise is added. -/
theorem uniformHealing_of_hTimeConcl (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (h : HTimeConcl p c E rho G ΔF) :
    Healed p c E rho (E.t_GST + B_HF p ΔF G) := by
  obtain ⟨w, input, start, bound⟩ := h
  exact healed_mono_start p c E rho (start.trans bound.le) input.healed

end AvailableChain.FGSA.Run
end
