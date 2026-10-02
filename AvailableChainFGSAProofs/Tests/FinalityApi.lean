module
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (adapter examples)

public section

namespace AvailableChain.FGSA.Run.Tests.FinalityApi

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- Each example applies one proved body with exactly its d35 premises on W.
example (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key)) (hnr : V2.D.NoRestart rho)
    (x : V) (hx : x ∈ rho.honest) (t t' : Time) (htt : t ≤ t') :
    Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
      (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fgsa_apiFinalizedMonotonicityClaim_body p c E rho hs hnr x hx t t' htt

example (hp : FinalizedSafetyPrem p c E rho ()) :
    Gen.Pure.CompatOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) ∧
    Gen.Pure.MonoOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) :=
  fgsa_apiFinalizedSafetyClaim_body p c E rho () hp

example (hp : FinalizedSafetyPrem p c E rho ()) : RXing p c E rho :=
  fgsa_apiFinalLockClaim_body p c E rho () hp

end AvailableChain.FGSA.Run.Tests.FinalityApi
end
