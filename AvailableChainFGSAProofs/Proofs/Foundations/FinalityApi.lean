module
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalizedSafety
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing
public import AvailableChainGeneric.Statements.Pure.Props

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- DC Generic/Claims.lean:61 Consensus.finalizedMonotone; class: INTENTIONAL.
FG restore resets F to genesis, so NoRestart is required.
This body has exactly the premises of the restored monotonicity contract. -/
theorem fgsa_apiFinalizedMonotonicityClaim_body :
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    rho.events.Pairwise (fun a b => a.key ≤ b.key) → V2.D.NoRestart rho →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fun c E rho hs hnr => fgsa_finalizedMonotone p c E rho hs hnr

/-- DC Consensus.finalizedSafe/finalizedMonotone: INTENTIONAL event-prefix reads.
BaseSet and the fault bound supply agreement; NoRestart supplies monotonicity. -/
theorem fgsa_apiFinalizedSafetyClaim_body :
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      FinalizedSafetyPrem p c E rho pt →
        Gen.Pure.CompatOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) ∧
        Gen.Pure.MonoOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) := by
  intro V _ _ In c E rho pt hp
  constructor
  · intro i j x y _ _ hx hy
    exact eraseFG_compatible (fgsa_finalizedSafety p c E rho hp i j x y hx hy)
  · intro i j x _ _ hij hx
    exact eraseFG_preceq (fgsa_rMono p c E rho hp.set.noRestart i j x hx hij).1

/-- DC finalized_preceq_of_height_lt: INTENTIONAL accepted W carrier observation.
BaseSet and the fault bound discharge the strict crossing channel. -/
theorem fgsa_apiFinalLockClaim_body :
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      FinalizedSafetyPrem p c E rho pt → RXing p c E rho := by
  intro V _ _ In c E rho pt hp i j x y K W hx hij hK hKF hW hh
  apply fgsa_finalLock p c E rho hp.set.linked (Gen.Pure.count_rec p.nPos hp.fault)
    hp.set.valid.toUnforgeableSignatures x hx i j hij K hK hKF y W hW
  simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf] using hh

end AvailableChain.FGSA.Run
end
