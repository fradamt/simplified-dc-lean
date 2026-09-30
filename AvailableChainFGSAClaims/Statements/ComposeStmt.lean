module
public import AvailableChainFGSAClaims.Statements.Reads

@[expose] public section

/-! P3 App. A.1/A.10, F0.8a. The generic composition rules stay in Gen:
Gen.Pure.AGRule.holds, Gen.Pure.firstFailure_holds, Gen.Pure.WindowRule.holds
(Proofs/Pure/FirstBad). Gen.Pure.RetroAt and Gen.V2.Pending supply the
retrospective and deadline predicates. No F2 invariant enters this module. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) (rho : V2.Run V (fgsa p c))

/-- Study §5.4 (895–903): event indices between consecutive post-gate cuts.
Slot zero starts at index zero. Consumers: F5, H.14–H.17, with Gen.Pure.WindowRule. -/
def windowIdx (s : Slot) (i : Nat) : Prop :=
  (match s with
   | 0 => True
   | s' + 1 => afterTicksIdx rho (SA.gateTime p.toParams s') ≤ i) ∧
  i < afterTicksIdx rho (SA.gateTime p.toParams s)

end AvailableChain.FGSA.Run
end
