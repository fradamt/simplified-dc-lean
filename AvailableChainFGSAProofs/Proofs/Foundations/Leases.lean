module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSA.Proofs.LeaseOutput
public import AvailableChainFGSA.Proofs.StoreBundle
public import AvailableChainGeneric.Proofs.V2.Induction

public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- All stored targets, including due rows, are below the current output.
Gen E-10 `invariant_triple` lifts the E-11 store preservation lemmas.
T7.5 supplies `CStoreInv` and `NestOK` through the reachable store bundle. -/
theorem fgsa_storedTargetsBelowOutput (i : Nat) (x : V) :
    StoredTargetsBelowOutput p (storeAt p c E rho i x) := by
  have h := Gen.V2.invariant_triple (P := fgsa p c)
    (fun nd : Node p => Reachable p nd.st ∧ StoredTargetsBelowOutput p nd.st)
    ⟨Reachable.init, storedTargetsBelowOutput_init p⟩
    (fun nd t h => ⟨Reachable.tick t h.1,
      storedTargetsBelowOutput_clock p nd.st t
        (storeBundle_of_reachable p nd.st h.1).cstore
        (storeBundle_of_reachable p nd.st h.1).nest h.2⟩)
    (fun nd o h => ⟨Reachable.deliver (toWire p o) h.1,
      storedTargetsBelowOutput_process p nd.st (toWire p o)
        (storeBundle_of_reachable p nd.st h.1).cstore h.2⟩)
    (fun _ _ h => h)
    (fun _ _ => ⟨Reachable.init, storedTargetsBelowOutput_init p⟩)
    E rho i x
  exact h.2

end AvailableChain.FGSA.Run
end
