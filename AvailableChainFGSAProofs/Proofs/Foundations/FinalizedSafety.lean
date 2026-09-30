module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable
public import AvailableChainFGSAProofs.Proofs.Foundations.Client
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainGeneric.Proofs.Pure.Quorum

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Finalized safety at any two honest reads. Gen count_rec converts
faulty.card ≤ (n − 1) / 3 and n > 0 to FaultX, after identity transport. -/
theorem fgsa_finalizedSafety (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    {Pt : Type} {pt : Pt} (hp : FinalizedSafetyPrem p c E rho pt)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true := by
  rcases fgsa_accountable p c E rho hp.set.linked hp.set.valid.toUnforgeableSignatures
      (fgsa_clientSafeAll p c E rho hp.set.linked) e e' x y hx hy with hc | hf
  · exact hc
  · have hX := (Gen.Pure.count_rec p.nPos hp.fault).lt
    omega

end AvailableChain.FGSA.Run
end
