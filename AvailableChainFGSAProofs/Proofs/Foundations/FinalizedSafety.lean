module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable
public import AvailableChainFGSAProofs.Proofs.Foundations.Client
public import AvailableChainFGSAClaims.Statements.Packages.Safety

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Finalized safety at any two honest reads. Gen count_rec converts
faulty.card ≤ (n − 1) / 3 and n > 0 to FaultX, after identity transport.
Local F only extends by fgsa_rMono under NoRestart. -/
theorem fgsa_finalizedSafety (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    {Pt : Type} {pt : Pt} (hp : FinalizedSafetyPrem p c E rho pt)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true := by
  exact fgsa_eventPrefixAgreement p c E rho e e' x y hx hy
    (fgsa_storeSlashableBound_of_faults p c E rho hp.set.linked
      (fgsa_unforgeable_of_base p c E rho hp.set) (Gen.Pure.count_rec p.nPos hp.fault)
      (fgsa_clientSafeAll p c E rho hp.set.linked) e e' x y hx hy)

end AvailableChain.FGSA.Run
end
