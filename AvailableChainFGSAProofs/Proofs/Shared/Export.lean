module
public import AvailableChainFGSAProofs.Proofs.Shared.Release
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAClaims.Claims.Shared

public section

namespace AvailableChain.FGSA.Run

/-- P3 F1b.2, blueprint 02 §2.2 and 21 IF.6. Class (ii), frozen claim assembly.
DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405 `eligible_compatible`.
INTENTIONAL: optional F-anchored active-view results and label-local synchronization
(spec/fgsa-protocol.tex:2496–2513). Export boundary: SYN L50. -/
theorem fgsa_sameLabelClaim (p : Params) : SameLabelClaim p := by
  intro V _ _ In c E rho pt h
  exact fgsa_sameLabel p c E rho h.set.valid h.set.noRestart h.set.delta pt.s h.sync

/-- P3 F1b.3, bp.release.v1(a,c), blueprint 01 §5.
Class (iii), store wrapper. DC counterpart: none; INTENTIONAL SA lifecycle,
spec/fgsa-protocol.tex:2514–2515. Export boundary: SYN L50. -/
theorem fgsa_releaseStoreClaim (p : Params) : ReleaseStoreClaim p :=
  fgsa_release_store p

/-- P3 F1b.3, bp.release.v1(a–c), blueprint 02 §2 and 21 H.1.
Class (ii), v2 authenticity/CStar instance and store assembly.
DC counterpart: none; INTENTIONAL SA lifecycle, spec/fgsa-protocol.tex:2514–2515.
Export boundary: SYN L50. -/
theorem fgsa_releaseClaim (p : Params) : ReleaseClaim p := by
  intro V _ _ In c E rho pt h
  refine ⟨fgsa_releaseStoreClaim p, ?_⟩
  intro i x s B _ _ hheads
  exact ⟨fgsa_release_bound p c E rho h.set.valid h.set.noRestart
    h.set.cstar h.set.delta i x s B hheads, h.lt⟩

end AvailableChain.FGSA.Run
end
