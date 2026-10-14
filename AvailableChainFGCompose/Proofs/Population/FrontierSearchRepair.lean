module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGCompose.Statements.Population.FrontierSearch

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair) (Jst : Time) (leaseSlots : Nat)
variable (Ef : Electorate (Fin n)) (obs : FGObservationLaws R O)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

include obs in
/-- Blueprint 21 HG.3. DC: SAME save a complete seed at its actual gate.
The HEAD service and the local service at the gate are explicit leaves. -/
theorem frontierSearch_save_seed_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hp : PhaseInterval R E rho O u D m J contested)
    (hseed : FrontierSeedQualification T leaseSlots E.t_GST u q)
    (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
    (hh : (O.height Qfg).h = m) (hs : FrontierProposalService R E rho T q Q)
    (hg : T.gate q ≤ D)
    (hlocal : FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m (T.gate q)) :
    StrongServedFG R S E rho O T I pair Jst leaseSlots m (T.gate q) := by
  have hu := frontierSearch_seed_after T leaseSlots hT hk hseed
  have huq : u ≤ T.gate q := by
    rw [hT.gate_eq]
    linarith [hT.delta_pos]
  exact ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh, hs, hseed, hu,
    frontierSearch_phase_cut R E rho O hp huq hg, le_rfl, hg.trans hp.2.1,
    frontierSearch_phase_cap R E rho O obs hp hg, hlocal⟩

end AvailableChain.FGCompose
end
