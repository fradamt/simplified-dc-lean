module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery
public import AvailableChainFGSAProofs.Proofs.Healing.RegressionFixture

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.ReplayObligations
open AvailableChain.SimplexFG

-- These exact existential goals are OPEN. No theorem supplies their witnesses.
def k3Replay : Prop := ∃ rho : V2.D.Run (Fin 4) (fgsa StaleLeaseReplay.p3 unitCodec),
  RecoverySleep₂ StaleLeaseReplay.p3 unitCodec ReplayClocks.env1 rho 8 1 ∧
  38 ≤ rho.horizon ∧
  PhaseInterval StaleLeaseReplay.p3 unitCodec ReplayClocks.env1 rho 21 26 1
    (some .genesis) false ∧
  PhaseBody StaleLeaseReplay.p3 unitCodec ReplayClocks.env1 rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p3).erase ∧
  ¬ Transfers StaleLeaseReplay.p3 unitCodec ReplayClocks.env1 rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p3).erase 26

def k4Replay : Prop := ∃ rho : V2.D.Run (Fin 4) (fgsa StaleLeaseReplay.p4 unitCodec),
  RecoverySleep₂ StaleLeaseReplay.p4 unitCodec ReplayClocks.env1 rho 8 1 ∧
  38 ≤ rho.horizon ∧
  PhaseInterval StaleLeaseReplay.p4 unitCodec ReplayClocks.env1 rho 21 30 1
    (some .genesis) false ∧
  PhaseBody StaleLeaseReplay.p4 unitCodec ReplayClocks.env1 rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p4).erase ∧
  ¬ Transfers StaleLeaseReplay.p4 unitCodec ReplayClocks.env1 rho 5
    (StaleLeaseReplay.bodyB StaleLeaseReplay.p4).erase 30

def slowReplay : Prop := ∃ rho : V2.D.Run (Fin 7) (fgsa SlowLeaseReplay.params unitCodec),
  RecoverySleep₂ SlowLeaseReplay.params unitCodec ReplayClocks.env7 rho 8 1 ∧
  1018 ≤ rho.horizon ∧
  ∃ J, PhaseInterval SlowLeaseReplay.params unitCodec ReplayClocks.env7 rho 1001 1010 3
    (some J) false ∧
  PhaseBody SlowLeaseReplay.params unitCodec ReplayClocks.env7 rho 251 SlowLeaseReplay.B.erase ∧
  ¬ Transfers SlowLeaseReplay.params unitCodec ReplayClocks.env7 rho 251
    SlowLeaseReplay.B.erase 1010

def splitCertificate
    (rho : V2.D.Run (Fin 7) (fgsa SplitBatchReplay.params unitCodec)) (horizon : Time) : Prop :=
  rho.horizon = horizon ∧
  RecoverySleep₂ SplitBatchReplay.params unitCodec ReplayClocks.envSplit rho 16 2 ∧
  PhaseInterval SplitBatchReplay.params unitCodec ReplayClocks.envSplit rho 2008 2058 3
    none true ∧
  ∃ Q, HonestProposal ReplayClocks.envSplit rho (fgsaInterface SplitBatchReplay.params unitCodec)
    254 Q ∧ ¬ ExactService SplitBatchReplay.params unitCodec ReplayClocks.envSplit rho 254 Q

def splitReplay (horizon : Time) : Prop :=
  ∃ rho, splitCertificate rho horizon

def splitExtensions : Prop := ∃ first second,
  splitCertificate first 2070 ∧ splitCertificate second 2080 ∧
  first.events.take (afterTicksIdx first 2058) = second.events.take (afterTicksIdx second 2058)

/-- A concrete incompatible HEAD suffices to refute the old Transfers obligation. -/
theorem transfers_fail_of_head {p : Params} {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p unitCodec))
    {s r : Slot} {B H : Block} {v : Time} {x : V}
    (hx : x ∈ rho.honest) (hsr : s + 1 ≤ r) (hrv : SA.voteTime p.toParams r ≤ v)
    (hhead : headAtLabel p unitCodec E rho x r = some H) (hbad : ¬ Block.Preceq B H) :
    ¬ Transfers p unitCodec E rho s B v :=
  fun h => hbad (h.1 x r H hx hsr hrv hhead)

end AvailableChain.FGSA.Run.Tests.ReplayObligations
end

#print axioms AvailableChain.FGSA.Run.Tests.ReplayObligations.transfers_fail_of_head
