module
public import AvailableChainSAPC.Proofs.CleanService

/-!
Remaining clean inclusion obligation after round 17. No default target
imports this module. This is not an assumption added to any contract.

`RunClean.clean_run_invariant` proves every uncapped event step.
`RunClean.clean_safety_from_engine` proves safety and monotonicity of both
base outputs from plain Sleepy. `RunCleanActiveTransfer` discharges the
active-PC premise of the shared history induction from earlier HEAD
invariants; the chronological induction now supplies these invariants.
The old event and PC-transfer obligations are therefore removed here.

Common exact honest proposal HEAD choices remain open. Raw proposal
service and both 6Δ inclusion conclusions already follow from those
choices and the now-proved invariant. Round 16 proves common proposal
counts, equivocation, scores, ordinary view transport, and active F4
floors. Round 17 proves frozen/carried PC comparison, common active targets
and anchors, finite-root placement on the ordinary proposer walk, and the
ordinary proposal parent in either mode. Exact disabled HEAD choices,
including an active proposer with a disabled reader, are also proved.
Exact active choices still need eligible-path reflection for the enlarged
active tree and final walk transport. The rejected free-path statement
remains in `RejectedCleanInduction` with its checked counterexample.
-/

@[expose] public section
namespace AvailableChain.SAPC.Pending
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Raw service and common proposal counts/floors are proved. Exact
HEAD choice remains to be established from the unchanged regime. -/
def CleanProposalChoicesObligation {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) : Prop :=
  E.Δ = p.Δ → ∀ rho t₀,
    SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀ →
    JointCleanInvariant p E rho rho.events.length →
    ∀ r, t₀ < proposalTime p r → HonestAwakeProposer E rho r →
      gateTime p r ≤ rho.horizon → ∃ b,
        HonestProposalAt E (sapcInterface p).toInterface rho r b ∧
        ∀ v ∈ rho.honest, (headData p rho r v).target = b

end AvailableChain.SAPC.Pending
end
