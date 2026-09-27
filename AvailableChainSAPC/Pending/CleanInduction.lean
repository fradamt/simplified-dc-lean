module
public import AvailableChainSAPC.Proofs.CleanService

/-!
Remaining proof obligations after round 13. No default target imports this
module. These definitions are not assumptions added to any contract.
The rejected free-path statement is kept in `RejectedCleanInduction`.

`JointCleanInvariant` has no path argument. Both its source closure and
its continuation use actual run events. The shared SA induction proves
ordered genuine history once the active-PC transfer condition below is
supplied. Batch preservation and finite-root compatibility are proved.
Round 13 proves the complete capped event induction, including early/gate
source comparison, ordered history, and the final incomplete HEAD. Local
reverse receipts remove the following-gate horizon premise. The uncapped
steps below still require first-use disablement and mixed-mode transfer.
Common exact proposal choices remain open in both fault scopes.
-/

@[expose] public section
namespace AvailableChain.SAPC.Pending
open AvailableChain.Generic AvailableChain.Statements.Generic

def JointEventStep {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (e : Event V (sapc p).Object) : Prop :=
  ∀ i, rho.events[i]? = some e → JointCleanInvariant p E rho i →
    JointCleanInvariant p E rho (i + 1)

/-- No cap is added. Early and the preceding gate are one actual clock;
HEAD and release are also one clock. -/
def CleanEventObligations {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) : Prop :=
  E.Δ = p.Δ → ∀ rho t₀,
    SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀ →
    (∀ v r, JointEventStep p E rho (.tick v (earlyTime p r))) ∧
    (∀ v r, JointEventStep p E rho (.tick v (voteTime p r))) ∧
    (∀ v r, JointEventStep p E rho (.tick v (gateTime p r))) ∧
    (∀ v r, JointEventStep p E rho (.tick v (proposalTime p r)))

/-- This is the remaining PC-specific input of the shared label
induction. Disabled readers need no selected-PC compatibility premise.
Earlier genuine results already order the finite roots. -/
def CleanPCTransferObligation {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) : Prop :=
  E.Δ = p.Δ → ∀ rho t₀,
    SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀ →
    ∀ r, gateTime p r ≤ rho.horizon →
      GridCO.GenuineExtends (fun v => v ∈ rho.honest)
        (fun s v => SA.confirmation p
          (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r →
      ∀ source ∈ rho.honest, ∀ b,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r =
          some b → ∀ reader ∈ rho.honest, ∀ cert,
        capBroken p (headState p rho (r + 1) reader) = false →
        selectedPC p (headState p rho (r + 1) reader) (r + 1) = some cert →
          Block.Compatible cert.target b

/-- Raw service is now proved from common exact HEADs. Common proposal
merge and choice remain to be established from the unchanged regime. -/
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
