module
public import AvailableChainGeneric.Statements.AC.Reads

@[expose] public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

-- Keep the adopted binder names, including unused proof binders (D01).
set_option linter.unusedVariables false in
/-- Live targets at an honest node are compatible.
Source: step4b-plan.md, S4b-01, Q1 A; GLY r3.14:716–719,1821–1825. -/
def LeaseChainStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
    (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (x : V)
    (hx : x ∈ rho.honest) (l k : Block × Nat × Time)
    (hl : l ∈ A.leases i x) (hk : k ∈ A.leases i x)
    (hll : A.now i x < Lease.deadline l) (hkl : A.now i x < Lease.deadline k),
    Block.Compatible (Lease.target l) (Lease.target k)

set_option linter.unusedVariables false in
theorem LeaseChainStatement_def : LeaseChainStatement =
    (∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
      (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (x : V)
      (hx : x ∈ rho.honest) (l k : Block × Nat × Time)
      (hl : l ∈ A.leases i x) (hk : k ∈ A.leases i x)
      (hll : A.now i x < Lease.deadline l) (hkl : A.now i x < Lease.deadline k),
      Block.Compatible (Lease.target l) (Lease.target k)) := by
  rw [LeaseChainStatement]

set_option linter.unusedVariables false in
/-- A gate retains a prefix protected by a lease that is live at the gate time.
Source: step4b-plan.md, S4b-01, Q1 A; GLY r3.14:716–719,1821–1825. -/
def PendingGateHarmlessStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
    (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (s : Slot) (x : V)
    (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s)))
    (B : Block) (g : Nat) (d : Time) (hr : (B, g, d) ∈ A.leases i x)
    (hd : SA.gateTime A.prm s < d) (hB : Block.Preceq B (A.output i x)),
    Block.Preceq B (A.output (i + 1) x)

set_option linter.unusedVariables false in
theorem PendingGateHarmlessStatement_def : PendingGateHarmlessStatement =
    (∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
      (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (s : Slot) (x : V)
      (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s)))
      (B : Block) (g : Nat) (d : Time) (hr : (B, g, d) ∈ A.leases i x)
      (hd : SA.gateTime A.prm s < d) (hB : Block.Preceq B (A.output i x)),
      Block.Preceq B (A.output (i + 1) x)) := by
  rw [PendingGateHarmlessStatement]

end AvailableChain.Gen.AC
