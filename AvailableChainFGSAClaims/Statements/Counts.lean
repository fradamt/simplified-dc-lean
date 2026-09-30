module
public import AvailableChainGeneric.Statements.V2.Reads

@[expose] public section

namespace AvailableChain.FGSA.Run

variable {V In : Type} [DecidableEq V] {P : V2.ProtocolSpec In}

-- faulty, awakeHonest, and HonestSlot are Gen.V2 declarations.
/-- Honest nodes awake at some time in the closed interval. -/
noncomputable def awakeHonestIn (E : Generic.Env V) (rho : V2.Run V P)
    (a b : Time) : Finset V := by
  classical
  exact rho.honest.filter (fun v => ∃ t, a ≤ t ∧ t ≤ b ∧ E.awake v t = true)

/-- The honest proposer emits the block at its proposal time. -/
def HonestProposal (E : Generic.Env V) (rho : V2.Run V P) (I : V2.Interface P)
    (s : Slot) (B : Block) : Prop :=
  Gen.V2.HonestSlot rho I s ∧ ∃ o,
    V2.Run.emits E rho (V2.proposerOf rho I s) o (V2.proposalTime I s) ∧
    I.block o.payload = some B

end AvailableChain.FGSA.Run
end
