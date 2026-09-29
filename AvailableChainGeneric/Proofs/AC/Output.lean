module
public import AvailableChainGeneric.Statements.AC.Reads
public import AvailableChainEngineV2.Conditions.Schedule

public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V : Type} {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

/-- The three output cases on an interval with no local restart
(aclaws-inputs.md:9–13; GLY C.1 item 2). -/
theorem output_step_of_restartFree (A : ACReads E rho) (laws : ACLaws A)
    (i : Nat) (x : V) (hrf : restartFree rho x i (i + 1)) :
    A.output (i + 1) x = A.output i x ∨ GateWrite A i x ∨ Reconcile A i x := by
  rcases laws.output_step i x with same | gate | reconcile | reset
  · exact Or.inl same
  · exact Or.inr (Or.inl gate)
  · exact Or.inr (Or.inr reconcile)
  · obtain ⟨t, ht, _⟩ := reset
    exact (hrf i t (Nat.le_refl i) (Nat.lt_succ_self i) ht).elim

end AvailableChain.Gen.AC
