module
public import AvailableChainGeneric.Proofs.Pure.ScheduleW -- shake: keep (concrete examples and axiom audit commands)

public section

namespace AvailableChain.Gen.Pure

example : FGoodE_W (fun s => 0 < s) 3 3 1 :=
  ⟨by decide, by decide, ⟨9, by decide, by decide, by decide⟩, by decide⟩

example : FGood4_W (fun s => 0 < s) 3 3 1 :=
  ⟨⟨by decide, by decide, ⟨9, by decide, by decide, by decide⟩, by decide⟩, by decide⟩

example : Tail_W (fun s => 0 < s) 3 3 1 :=
  ⟨by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩

/-- Each eligible window has a witness, including the first nonempty search. -/
example : RecFE_W (fun s => 0 < s) 3 3 12 1 12 0 61 1 := by
  refine ⟨by decide, ?_⟩
  intro q hq _ _
  refine ⟨q, ⟨le_rfl, by omega⟩, ?_⟩
  rw [FGoodE_W_def]
  exact ⟨by change (0 : Nat) < q * 3; omega,
    by change (0 : Nat) < (q + 1) * 3; omega,
    ⟨(q + 2) * 3, by omega, le_rfl, by change (0 : Nat) < (q + 2) * 3; omega⟩,
    by change (0 : Nat) < (q + 2) * 3 + 3; omega⟩

example : RecF4_W (fun s => 0 < s) 3 3 12 1 12 0 61 1 := by
  refine ⟨by decide, ?_⟩
  intro q hq _ _
  refine ⟨q, ⟨le_rfl, by omega⟩, ?_⟩
  rw [FGood4_W_def, FGoodE_W_def]
  exact ⟨⟨by change (0 : Nat) < q * 3; omega,
    by change (0 : Nat) < (q + 1) * 3; omega,
    ⟨(q + 2) * 3, by omega, le_rfl, by change (0 : Nat) < (q + 2) * 3; omega⟩,
    by change (0 : Nat) < (q + 2) * 3 + 3; omega⟩,
    by change (0 : Nat) < (q + 1) * 3 + 3; omega⟩

example : (1 : Nat) ≤ 1 ∧ (0 : Time) ≤ 1 * 12 ∧
    ((1 : Time) + 1 + 1) * 12 + 12 + 1 ≤ 61 := by decide

example : FGoodE_W (fun s => 0 < s) 2 2 1 :=
  ⟨by decide, by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩

#print axioms fgood4_W_implies_fgoodE_W
#print axioms recF4_W_implies_recFE_W
#print axioms fgoodE_W_two
#print axioms fgood4_W_two
#print axioms tail_W_two
#print axioms recFE_W_eight_delta
#print axioms recFE_W_extract
#print axioms recFE_W_receipt_lt

end AvailableChain.Gen.Pure
