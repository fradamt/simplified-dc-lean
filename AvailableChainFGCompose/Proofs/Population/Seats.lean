module
public import AvailableChainFGCompose.Statements.Population.Seats
public import AvailableChainFGCompose.Statements.SafetyClient

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire : Type}
variable (S : FGSafetyReads P n Wire) (rho : V2.D.Run V P)

/-- Seat honesty and seat faultiness partition the finite FG electorate. -/
theorem fgHonestSeats_eq_compl : FGHonestSeats S rho = (historyFaulty S rho)ᶜ := by
  classical
  ext i
  simp [FGHonestSeats_def, historyFaulty]

/-- A positive quorum threshold supplies a seat, even with an infinite node universe. -/
theorem fgHonestSeats_nonempty_of_quorum (Ef : Electorate (Fin n))
    (hq : 0 < Ef.q) (hH : Ef.IsQuorum (FGHonestSeats S rho)) :
    (FGHonestSeats S rho).Nonempty := by
  classical
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  change Ef.q ≤ Ef.weightOf (FGHonestSeats S rho) at hH
  rw [he, Electorate.weightOf, Finset.sum_empty] at hH
  omega

/-- Unit-seat fault counts give the weighted fault premise without counting nonholders. -/
theorem fg_fault_weight_of_count (Ef : Electorate (Fin n)) (unit : FGSafetyUnitLaws Ef)
    (hf : (historyFaulty S rho).card ≤ (n - 1) / 3) :
    Ef.weightOf (historyFaulty S rho) < Ef.q := by
  rw [unit.weight, unit.quorum, Gen.Pure.qF_def]
  have := unit.n_pos
  omega

/-- Honest FG seats form a unit quorum under the seat fault bound. -/
theorem high_target_honest_quorum_holder (Ef : Electorate (Fin n))
    (unit : FGSafetyUnitLaws Ef) (hf : (historyFaulty S rho).card ≤ (n - 1) / 3) :
    Ef.IsQuorum (FGHonestSeats S rho) := by
  classical
  have hsum : (FGHonestSeats S rho).card + (historyFaulty S rho).card = n := by
    rw [fgHonestSeats_eq_compl, Finset.card_compl_add_card, Fintype.card_fin]
  change Ef.q ≤ Ef.weightOf (FGHonestSeats S rho)
  rw [unit.quorum, unit.weight, Gen.Pure.qF_def]
  have := unit.n_pos
  omega

end AvailableChain.FGCompose
end
