module
public import AvailableChainFGCompose.Statements.Population.Seats

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

end AvailableChain.FGCompose
end
