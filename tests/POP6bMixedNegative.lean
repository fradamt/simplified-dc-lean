module
import all AvailableChainFGCompose.Tests.P0d5db
import all tests.POP6bMixedFixture
import all tests.POP6bMixedFacts
import all tests.POP6bMixedControl

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bNegative
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db POP6bMixed

private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (hj : run.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    reads.encode a ∉ V2.D.Run.emitsAt env run j := by
  intro ha
  rw [emissions_premises_sat j 7 t hj] at ha
  unfold output at ha
  by_cases owner : (if protocol.signLabel t = 6 then 9 else 7) = 7
  · rw [ite_eq_left owner] at ha
    obtain ⟨p, _, he⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp ha)
    have hl := congrArg (fun o : protocol.Object => match o.auth with
      | .seat l _ => some l | .none => none) he
    change some (protocol.signLabel t) = some 6 at hl
    have eq := Option.some.inj hl
    rw [eq] at owner
    norm_num at owner
  · rw [ite_eq_right owner] at ha
    cases ha

#print axioms nonholder_no_encoded

end AvailableChain.FGCompose.Tests.POP6bNegative
end
