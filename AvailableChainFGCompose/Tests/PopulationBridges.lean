module
public import AvailableChainFGCompose.Proofs.Population.Safety
public import AvailableChainFGCompose.Proofs.SafetySlashing

set_option linter.privateModule false

public section

/-! Conditional algebraic specializations, not client/store premise producers.
The separate Population controls provide nonvacuous emitting all-holder witnesses. -/
namespace AvailableChain.FGCompose.Tests.PopulationBridges
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (S : FGSafetyReads P n Wire) (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Old global client laws imply the new actual-tick equation, with exactly the old RHS. -/
private theorem legacy_tick_specialization (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (J : FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
    (he : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i)
    (Q : FGSelectionReads P n) (client : FGSelectionClientLaws Q S)
    (i : Fin n) (j : Nat) (t : Time) (ht : rho.events[j]? = some (.tick (e i) t)) :
    ((V2.D.Run.emitsAt E rho j).filter P.objSelfVisible).filterMap S.decodeObject =
      if E.awake (e i) t = true ∧ S.enabled t = true then
        (createRowOnce Ef cfg (S.record (V2.D.Run.stateBefore E rho j (e i))) (e.symm (e i))
          (Q.clientInputs (P.clock (V2.D.Run.stateBefore E rho j (e i)) t)).1
          (Q.clientInputs (P.clock (V2.D.Run.stateBefore E rho j (e i)) t)).2).1.toList
      else [] := by
  have hfun : (fun i => e i) = safetyHolder S rho := funext (fun i => (he i).symm)
  have rows := ordinary_FGHolderClientLaws S Ef cfg E rho J e he
  change FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho) (fun i => e i)
    at rows
  rw [hfun] at rows
  have hh : safetyHolder S rho i = e i := he i
  have h := selection_tick_rows_holder S E rho Ef cfg Q client rows i j t (hh.symm ▸ ht)
  simpa only [hh, J.clock_record, Equiv.symm_apply_apply] using h

end AvailableChain.FGCompose.Tests.PopulationBridges
end
