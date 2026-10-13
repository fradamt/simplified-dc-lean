module
public import AvailableChainFGCompose.Proofs.OrdinaryHolderClient
public import AvailableChainFGCompose.Statements.Selection
public import AvailableChainFGCompose.Statements.SafetyClaims

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire : Type}
variable (S : FGSafetyReads P n Wire) (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Paired selection inputs at an actual holder tick, with its actual duty record.
The global bijective client law supplies this run-local law through X1c. -/
theorem selection_tick_rows_holder (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (Q : FGSelectionReads P n) (client : FGSelectionClientLaws Q S)
    (rows : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho)) (i : Fin n) (j : Nat) (t : Time)
    (ht : rho.events[j]? = some (.tick (safetyHolder S rho i) t)) :
    ((V2.D.Run.emitsAt E rho j).filter P.objSelfVisible).filterMap S.decodeObject =
      if E.awake (safetyHolder S rho i) t = true ∧ S.enabled t = true then
        (createRowOnce Ef cfg
          (S.record (P.clock (V2.D.Run.stateBefore E rho j (safetyHolder S rho i)) t)) i
          (Q.clientInputs
            (P.clock (V2.D.Run.stateBefore E rho j (safetyHolder S rho i)) t)).1
          (Q.clientInputs
            (P.clock (V2.D.Run.stateBefore E rho j (safetyHolder S rho i)) t)).2).1.toList
      else [] := by
  have h := rows.holder_rows j _ t i ht rfl
  rw [ordinary_obsOwnReleased, V2.D.Engine.ownReleasedAt_def, ht] at h
  rw [ite_eq_left (show Option.map V2.Event.node
    (some (.tick (safetyHolder S rho i) t : V2.Event V P.Object)) =
      some (safetyHolder S rho i) from rfl)] at h
  have hd := ordinary_obsDutyState_tick E rho ht
  dsimp only [obsDutyState] at hd
  rw [hd, ← client.inputs_eq] at h
  exact h

end AvailableChain.FGCompose
end
