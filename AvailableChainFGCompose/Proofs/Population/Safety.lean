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

/-- A nonholder may release raw objects, but none can witness a decoded slashable row. -/
theorem safety_nonholder_noSlash (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (rows : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho)) (W : FGSafetyWireLaws S) (x : V)
    (hn : ∀ i, safetyHolder S rho i ≠ x) : safetyNoSlash S E rho x := by
  intro a _ ha _ u _ hu _
  obtain ⟨j, t, ht, hem⟩ := ha
  have hd := (W.decode_encode a).trans hu
  have hm : u ∈ (V2.D.Engine.ownReleasedAt E rho x j).filterMap S.decodeObject := by
    apply List.mem_filterMap.mpr
    refine ⟨S.encode a, ?_, hd⟩
    rw [V2.D.Engine.ownReleasedAt_def, ht]
    rw [ite_eq_left (show Option.map V2.Event.node
      (some (.tick x t : V2.Event V P.Object)) = some x from rfl)]
    exact List.mem_filter.mpr ⟨hem, W.decoded_visible _ _ hd⟩
  have hs := rows.nonholder_rows j x t ht hn
  rw [ordinary_obsOwnReleased] at hs
  rw [hs] at hm
  exact (List.not_mem_nil hm).elim

/-- Supply the existing all-honest count API by splitting holders from nonholders. -/
theorem safety_noSlash_all_of_holder (Ef : Electorate (Fin n)) (cfg : FGConfig)
    (rows : FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho)) (W : FGSafetyWireLaws S)
    (he : ∀ i, safetyHolder S rho i ∈ rho.honest →
      safetyNoSlash S E rho (safetyHolder S rho i)) :
    ∀ x ∈ rho.honest, safetyNoSlash S E rho x := by
  classical
  intro x hx
  by_cases hh : ∃ i, safetyHolder S rho i = x
  · obtain ⟨i, rfl⟩ := hh
    exact he i hx
  · exact safety_nonholder_noSlash S E rho Ef cfg rows W x (by simpa using hh)

end AvailableChain.FGCompose
end
