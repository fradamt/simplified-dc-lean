module
public import AvailableChainFGCompose.Statements.FinalityRecords
public import AvailableChainFGCompose.Statements.Population.Seats
public import AvailableChainFGCompose.Proofs.HolderClient
public import AvailableChainFGCompose.Proofs.OrdinaryHolderClient
public import AvailableChainFGCompose.Proofs.Finality.RecordInv

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)} {cfg : FGConfig}
variable {pt : FGServicePoint}

/-- The actual holder trace supplies durable row history without enumerating the nodes. -/
private theorem d7r_history_holder
    (trace : FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho)
      (safetyHolder S rho)) (seat : Fin n) (hx : safetyHolder S rho seat ∈ rho.honest)
    (i : Nat) :
    FGRowRecordHistory (S.record (V2.D.Run.stateBefore E rho i (safetyHolder S rho seat))) := by
  rw [((ordinary_FGHolderClientTrace_iff S Ef cfg E rho _).mp trace seat hx i).1]
  let inputs := (List.range i).filterMap (safetyInputAt S E rho (safetyHolder S rho seat))
  have hc := clientRunOnce_covers Ef cfg seat inputs RecordOnce.initial recordInv_initial
  refine ⟨hc.1, ?_⟩
  intro h U timeout fp hm
  rw [clientRecordOnce_sent] at hm
  change (.vote h U timeout, fp) ∈
    ((clientRunOnce Ef cfg seat RecordOnce.initial inputs).map Row.onceKey).reverse ++ [] at hm
  simp only [List.append_nil, List.mem_reverse, List.mem_map] at hm
  obtain ⟨a, ha, hk⟩ := hm
  have hh := congrArg Prod.fst hk
  change a.height_pair = .vote h U timeout at hh
  exact ⟨fun ht => (hc.2.2 a ha).1 h U (ht ▸ hh),
    fun ht => (hc.2.2 a ha).2.1 h U (ht ▸ hh)⟩

end AvailableChain.FGCompose
end
