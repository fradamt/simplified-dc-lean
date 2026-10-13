module
public import AvailableChainFGCompose.Statements.SafetyOrigin
public import AvailableChainFGCompose.Proofs.SafetyAccountable
public import AvailableChainFGCompose.Proofs.SafetySlashing

public section

/-! The safety consumers under the origin laws. A delivery can admit the delivered body
and bodies that were pending. Each stored non-genesis block still has a delivery to the
same node with its erasure and rows, so the conclusions of the consumers do not change. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {Ef : Electorate (Fin n)} {H : FGHeightView (Fin n)} {f : FGFinalityView (Fin n)}
variable {cfg : FGConfig}
variable [DecidableEq V] {E : Generic.Env V} {rho : V2.D.Run V P}
variable {Good : P.State → Prop} {pending : P.State → P.Object → Prop} {Q : Block → Prop}

/-- The frozen record implies the origin record, with no pending object: the one new block
of a delivery has the delivered object as its origin. The converse does not hold. -/
theorem safetyStoreOriginLaws_of_storeLaws (L : FGSafetyStoreLaws R S H f Good) :
    FGSafetyStoreOriginLaws R S H f Good (fun _ _ => False) where
  initial_good := L.initial_good
  clock_good := L.clock_good
  process_good := L.process_good
  own_good := L.own_good
  restart_good := L.restart_good
  invariant := L.invariant
  initial_tf := L.initial_tf
  restart_tf := L.restart_tf
  process_origin := fun nd o B hg hB hold =>
    ⟨o, Or.inl rfl, L.process_new nd o B hg hB hold⟩
  pending_origin := ⟨fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h.elim,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

end AvailableChain.FGCompose
end
