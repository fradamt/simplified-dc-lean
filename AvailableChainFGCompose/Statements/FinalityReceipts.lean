module
public import AvailableChainFGCompose.Statements.Service
public import AvailableChainGeneric.Statements.V2.Duty.Receipt
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface P)
variable (entry : Wire → Option (Height × BlockId))
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → (FGBlock (Fin n)) → Wire → Bool)

structure ReceiverService (family : P.Object → Prop)
    (timely : P.State → P.Object → Prop)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (o : P.Object) (send freeze : Time) (x : V) where
  dl : Time → Time
  cut : Time
  anchor : Time
  within : Gen.V2.Duty.DeliveryWithinOn E rho family dl cut
  ready : Gen.V2.Duty.ReadyTrigger E rho o send x anchor (dl anchor)
  send_le : send ≤ anchor
  nonneg : 0 ≤ anchor
  later : anchor < dl anchor
  cut_le : dl anchor ≤ cut
  horizon : dl anchor ≤ rho.horizon
  freeze_le : dl anchor ≤ freeze
  history : Gen.V2.Duty.HistorySafeAt E rho x o anchor
  epoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho anchor)
    (V2.D.Run.idxBefore rho freeze)
  handlers : ∀ j t, anchor ≤ t → t < dl anchor →
    V2.D.Run.handlesAt E rho j x o t → P.wellFormed o = true ∧
      P.depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      timely (V2.D.Run.stateBefore E rho j x) o
  not_excluded : P.excludes (V2.D.Run.stateBeforeTime E rho (dl anchor) x) o = false

structure FreshHeadService (family : P.Object → Prop)
    (timely : P.State → P.Object → Prop) (T : FGTiming)
    (headObject : Slot → Fin n → BlockId → P.Object)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (s : Slot) (q : Fin n) (b : BlockId) (freeze : Time) (x : V) where
  dl : Time → Time
  cut : Time
  within : Gen.V2.Duty.DeliveryWithinOn E rho family dl cut
  ready : Gen.V2.Duty.ReadyTrigger E rho (headObject s q b)
    (T.vote s) x (T.vote s) (dl (T.vote s))
  later : T.vote s < dl (T.vote s)
  cut_le : dl (T.vote s) ≤ cut
  horizon : dl (T.vote s) ≤ rho.horizon
  freeze_le : dl (T.vote s) ≤ freeze
  epoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho (T.vote s))
    (V2.D.Run.idxBefore rho freeze)
  handlers : ∀ j t, T.vote s ≤ t → t < dl (T.vote s) →
    V2.D.Run.handlesAt E rho j x (headObject s q b) t →
    P.wellFormed (headObject s q b) = true ∧
      P.depsPresent (V2.D.Run.stateBefore E rho j x) (headObject s q b) = true ∧
      timely (V2.D.Run.stateBefore E rho j x) (headObject s q b)
  not_excluded : P.excludes (V2.D.Run.stateBeforeTime E rho (dl (T.vote s)) x)
    (headObject s q b) = false

def TargetReceiptService {Body : Type} (bodyObject : Slot → Body → P.Object)
    (bodyErase : Body → Block) (family : P.Object → Prop)
    (timely : P.State → P.Object → Prop) (E : Generic.Env V)
    (rho : V2.D.Run V P) (K : Block) (freeze : Time) (x : V) : Prop :=
  K = .genesis ∨ ∃ s N send, bodyErase N = K ∧
    Nonempty (ReceiverService family timely E rho (bodyObject s N) send freeze x)

structure FinalityActionReceipts {Body : Type} (T : FGTiming)
    (R : FGCoreReads P n Base Proposal Wire) (A : FGACServiceReads V)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (headHolder : Slot → Fin n → V)
    (family : P.Object → Prop) (timely : P.State → P.Object → Prop)
    (headObject : Slot → Fin n → BlockId → P.Object)
    (bodyObject : Slot → Body → P.Object) (bodyErase : Body → Block) : Prop where
  service : ∀ q x, x ∈ rho.honest → E.t_GST < T.action q →
    E.t_GST ≤ slotStartZ T (((q * T.roundSlots + 1 : Nat) : Int) - 1) →
    T.action q ≤ rho.horizon → ∀ nd,
    postClock E rho x (T.action q) = some nd → ∀ a K,
    headHolder (q * T.roundSlots + 1) a ∈ rho.honest →
    A.headAtLabel (headHolder (q * T.roundSlots + 1) a)
      (q * T.roundSlots + 1) = some K →
    Block.Preceq (R.erase (R.core nd).fg.F) K →
    Nonempty (FreshHeadService family timely T headObject E rho
      (q * T.roundSlots + 1) a K.root (T.action q) x) ∧
      TargetReceiptService bodyObject bodyErase family timely E rho K (T.action q) x

end AvailableChain.FGCompose
end
