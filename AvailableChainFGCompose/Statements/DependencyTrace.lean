module
public import AvailableChainFGCompose.Statements.Dependency

@[expose] public section

namespace AvailableChain.FGCompose

variable {In V Body Row Latest : Type} [DecidableEq V]
variable {P : V2.ProtocolSpecD In}

/-- Epoch zero precedes any restart. A restart at index k starts epoch k+1. -/
def dependencyReceiverEpoch (rho : V2.D.Run V P) (x : V) (j : Nat) : Nat :=
  ((rho.events.take j).zipIdx).foldl (fun epoch pair =>
    match pair.1 with
    | .restart y _ => if y = x then pair.2 + 1 else epoch
    | _ => epoch) 0

/-- Immutable original receipt data. Retries keep this value in full. -/
structure FGReceiptToken (V Wire : Type) where
  receiver : V
  eventIndex : Nat
  wire : Wire
  receiptTime : Time
  receiptEpoch : Nat

/-- These observations are the driver's original wire validation and payload reads. -/
structure FGDependencyWireReads (P : V2.ProtocolSpecD In) (Body Row : Type) where
  decodeBody : P.Object → Option Body
  namedRoots : P.Object → Option (BlockId × BlockId)
  proposalErase : P.Object → Option Block
  decodedRows : P.Object → List Row
  bodyRows : Body → List Row

/-- Receipt evidence binds the receiver, exact full body, wire, time and restart epoch. -/
structure FGReceiptOrigin (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (x : V) (b : Body) (o : FGReceiptToken V P.Object) : Prop where
  receiver_eq : o.receiver = x
  delivered : rho.events[o.eventIndex]? = some (.deliver x o.wire o.receiptTime)
  decoded : W.decodeBody o.wire = some b
  authentic : P.wellFormed o.wire = true
  awake_receipt : E.awake x o.receiptTime = true
  named : W.namedRoots o.wire = some (H.root b, H.root (H.parent b))
  geometry : W.proposalErase o.wire = some (H.erase b)
  rows : W.decodedRows o.wire = W.bodyRows b
  epoch_eq : o.receiptEpoch = dependencyReceiverEpoch rho x o.eventIndex

/-- Finite refinement data. The driver protocol P and the one-body leaf are separate. -/
structure FGDependencyTrace (State : Type) where
  length : Nat
  state : Nat → State
  time : Nat → Time
  start : Nat → Nat
  done : Nat → Nat
  readCut : Nat → Nat

def dependencyStrictPrefix (rho : V2.D.Run V P) (T : FGDependencyTrace P.State)
    (deadline : Time) (k : Nat) : Prop :=
  k ≤ T.length ∧ T.time k < deadline ∧
    ∀ j e, rho.events[j]? = some e → T.start j ≤ k → e.time < deadline

variable {LeafIn : Type} {Leaf : V2.ProtocolSpecD LeafIn}

/-- Production requires a simulation of this actual driver run, not the ordinary leaf fold. -/
structure FGDependencyTraceLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (x : V) (H : FGHistoricalReads P.State Body)
    (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (T : FGDependencyTrace P.State)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop where
  initial : T.state 0 = P.init
  initial_accepted : ∀ b, D.accepted P.init b → b = L.genesis
  micro_step : ∀ k, k < T.length → ∃ kind, Step kind x (T.state k) (T.state (k + 1))
  external_step : ∀ j e, rho.events[j]? = some e →
    T.state (T.start j) = V2.D.Run.stateBefore E rho j x ∧
    T.state (T.done j) = V2.D.Run.stateBefore E rho (j + 1) x
  wire_validation : ∀ wire b, P.wellFormed wire = true →
    W.decodeBody wire = some b → D.validBody b
  origin_valid : ∀ k b o, k ≤ T.length → D.originAvailable (T.state k) b o →
    FGReceiptOrigin E rho H W x b o ∧ T.start o.eventIndex < k
  leaf_step : ∀ k b o st', k < T.length →
    L.step (T.state k) b o .accepted st' → st' = T.state (k + 1) →
    FGReceiptOrigin E rho H W x b o ∧ T.start o.eventIndex < k ∧
    leafState st' = Leaf.process (leafState (T.state k)) (leafWire o.wire)
  origin_attribution : ∀ k b, k < T.length →
    D.accepted (T.state (k + 1)) b → ¬ D.accepted (T.state k) b → ∃ o,
    L.step (T.state k) b o .accepted (T.state (k + 1)) ∧
    D.originAvailable (T.state (k + 1)) b o ∧
    W.proposalErase o.wire = some (H.erase b) ∧ W.decodedRows o.wire = W.bodyRows b
  read_correspondence : ∀ i st, ActualRead x i st →
    T.readCut i ≤ T.length ∧ T.state (T.readCut i) = st ∧ dependencyClosed H D st
  order_and_time : ∀ (i j : Nat) (ei ej : V2.Event V P.Object),
    rho.events[i]? = some ei → rho.events[j]? = some ej →
    i ≤ j → ei.time ≤ ej.time
  finite_segment : ∀ j e, rho.events[j]? = some e →
    T.start j ≤ T.done j ∧ T.done j ≤ T.length
  event_drain : ∀ j y wire t, rho.events[j]? = some (.deliver y wire t) →
    dependencyClosed H D (T.state (T.done j))
  entry_drain : ∀ j e, rho.events[j]? = some e →
    dependencyClosed H D (T.state (T.done j))
  segment_time : ∀ j e k, rho.events[j]? = some e →
    T.start j ≤ k → k ≤ T.done j → T.time k = e.time
  event_order : ∀ (i j : Nat) (ei ej : V2.Event V P.Object),
    rho.events[i]? = some ei → rho.events[j]? = some ej →
    i < j → T.done i < T.start j
  completion_cut : ∀ j e deadline, rho.events[j]? = some e → e.time < deadline →
    dependencyStrictPrefix rho T deadline (T.done j)
  atomic_tick : ∀ (j : Nat) (t : Time), rho.events[j]? = some (.tick x t) →
    T.readCut j ≤ T.length ∧
    T.state (T.readCut j) = P.clock (V2.D.Run.stateBefore E rho j x) t ∧
    dependencyClosed H D (T.state (T.readCut j))

/-- Network facts are consumed under the original awake, horizon and old-send guards. -/
structure FGDependencyDeliveryLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (x : V) (H : FGHistoricalReads P.State Body)
    (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (T : FGDependencyTrace P.State)
    (Outstanding : P.Object → Time → Time → Prop) : Prop where
  old_send : ∀ sender wire sent wake deadline b,
    sender ∈ rho.honest → V2.D.Run.emits E rho sender wire sent →
    W.decodeBody wire = some b → D.validBody b → Outstanding wire sent wake →
    sent < deadline → wake ≤ deadline →
    (∀ t, wake ≤ t → t ≤ deadline → E.awake x t = true) →
    (∀ (j : Nat) (t : Time), rho.events[j]? = some (.restart x t) → wake < t → deadline < t) →
    deadline ≤ rho.horizon →
    max (max sent E.t_GST) wake + E.Δ ≤ deadline →
    ∃ j o, FGReceiptOrigin E rho H W x b o ∧ o.eventIndex = j ∧
      o.receiptTime < max (max sent E.t_GST) wake + E.Δ ∧
      Effect H D (T.state (T.done j)) b o

end AvailableChain.FGCompose
end
