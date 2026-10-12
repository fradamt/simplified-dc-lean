module
public import AvailableChainFGCompose.Statements.ExecutionObs
public import AvailableChainFGCompose.Statements.SafetyReads

@[expose] public section

/-! Route-C bridge statements over the shared execution observation: accepted-body
origin, the holder-aware FG client, selected microstep acceptance and the strict-cut
HEAD history. Definitions and records only. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body Row : Type}

/-- Each body that a microstep adds to accepted storage has a delivered origin (the
accepting step and its original receipt token) or a local own-release origin at a tick of
the same receiver. The original token keeps receiver, index, wire, time and epoch. -/
structure FGAcceptedBodyOrigin (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (O : FGExecutionObs V P) (x : V) : Prop where
  origin : ∀ k b, k < O.cutLength x →
    b ∈ H.acceptedBodies (O.cutState x (k + 1)) → b ∉ H.acceptedBodies (O.cutState x k) →
    (∃ o, O.accepts x k o ∧ FGReceiptOrigin E rho H W x b o) ∨
    (∃ j t wire, rho.events[j]? = some (.tick x t) ∧ wire ∈ obsOwnReleased O x j ∧
      O.duty x j ≤ k ∧ k < O.done x j ∧ W.decodeBody wire = some b)

/-- E1F obligation (PC line): accepted-body origin of the canonical driver observation,
from the trace laws and the identification of accepted storage with driver acceptance. -/
def AcceptedBodyOriginDriverStatement {LeafIn Latest : Type}
    {Leaf : V2.ProtocolSpecD LeafIn}
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop :=
  ∀ x, FGDependencyTraceLaws E rho x H W D L Step (T x) F (Op x) Arrival Notify
    leafState leafWire ActualRead →
  (∀ k b, k ≤ (T x).length →
    (b ∈ H.acceptedBodies ((T x).state k) ↔ D.accepted ((T x).state k) b)) →
  FGAcceptedBodyOrigin E rho H W (driverFGExecutionObs E rho F T Op) x

theorem AcceptedBodyOriginDriverStatement_def {LeafIn Latest : Type}
    {Leaf : V2.ProtocolSpecD LeafIn}
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    AcceptedBodyOriginDriverStatement (Leaf := Leaf) E rho H W D L Step F T Op Arrival Notify
        leafState leafWire ActualRead =
      (∀ x, FGDependencyTraceLaws E rho x H W D L Step (T x) F (Op x) Arrival Notify
        leafState leafWire ActualRead →
      (∀ k b, k ≤ (T x).length →
        (b ∈ H.acceptedBodies ((T x).state k) ↔ D.accepted ((T x).state k) b)) →
      FGAcceptedBodyOrigin E rho H W (driverFGExecutionObs E rho F T Op) x) := rfl

/-- The actual holder-aware FG client (D1: no global `Fin n ≃ V`). `holder i` is the node
of FG seat `i`; it is injective, not surjective. The released FG row of a holder is
`createRowOnce` at the drained duty state with both inputs; a node with no FG seat
releases no FG row. The record changes only by the own writes of a tick. -/
structure FGHolderClientLaws (S : FGSafetyReads P n Wire) (Ef : Electorate (Fin n))
    (cfg : FGConfig) (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGExecutionObs V P)
    (holder : Fin n → V) : Prop where
  holder_eq : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = holder i
  holder_inj : Function.Injective holder
  initial_record : S.record P.init = RecordOnce.initial
  duty_record : ∀ j e x, rho.events[j]? = some e →
    S.record (O.cutState x (O.duty x j)) = S.record (O.cutState x (O.start x j))
  quiet_record : ∀ j e x, rho.events[j]? = some e → (∀ t, e ≠ .tick x t) →
    S.record (O.cutState x (O.done x j)) = S.record (O.cutState x (O.start x j))
  own_record : ∀ j x t, rho.events[j]? = some (.tick x t) →
    S.record (O.cutState x (O.done x j)) =
      (obsOwnReleased O x j).foldl (safetyRecordStep S) (S.record (O.cutState x (O.duty x j)))
  holder_rows : ∀ j x t i, rho.events[j]? = some (.tick x t) → holder i = x →
    (obsOwnReleased O x j).filterMap S.decodeObject =
      if E.awake x t = true ∧ S.enabled t = true then
        (createRowOnce Ef cfg (S.record (O.cutState x (O.duty x j))) i
          (S.inputs (O.cutState x (O.duty x j))).1
          (S.inputs (O.cutState x (O.duty x j))).2).1.toList
      else []
  nonholder_rows : ∀ j x t, rho.events[j]? = some (.tick x t) → (∀ i, holder i ≠ x) →
    (obsOwnReleased O x j).filterMap S.decodeObject = []

/-- Held witnesses of a block's causal history at actual local cuts: every ancestor with
rows is held by an honest receiver at a real cut whose event time is before `deadline`.
This is not an equality with `ChainRowsBefore`. -/
def FGChainRowsAtCut (R : FGCoreReads P n Base Proposal Wire) (rho : V2.D.Run V P)
    (O : FGExecutionObs V P) (X : FGBlock (Fin n)) (deadline : Time) : Prop :=
  ∀ W, FGBlock.Preceq W X → ∀ row ∈ W.rows, ∃ x k, x ∈ rho.honest ∧
    k ≤ O.cutLength x ∧ W ∈ (R.core (O.cutState x k)).fg.TF ∧ O.cutTime x k < deadline

omit [DecidableEq V] in
theorem FGChainRowsAtCut_def (R : FGCoreReads P n Base Proposal Wire) (rho : V2.D.Run V P)
    (O : FGExecutionObs V P) (X : FGBlock (Fin n)) (deadline : Time) :
    FGChainRowsAtCut R rho O X deadline =
      (∀ W, FGBlock.Preceq W X → ∀ row ∈ W.rows, ∃ x k, x ∈ rho.honest ∧
        k ≤ O.cutLength x ∧ W ∈ (R.core (O.cutState x k)).fg.TF ∧
        O.cutTime x k < deadline) := rfl

/-- The strict-cut HEAD history bridge: a HEAD read at an honest duty cut before the
deadline gives held causal history at real cuts. X1b proves it. -/
def ChainRowsOfHeadObsStatement (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGExecutionObs V P) : Prop :=
  FGCoreLaws R → FGExecutionObsLaws E rho O → FGObservedCoreLaws R rho O →
  ∀ j x t s X deadline, x ∈ rho.honest → rho.events[j]? = some (.tick x t) →
    R.headVote (O.cutState x (O.duty x j)) s = R.erase X → t < deadline →
    FGChainRowsAtCut R rho O X deadline

theorem ChainRowsOfHeadObsStatement_def (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGExecutionObs V P) :
    ChainRowsOfHeadObsStatement R E rho O =
      (FGCoreLaws R → FGExecutionObsLaws E rho O → FGObservedCoreLaws R rho O →
      ∀ j x t s X deadline, x ∈ rho.honest → rho.events[j]? = some (.tick x t) →
        R.headVote (O.cutState x (O.duty x j)) s = R.erase X → t < deadline →
        FGChainRowsAtCut R rho O X deadline) := rfl

/-- One selected acceptance at an actual microstep of an honest receiver: the original
token, the event segment, the strict deadline and the exact local window effect `update`
after insertion of `W`. The guards are evaluated at `O.cutState x step` (X1e). -/
structure FGSelectedAcceptance (R : FGCoreReads P n Base Proposal Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P)
    (update : Store (Fin n) → FGBlock (Fin n) → Store (Fin n))
    (x : V) (W : FGBlock (Fin n)) (d : Time) where
  step : Nat
  eventIndex : Nat
  token : FGReceiptToken V P.Object
  honest : x ∈ rho.honest
  accepts : O.accepts x step token
  segment : O.start x eventIndex ≤ step ∧ step < O.done x eventIndex
  event_some : ∃ e, rho.events[eventIndex]? = some e
  before_deadline : O.cutTime x step < d
  effect : (R.core (O.cutState x (step + 1))).fg =
    update { (R.core (O.cutState x step)).fg with
      TF := insert W (R.core (O.cutState x step)).fg.TF } W

/-- Retention of an accepted finality `U` after the selected step, to every later local
cut of the same receiver. X1e proves it from the observed finality laws. -/
def SelectedAcceptanceKeepStatement (R : FGCoreReads P n Base Proposal Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P)
    (update : Store (Fin n) → FGBlock (Fin n) → Store (Fin n)) : Prop :=
  FGObservedFinalityLaws R rho O →
  ∀ x W U d (A : FGSelectedAcceptance R rho O update x W d),
    FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F →
    ∀ k, A.step < k → k ≤ O.cutLength x → FGBlock.Preceq U (R.core (O.cutState x k)).fg.F

omit [DecidableEq V] in
theorem SelectedAcceptanceKeepStatement_def (R : FGCoreReads P n Base Proposal Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P)
    (update : Store (Fin n) → FGBlock (Fin n) → Store (Fin n)) :
    SelectedAcceptanceKeepStatement R rho O update =
      (FGObservedFinalityLaws R rho O →
      ∀ x W U d (A : FGSelectedAcceptance R rho O update x W d),
        FGBlock.Preceq U (R.core (O.cutState x (A.step + 1))).fg.F →
        ∀ k, A.step < k → k ≤ O.cutLength x →
          FGBlock.Preceq U (R.core (O.cutState x k)).fg.F) := rfl

end AvailableChain.FGCompose
end
