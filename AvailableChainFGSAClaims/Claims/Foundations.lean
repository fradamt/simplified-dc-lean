module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainGeneric.Statements.AC.Lease

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- FS20 conclusion of bp.clientSafety.v1. T7.9 A is pairwise and order-free. -/
def ClientSafeAll (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) : Prop :=
  ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x

/-- A8: Linked is the only premise. Restarts are permitted (T7.9 A, route R1). -/
def ClientSafetyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    V2.Linked (fgsaFamilies p c).linked rho → ClientSafeAll p c E rho

/-- S3 X5: the family-(0) package form of client safety. -/
def ClientSafetyBaseClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → ClientSafeAll p c E rho

/- bp.receiptCoverage.v1 cites AvailableChain.FGSA.Run.ReceiptCoverageStatement
in AvailableChainFGSARun/Statements/ReceiptCoverage.lean (FROZEN 364d837e),
proved by fgsa_receiptCoverage. Its within, slotWindow, compat and deadline
premises remain unchanged. There is no second K8 statement here. -/

/-- P3 App. A.10: all seven F1 foundation channels. BaseSet and FaultQ are in the package. -/
def FGFoundationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → FGFoundation p c E rho

/-- P3 App. A.10, G30: the source frame at every threshold.
BaseSet and FaultQ are in the package. -/
def SrcFrameAboveClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho


open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- The FG carrier of emitted or delivered proposals, including ancestors. -/
def RunFGBlock (X : FGBlock (Fin p.n)) : Prop :=
  ∃ o b raw sup rows,
    o.payload = Msg.proposal b raw sup rows ∧
    ((∃ x t, V2.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) b

/-- bp.carrier.v1: erasure on the run carrier keeps identity and geometry. -/
def CarrierAt : Prop :=
  (∀ X Y, RunFGBlock p c E rho X → RunFGBlock p c E rho Y →
    (eraseFG X = eraseFG Y → X = Y) ∧
    (FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y))) ∧
  (∀ X, RunFGBlock p c E rho X →
    eraseFG X.parent = (eraseFG X).parent ∧
    (eraseFG X).slot = X.slot ∧ (eraseFG X).root = X.root)

/-- bp.store.v1: snapshot invariants and the two temporal channels.
Each temporal channel retains its NoRestart premise. -/
def StoreAt : Prop :=
  (∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
    CStoreInv p (storeAt p c E rho i x)) ∧
  (V2.ScheduleWellFormed E rho → RStoreCumul p c E rho ∧ RMono p c E rho)

/-- bp.activeView.v1: the active tree and its unchanged vote/stamp data. -/
def ActiveViewAt : Prop := RStore p c E rho

/-- bp.leaseOrigins.v1: all obligation rows have a passed gate origin.
The statement includes due rows, target order, ancestor deadlines and fast writes. -/
def LeaseOriginsAt : Prop := ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ row ∈ st.base.obligations, ∃ j < i, ∃ s B,
    IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
    gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
  Gen.AC.LeaseMapChain st.base ∧
  (∀ K g deadline, (K, g, deadline) ∈ st.base.obligations →
    ∀ B, B ≠ .genesis → Block.Preceq B K →
      Gen.AC.ProtectsUntil st.base B g deadline) ∧
  (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] →
    ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        Block.Preceq X B ∧ fastAt p c E rho x s X)

/-- bp.sourceDiscipline.v1(a,d): actual sources, emitted names and label bounds. -/
def SourceDisciplineBaseAt : Prop :=
  TSrc p c E rho ∧ LabelBound p c E rho ∧
  (∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

/-- bp.sourceDiscipline.v1(a–d), including target/progress and finality origins. -/
def SourceDisciplineAt : Prop :=
  SourceDisciplineBaseAt p c E rho ∧ RStrat p c E rho

/-- bp.carrier.v1; all runs. -/
def CarrierClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    CarrierAt p c E rho

/-- bp.chainCertificates.v1; all runs. -/
def ChainCertificatesClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    RGeo p c E rho

/-- bp.store.v1; all runs, with local temporal premises. -/
def StoreClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    StoreAt p c E rho

/-- bp.activeView.v1; all runs. -/
def ActiveViewClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    ActiveViewAt p c E rho

/-- bp.leaseOrigins.v1; scheduled runs. -/
def LeaseOriginsClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    V2.ScheduleWellFormed E rho → LeaseOriginsAt p c E rho

/-- bp.reconcile.v1: exact edits, fixed-F idempotence and K1.
The K1 lease premise includes due rows and has no fastWrite premise. -/
def ReconcileAt (st : State p.n) : Prop :=
  FGSA.reconcile st = { st with
    base := { st.base with
      obligations := st.base.obligations.filter (fun row => FGSA.activeCompatible st row.1)
      genuine := st.base.genuine.map
        (fun row => (row.1, row.2.filter (FGSA.activeCompatible st)))
      stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F }
    fastWrite := st.fastWrite.map
      (fun row => (row.1, row.2.filter (FGSA.activeCompatible st))) } ∧
  FGSA.reconcile (FGSA.reconcile st) = FGSA.reconcile st ∧
  (∀ F₀, FGSA.FastOrigin F₀ st → Block.Preceq F₀ (eraseFG st.fg.F) →
    (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) →
    (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) →
    Block.Compatible st.base.stableRecord (eraseFG st.fg.F) →
    FGSA.reconcile st = { st with base := { st.base with
      stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (FGSA.reconcile st).base.stableRecord)

/-- bp.reconcile.v1: the store claim at each reachable store. -/
def ReconcileClaim : Prop := ∀ st, Reachable p st → ReconcileAt p st

/-- comp.outputNesting.v2: the T7.5 NestOK conclusion at every run store. -/
def OutputNestingAt : Prop := ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
  FGSA.NestOK (storeAt p c E rho i x)

def OutputNestingClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    OutputNestingAt p c E rho

/-- bp.frame.v1; all runs. -/
def FrameClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    RFrameExact p c E rho

/-- bp.sourceDiscipline.v1(a,d); no FaultQ premise. -/
def SourceDisciplineBaseClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → SourceDisciplineBaseAt p c E rho

/-- bp.sourceDiscipline.v1(a–d); BaseSet and FaultQ. -/
def SourceDisciplineClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → SourceDisciplineAt p c E rho


end AvailableChain.FGSA.Run
end
