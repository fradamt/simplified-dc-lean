module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSARun.Statements.Client

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

end AvailableChain.FGSA.Run
end
