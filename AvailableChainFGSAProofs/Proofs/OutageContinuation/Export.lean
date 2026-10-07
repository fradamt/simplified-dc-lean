module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationJoint
public import AvailableChainFGSAProofs.Proofs.Shared.Claims

public section

namespace AvailableChain.FGSA.Run

/-- OUTPUT-DIRECT §10. DC: INTENTIONAL; the completed lane body proves
the companion from the existing supplier interfaces. Shared/Claims performs
the claim assembly. No continuation invariant is an input. -/
theorem outageContinuation_claim_of (p : Params)
    (hstore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), StoreAt p c E rho)
    (hactive : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), ActiveViewAt p c E rho)
    (hframe : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), FrameAt p c E rho)
    (hsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho)
    (hdisc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SourceDisciplineAt p c E rho)
    (hcut : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
        CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀) :
    OutageContinuationClaim p :=
  outageContinuation_of_body p (@outageV_body p) hstore hactive hframe hsrc hdisc hcut

end AvailableChain.FGSA.Run
end
