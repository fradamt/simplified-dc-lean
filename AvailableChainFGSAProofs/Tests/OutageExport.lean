module
public import AvailableChainFGSAProofs.Proofs.Assembly.Outage -- shake: keep (body-to-claim checks)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.OutageExport

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {pt : PtOut} {ΔF : Time}
variable (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))


include hstore hframe hsrc htsrc hnamed

/-- The cut input keeps enabled gates, confirmed readers, and receiver epochs.
Clean supplies it from the outage's sleep prefix; it is true under that regime. -/
theorem compat_of_sleep_cut
    (hcut : CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀)
    (h : OutagePrem p c fast E rho pt ΔF) : OutageCompatAt p c E rho fast pt := by
  exact outage_compat_body_of_cut p hstore hframe hsrc htsrc hnamed hcut h
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨h.set.pre.base, h.set.faultQ⟩ hstore)

/-- The fast projection has exactly the public reader and duty scopes. -/
example (hcut : CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀)
    (h : OutagePrem p c true E rho pt ΔF) : P1Concl p c E rho true pt :=
  (compat_of_sleep_cut hstore hframe hsrc htsrc hnamed hcut h).1

/-- The slow projection keeps the same protected receiver scope. -/
example (hcut : CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀)
    (h : OutagePrem p c false E rho pt ΔF) : P1Concl p c E rho false pt :=
  (compat_of_sleep_cut hstore hframe hsrc htsrc hnamed hcut h).1

#print axioms compat_of_sleep_cut

end AvailableChain.FGSA.Run.Tests.OutageExport
