module
public import AvailableChainFGSAClaims.Statements.Packages.Safety

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- bp.cleanInclusion.v1; 03 §5; P3:3238–3250; S3a FS9:2037–2043.
DC Generic/Regimes:92 SleepyRegime: INTENTIONAL: CleanSet supplies the FG-SA
healthy prefix; the gate must lie in the finite run (S3a Q12). -/
structure CleanInclusionPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSP) (ΔF : Time := E.Δ) : Prop where
  set : CleanSet p c E rho ΔF
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P
  hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon

/-- bp.exactProposal.v1; 00:826–838; S3a FS9:2037–2041.
DC Generic/Claims:28–33 AvailableAt: INTENTIONAL: the FG-SA local adoption
statement uses CleanSet and a supplied honest proposal (03 §4). -/
structure ExactProposalPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSP) (ΔF : Time := E.Δ) : Prop where
  set : CleanSet p c E rho ΔF
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P
  hhor : SA.voteTime p.toParams pt.s ≤ rho.horizon

end AvailableChain.FGSA.Run
end
