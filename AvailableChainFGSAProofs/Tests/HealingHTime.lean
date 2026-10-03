module
public import AvailableChainFGSAProofs.Proofs.Assembly.HTime -- shake: keep (W3 claim adapter tests)

public section

/-! Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME HTimeClaim and its original run package. -/

namespace AvailableChain.FGSA.Run.Tests.HealingHTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME claim type with only the statement producer as a hypothetical input. -/
example (p : Params) (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p :=
  healing_hTimeClaim_of_statement p hTime

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE T/W3.
DC: SAME witness and chained bound after the package is applied to a run. -/
example (p : Params) (hTime : ∀ G ΔF, HTimeStatement p G ΔF)
    (G ΔF : Time) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : HealingTimePrem p c G ΔF E rho ()) : HTimeConcl p c E rho G ΔF :=
  healing_hTimeClaim_of_statement p hTime G ΔF hClock c E rho () h

#check healing_hTimeClaim_of_statement
#print axioms healing_hTimeClaim_of_statement

end AvailableChain.FGSA.Run.Tests.HealingHTime
end
