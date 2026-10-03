module
public import AvailableChainFGSAProofs.Proofs.Healing.Export -- shake: keep (lane boundary)

public section

/-! Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W3.
DC: SAME healing premises, witness, and both time bounds. -/

namespace AvailableChain.FGSA.Run

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W3.
DC: SAME statement under HealingTimePrem. The package supplies HealingSet,
LivenessBoundW, and the healing horizon at the original G and ΔF. -/
theorem healing_hTimeClaim_of_statement (p : Params)
    (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact hTime G ΔF hClock c E rho h.set h.bound h.hhor

end AvailableChain.FGSA.Run
end
