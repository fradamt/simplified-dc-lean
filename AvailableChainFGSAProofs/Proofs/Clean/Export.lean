module
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Clean.Zero
public import AvailableChainFGSAProofs.Proofs.Clean.Safety

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.Run V (fgsa p c)}

/-- P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 and Generic/Conditions:134:
INTENTIONAL divergence. Strict-before-cut participation can be empty.
Admission needs 4Δ and gates need 6Δ, so time-zero origins stay initial.
NoRestart comes from h. No F1 channel or extra honesty premise is used.
This Export restores the frozen history Prop by definitional matching. -/
theorem cleanHistoryAt_zero (h : HealthyPrefix₂ p c E rho 0) :
    CleanHistoryAt p c E rho 0 := by
  exact (cleanCut_zero_body h).1

/-- P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 and Generic/Conditions:134:
INTENTIONAL divergence. The inclusive zero cut can have events, but
admission needs 4Δ and gates need 6Δ. The Clean fields stay initial.
NoRestart comes from h. No F1 channel or extra honesty premise is used.
This Export restores the frozen truncation Prop by definitional matching. -/
theorem cleanTruncAt_zero (h : HealthyPrefix₂ p c E rho 0) :
    CleanTruncAt p c E rho 0 := by
  exact (cleanCut_zero_body h).2

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27,41,48 and Generic/Interface:64.
Compatibility and monotonicity have the same meaning. INTENTIONAL
representation and domain divergence: both getters read S, and each
finite read index is at most the event count at all integer times
(S3 D43/D61). No restart, quorum, channel, or extra honesty premise is used.
This Export restores the frozen safety Prop by definitional matching. -/
theorem cleanSafetyAt_of_trunc (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hs : V2.ScheduleWellFormed E rho)
    (ht : CleanTruncAt p c E rho rho.horizon) : CleanSafetyAt p c E rho := by
  exact cleanSafety_of_trunc_body p c E rho hs ht

/-- P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 and Generic/Conditions:134:
INTENTIONAL divergence. The zero lane uses strict-before-cut participation;
its inclusive event prefix stays initial because admission needs 4Δ and
gates need 6Δ. The frozen cut premise supplies HealthyPrefix₂, including
NoRestart. No F1 channel or quorum premise is added. -/
theorem cleanCutZero_export (p : Params) : CleanCutZeroClaim p := by
  intro V _ _ In c E rho h
  exact ⟨cleanHistoryAt_zero h.set, cleanTruncAt_zero h.set⟩

end AvailableChain.FGSA.Run
end
