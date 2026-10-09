module
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAProofs.Proofs.Clean.Zero
public import AvailableChainFGSAProofs.Proofs.Clean.Safety
public import AvailableChainFGSAProofs.Proofs.Clean.Closure
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- P3 §§4.7, 8.5; bp02 §§5.4–6. Class B. DC counterparts:
Legacy/Definitions/SafetyRegimes:53–80 and Protocol/Grades/JointHistoryGapsIdx:26,141.
INTENTIONAL divergence: FG-SA uses raw SA results, exact lease/saved/fast-write
origins, and a finite inclusive event cut. This wrapper restores the frozen
Claims conclusion. NoRestart is inherited from CleanCut₂ through Base₂.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanHistoryAt (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {b₀ : Time} (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CleanHistoryAt p c E rho b₀ := by
  exact cleanHistoryAt_body p c E rho h hq hf hsrc

/-- P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 and Generic/Conditions:134:
INTENTIONAL divergence. Strict-before-cut participation can be empty.
Admission needs 4Δ and gates need 6Δ, so time-zero origins stay initial.
NoRestart comes from h. No F1 channel or extra honesty premise is used.
This Export restores the frozen history Prop by definitional matching.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanHistoryAt_zero (h : HealthyPrefix₂ p c E rho 0 ΔF) :
    CleanHistoryAt p c E rho 0 := by
  exact (cleanCut_zero_body h).1

/-- P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 and Generic/Conditions:134:
INTENTIONAL divergence. The inclusive zero cut can have events, but
admission needs 4Δ and gates need 6Δ. The Clean fields stay initial.
NoRestart comes from h. No F1 channel or extra honesty premise is used.
This Export restores the frozen truncation Prop by definitional matching.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanTruncAt_zero (h : HealthyPrefix₂ p c E rho 0 ΔF) :
    CleanTruncAt p c E rho 0 := by
  exact (cleanCut_zero_body h).2

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27,41,48 and Generic/Interface:64.
Compatibility and monotonicity have the same meaning. INTENTIONAL
representation and domain divergence: both getters read S, and each
finite read index is at most the event count at all integer times
(S3 D43/D61). No restart, quorum, channel, or extra honesty premise is used.
This Export restores the frozen safety Prop by definitional matching. -/
theorem cleanSafetyAt_of_trunc (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (ht : CleanTruncAt p c E rho rho.horizon) : CleanSafetyAt p c E rho := by
  exact cleanSafety_of_trunc_body p c E rho hs ht

/-- P3 §8.5:5320–5346, bp02 initialization and §6, SYN L39.
DC Legacy/Definitions/SafetyRegimes:53–80 and Generic/Conditions:134:
INTENTIONAL divergence. The zero lane uses strict-before-cut participation;
its inclusive event prefix stays initial because admission needs 4Δ and
gates need 6Δ. The frozen cut premise supplies HealthyPrefix₂, including
NoRestart. No F1 channel or quorum premise is added.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanCutZero_export (p : Params) : CleanCutZeroClaim p := by
  intro V _ _ In c E rho ΔF h
  exact ⟨cleanHistoryAt_zero h.set, cleanTruncAt_zero h.set⟩

/-- P3:3331–3335, bp02 §5.5; DC Legacy/Definitions/SafetyRegimes:61–75.
INTENTIONAL difference: raw SA results, a whole-result guard, and the cut
before same-time deliveries. NoRestart is inherited through Base₂.
This wrapper restores the exact frozen Claims conclusion.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanGateAt (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {b₀ : Time} (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CleanGateAt p c E rho b₀ := by
  exact cleanGateAt_body p c E rho h hq hf hsrc

/-- P3 §8.5, bp02 §§5.4–6; DC Legacy/Definitions/SafetyRegimes:53–80.
INTENTIONAL difference: six finite-cut clauses use raw SA gates and exact
FG-SA state origins. NoRestart is inherited from CleanCut₂ through Base₂.
This wrapper restores the exact frozen Claims conclusion.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanTruncAt (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {b₀ : Time} (h : CleanCut₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    CleanTruncAt p c E rho b₀ := by
  exact cleanTruncAt_body p c E rho h hq hf hsrc

/-- P3:5296–5311, L39; DC Legacy/Definitions/SafetyRegimes:53–80 and
Generic/Conditions:134. INTENTIONAL difference: a positive finite cut
supplies quorum from strict-before-cut participation and takes both F1
channels. NoRestart is inherited from Base₂. Assembly owns the cut split.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanCutPos_export (p : Params) : CleanCutPosClaim p := by
  intro V _ _ In c E rho ΔF pt hc hb hf hsrc
  have hq := hc.set.faultQ_of_pos hb
  have hf' : FGFoundation p c E rho :=
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩
  exact ⟨cleanHistoryAt p c E rho hc.set hq hf' hsrc,
    cleanTruncAt p c E rho hc.set hq hf' hsrc⟩

/-- P3 §8.5, bp02 §6; DC Generic/Properties:27,41,48 and Interface:64.
INTENTIONAL difference: a cut claim gives safety at every integer read,
since each read index is at most the event count. This implication has no
F1 channel premise or cut split. Clean run results inherit NoRestart via Base₂.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem cleanSafety_of_cut (p : Params) (hcut : CleanCutClaim p) : CleanSafetyClaim p := by
  intro V _ _ In c E rho ΔF _ h
  exact cleanSafetyAt_of_trunc p c E rho h.set.pre.base.valid.toScheduleWellFormed
    (hcut c E rho ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩).2

end AvailableChain.FGSA.Run
end
