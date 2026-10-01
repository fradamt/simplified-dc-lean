module
public import AvailableChainFGSAClaims.Statements.ComposeStmt

@[expose] public section

namespace AvailableChain.FGSA.Run
open Gen.Pure

/-- Healing time point (21 H.3–H.10), P3 §4.4.2 D41. -/
structure PtU where
  u : Time
/-- Full reset witness point (21 H.22:3044–3055), P3 §4.4.2 D41. -/
structure PtW where
  w : HealingWitness
/-- Frontier point (21 HG.1:1333–1350), P3 §4.4.2 D41. -/
structure PtM where
  m : Nat
/-- Round point (22 §1), P3 §4.4.2 D41. -/
structure PtR where
  r : Nat
/-- Attempt point (21 H.10:1263–1279), P3 §4.4.2 D41. -/
structure PtK where
  k : AttemptKey

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- Family (2) without a reset witness (21 §2), P3 §4.4.2.
Consumers: pre-reset channels. -/
structure HealingPrem {Pt : Type} (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Pt) : Prop where
  set : HealingSet p c E rho G
/-- Family (2), full H0 point (21:3044–3055), P3 §4.4.2.
Consumers: post-reset channels. Full H0 uses ResetArrivalFullStatement. -/
structure HealingWitnessPrem (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtW) : Prop
    extends HealingPrem p c G E rho pt where
  h0 : H0 p c E rho pt.w
/-- H-time horizon (21:3152–3170), P3 §4.4.2. Consumer: HTimeStatement. -/
structure HealingTimePrem (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit) : Prop
    extends HealingPrem p c G E rho pt where
  hhor : E.t_GST + B_H p G ≤ rho.horizon
/-- Reset-only horizon (21 H.11:1572–1595), P3 A.10 with lead ruling.
Consumer: ResetArrivalStatement. Does not promise Q*. -/
structure ResetArrivalPrem (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit) : Prop
    extends HealingPrem p c G E rho pt where
  hhor : E.t_GST + B'_reset p G ≤ rho.horizon
/-- Full-H0 horizon (21 H.18:2868–2876), lead ruling 2026-09-30.
Consumer: ResetArrivalFullStatement. -/
structure ResetArrivalFullPrem (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit) : Prop
    extends HealingPrem p c G E rho pt where
  hhor : E.t_GST + B'_reset p G + Γ p G + 4 * p.Δ ≤ rho.horizon
/-- Joined kernel (00:1119–1134), P3 A.10 D44.
Consumer: F0.6b kernel claim. Located after PtR to preserve module order.
Full H0 time is read through kernelStart; no existential witness is a field. -/
structure KernelJoinedPrem (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtR) : Prop where
  set : Recovery₂ p c E rho G
  window : (FGood (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) p.R pt.r ∧ G ≤ P p) ∨
    FGood4 (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) p.R pt.r
  start : kernelStart p c E rho pt.r
  hhor : ↑(pt.r + 2) * P p + 9 * p.Δ ≤ rho.horizon


/-- Attempt point premises (21 H.10:1263–1279), P3 §4.4.2/A.10.
Consumer: progress-attempt claim. The missing budget-horizon clause in P3's
ProgressAttemptStatement is a reported STOP; it is not hidden in validity. -/
structure HealingAttemptPrem (G : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtK) : Prop
    extends HealingPrem p c G E rho pt where
  valid : AttemptValid p c E rho pt.k

end AvailableChain.FGSA.Run
end
