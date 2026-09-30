module
public import AvailableChainFGSAClaims.Statements.ChannelProps

@[expose] public section

/-! P3 App. A.1/A.10, F0.8a. The generic composition rules stay in Gen:
Gen.Pure.AGRule.holds, Gen.Pure.firstFailure_holds, Gen.Pure.WindowRule.holds
(Proofs/Pure/FirstBad). Gen.Pure.RetroAt and Gen.V2.Pending supply the
retrospective and deadline predicates. No F2 invariant enters this module. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) (rho : V2.Run V (fgsa p c))

/-- Study §5.4 (895–903): event indices between consecutive post-gate cuts.
Slot zero starts at index zero. Consumers: F5, H.14–H.17, with Gen.Pure.WindowRule. -/
def windowIdx (s : Slot) (i : Nat) : Prop :=
  (match s with
   | 0 => True
   | s' + 1 => afterTicksIdx rho (SA.gateTime p.toParams s') ≤ i) ∧
  i < afterTicksIdx rho (SA.gateTime p.toParams s)

variable {rho} [DecidableEq V] (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- P3 App. A.1: study §3.1 (229–260), 01 §8.4 (795–801).
Earlier rows and certificates, bounded labels, atomic reads, and fixed tick FG state. -/
structure TimingContract : Prop where
  rowLag : ∀ j k y r a x, HonestRowAt p c E rho j y r a →
    HandlesRowAt p c E rho k x a → j < k
  certLag : RStrat p c E rho
  label : LabelBound p c E rho
  atomic : ∀ i x, x ∈ rho.honest →
    FGSA.SACompat (storeAt p c E rho i x) ∧ FGSA.NestOK (storeAt p c E rho i x)
  tickFG : ∀ x t nd, preTick E rho x t = some nd →
    ∀ nd', postClock E rho x t = some nd' → nd'.st.fg = nd.st.fg

/-- P3 App. A.10, D09: unconditional FG channels of App. A.2.
Blueprint bp.store.v1, bp.frame.v1, bp.chainCertificates.v1,
bp.sourceDiscipline.v1, and bp.reconcile.v1. -/
structure FGFoundation : Prop where
  store : RStore p c E rho
  cumul : RStoreCumul p c E rho
  mono : RMono p c E rho
  frame : RFrameExact p c E rho
  geo : RGeo p c E rho
  strat : RStrat p c E rho
  reconcile : RRec p c E rho

end AvailableChain.FGSA.Run
end
