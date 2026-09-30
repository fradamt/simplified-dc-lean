module
public import AvailableChainFGSAClaims.Statements.Counts
public import AvailableChainFGSAClaims.Statements.Bounds
public import AvailableChainFGSARun.Statements.Interface

@[expose] public section

namespace AvailableChain.FGSA.Run

open Gen.Pure
variable (p : Params) {In : Type} (c : AppCodec In)

abbrev WinSpec (Pt : Type) := ∀ {V : Type} [DecidableEq V] [Fintype V],
  Generic.Env V → V2.Run V (fgsa p c) → Pt → Time → Prop

structure PtB₀ where
  b₀ : Time
structure PtT where
  t : Time
structure PtOut where
  T : Time
  b₀ : Time
  b₁ : Time

/-- Emission and strict acceptance precede the deadline; the gate is within the bound. -/
def cleanWinAt {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : V2.Run V (fgsa p c)) (s : Slot) (bound : Time) : Prop :=
  ∃ (B : Block) (o : (fgsa p c).Object),
    HonestProposal E rho (fgsaInterface p c) s B ∧
    V2.Run.emits E rho (V2.proposerOf rho (fgsaInterface p c) s) o
      (V2.proposalTime (fgsaInterface p c) s) ∧
    (fgsaInterface p c).block o.payload = some B ∧
    (∀ w ∈ rho.honest, ∃ i t', V2.proposalTime (fgsaInterface p c) s ≤ t' ∧
      t' < max (V2.proposalTime (fgsaInterface p c) s) E.t_GST + E.Δ ∧
      V2.Run.acceptsAt E rho i w o t') ∧
    SA.gateTime p.toParams s ≤ bound

def cleanWin : WinSpec p c Unit := fun E rho _ H =>
  ∃ s, H ≤ V2.proposalTime (fgsaInterface p c) s ∧ cleanWinAt p c E rho s rho.horizon

def cleanPrefixWin : WinSpec p c PtB₀ := fun E rho pt H =>
  ∃ s, H ≤ V2.proposalTime (fgsaInterface p c) s ∧ cleanWinAt p c E rho s pt.b₀

def cleanLabelWin {Pt : Type} (sOf : Pt → Slot) : WinSpec p c Pt := fun E rho pt H =>
  H ≤ V2.proposalTime (fgsaInterface p c) (sOf pt) ∧ cleanWinAt p c E rho (sOf pt) rho.horizon

def gapWin {Pt : Type} (G : Time) : WinSpec p c Pt := fun E rho _ H =>
  ∃ t, max E.t_GST H ≤ t ∧ t + G ≤ rho.horizon

def formWin {Pt : Type} (form : FinForm) (g : Nat) : WinSpec p c Pt := fun E rho _ H =>
  ∃ q : Nat, 1 ≤ q ∧ E.t_GST ≤ (q : Time) * P p ∧ H ≤ (q : Time) * P p ∧
    windowEndA form p.R (P p) p.Δ q g ≤ rho.horizon

/-- The time-start recurrence window; it is not the discrete recurrence converse. -/
def formWinAt {Pt : Type} (g : Nat) : WinSpec p c Pt := fun E rho _ H =>
  ∃ t, max E.t_GST 1 ≤ t ∧ H ≤ t ∧ windowEndAtA p.R (P p) p.Δ t g ≤ rho.horizon

def kernelWin {Pt : Type} (rOf : Pt → Nat) (dl : Nat → Time) : WinSpec p c Pt :=
  fun _ rho pt H => H ≤ (rOf pt : Time) * P p ∧ dl (rOf pt) ≤ rho.horizon

def trigWin (dl : Time → Time) : WinSpec p c PtT := fun _ rho pt H =>
  H ≤ pt.t ∧ dl pt.t ≤ rho.horizon

end AvailableChain.FGSA.Run
end
