module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSAClaims.Statements.Witness -- shake: keep (F0.8b append point)
public import AvailableChainFGSAClaims.Statements.Counts
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.Pure.Props

@[expose] public section

/-! F0.5: HEALED through the GLY property kernel (P3 §4.6, D43, D61).
F0.8b adds the AC-output Props and healing input below these declarations. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- Post-gate cut at gate times; inclusive cut otherwise
(21 H.22:2985–2994; 22 §1:167–176). -/
def healStart (t : Time) : Nat :=
  if isGateTime p t then afterTicksIdx rho t else timeIdx rho t

/-- All event-prefix states from the cut through the run's last state
(21 H.22:2988–2991; 22 §1:170–173). -/
def HealSuffix (t : Time) (i : Nat) : Prop :=
  healStart p c rho t ≤ i ∧ i ≤ rho.events.length

/-- HEALED (21 H.22:2996–2999; 22 §1:178–181), with the Gen statements
`Gen.Pure.CompatOn`, `MonoOn`, `BelowOn`, and `ServedOn` from
`AvailableChainGeneric.Statements.Pure.Props` (GLY property kernel).

Compatibility: 21:2996–2997; 22:178–179. P3 D43/D61 uses the cross-time form.
Monotonicity: 21:2997; 22:179. The index is an event prefix.
F below S: 21:2998; 22:180. Both reads use the same event prefix.
Proposal service: 21:2998–2999; 22:180–181. The gate read is after all ticks;
the gate must be within the finite run horizon (P3 §4.6). -/
def Healed (t : Time) : Prop :=
  Gen.Pure.CompatOn (· ∈ rho.honest) (S_at p c E rho) (HealSuffix p c rho t) ∧
  Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (HealSuffix p c rho t) ∧
  Gen.Pure.BelowOn (· ∈ rho.honest) (F_at p c E rho) (S_at p c E rho)
    (HealSuffix p c rho t) ∧
  (∀ s B, t ≤ V2.proposalTime (fgsaInterface p c) s →
    SA.gateTime p.toParams s ≤ rho.horizon →
    HonestProposal E rho (fgsaInterface p c) s B →
    Gen.Pure.ServedOn (· ∈ rho.honest)
      (fun u x => (fgsaInterface p c).stable (afterTicks E rho u x)) B
      (· = SA.gateTime p.toParams s))

end AvailableChain.FGSA.Run
end
