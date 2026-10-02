module
public import AvailableChainFGSAClaims.Statements.Fold

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure
open Gen.V2.Duty (faulty)

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Raw action-history input. DC: SAME named-row cut; INTENTIONAL fixed FG authentication. -/
def finHeight {n : Nat} (a : RowWire n) : Option Nat :=
  a.payload.finality_pair.map (·.height)

/-- Raw action-history input. DC: SAME named-row cut; INTENTIONAL fixed FG authentication. -/
structure FreshPrem (q y : Nat) (X : FGBlock (Fin p.n)) where
  /-- FINAL 22:43–57: execution, schedule and no restart. -/
  base : BaseSet p c E rho
  /-- FINAL 22:948–958: every quorum has an honest row. -/
  faultQ : FaultQ p.n (faulty rho).card
  /-- FINAL 22:954–956,1068–1069: strict raw-row cut after inclusion. -/
  cut : Time
  /-- FINAL 22:948–958: no later than the next action. -/
  early : cut ≤ p.actionTime (q + 1)
  /-- FINAL 22:954–956: raw rows of the full chain through X. -/
  rows : ChainRowsBefore p c E rho X cut
  /-- FINAL 22:948–950,1054: no next-height honest row before the action. -/
  noNextRow : ∀ j x r a h t, HonestRowAt p c E rho j x r a →
    rowHeight a = some h → y + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (q + 1) ≤ t
  /-- FINAL 22:952–958,1068–1070: no finality row at or above y. -/
  noFinRow : ∀ j x r a h t, HonestRowAt p c E rho j x r a →
    finHeight a = some h → y ≤ h → eventTime rho j = some t →
    p.actionTime (q + 1) ≤ t

end AvailableChain.FGSA.Run
end
