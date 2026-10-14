module
public import AvailableChainFGCompose.Statements.Promotion
public import AvailableChainFGCompose.Statements.Population.Seats

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (H : FGHeightView (Fin n)) (T : FGTiming)
variable (pair : Wire → NamedHeightPair)

/-- Earlier-or-current signed coverage at the actual source read. -/
def OpeningCoveredFG (A : Finset (Fin n)) (r : Nat) (Q : Block) : Prop := ∀ i ∈ A,
  let x := safetyHolder S rho i;
  ∃ K nd j rSent a, postClock E rho x (T.action r) = some nd ∧
    actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
    Block.Preceq Q (R.erase K) ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
    namedEntry (pair a) = some ((H K).h, (H K).T_h.root)

theorem OpeningCoveredFG_def (A : Finset (Fin n)) (r : Nat) (Q : Block) :
    OpeningCoveredFG R S E rho H T pair A r Q =
      (∀ i ∈ A,
  let x := safetyHolder S rho i;
  ∃ K nd j rSent a, postClock E rho x (T.action r) = some nd ∧
    actionSourceFG R E rho T x r = some (some K) ∧ K ∈ (R.core nd).fg.TF ∧
    Block.Preceq Q (R.erase K) ∧ rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
    namedEntry (pair a) = some ((H K).h, (H K).T_h.root)) := rfl

end AvailableChain.FGCompose
end
