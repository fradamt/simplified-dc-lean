module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSA.Statements.Invariants

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- bp.sameLabel.v1: two honest raw results at one label are compatible. -/
def SameLabelAt (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (s : Slot) : Prop :=
  ∀ x y B C, x ∈ rho.honest → y ∈ rho.honest →
    gateResult p c E rho x s = some (some B) →
    gateResult p c E rho y s = some (some C) → Block.Compatible B C

def SameLabelClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtS),
    SameLabelPrem p c E rho pt → SameLabelAt p c E rho pt.s

/-- ap.headReachesLo.v6, pure clauses 1–3 (02 §7).
The controls and anchor are those of the full store, also for a smaller X. -/
def HeadReachesLoAt (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (raw support : List (GridCO.Wire p.n)) : Prop :=
  let D := filteredFrom p.E p.cfg (FGSA.controls p st) X
  let A := FGSA.liveRoot p st
  let H := FGSA.headInTree p st (FGSA.erasedList st D) raw support
  ((∃ B ∈ D, eraseFG B = A) ∨
      (∃ B ∈ D, (eraseFG B).parent? = some A ∧ FGSA.eligible p st raw support (eraseFG B) = true) →
    ∃ B ∈ D, eraseFG B = H ∧ (FGSA.controls p st).lo ≤ hOf p.E p.cfg B) ∧
  ((¬ ∃ B ∈ D, eraseFG B = A) →
    (∀ B ∈ D, (eraseFG B).parent? = some A → FGSA.eligible p st raw support (eraseFG B) = false) →
    H = A) ∧
  (A = eraseFG (FGSA.controls p st).Z → D.Nonempty → (FGSA.controls p st).Z ∈ D)

def HeadReachesLoClaim (p : Params) : Prop :=
  ∀ (st : State p.n) (X : Finset (FGBlock (Fin p.n)))
    (raw support : List (GridCO.Wire p.n)),
    Reachable p st → X ⊆ st.fg.TF →
    (∀ B ∈ X, ∀ A, FGBlock.Preceq A B → A ∈ X) →
    HeadReachesLoAt p st X raw support

/- bp.suffixWalk.v1 is the Gen.Pure statement family in Statements/Pure/Walk:
WalkCoversOfDominatedSuffixStatement, WalkExactOfDominatedSuffixStatement,
WalkReanchorOfDominatedSuffixStatement, WalkAvoidsUnsupportedChildStatement,
WalkCoversOfDominatedSuffixOfAnchorEligibleStatement,
WalkTerminalOfDescendantDepthBoundStatement,
WalkNoEligibleChildOfAnchorClosedStatement, GhostTransferSfxStatement.
GEN-FIRST: cite these statements; do not add aliases or claim wrappers. -/

end AvailableChain.FGSA.Run
end
