module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSAClaims.Statements.Counts
public import AvailableChainFGSARun.Statements.Interface

@[expose] public section

/-! P3 §4.10; blueprint 01 §1.1 (200c9c07), spec 8ef4ed3b.
The five joint selections are `FGSA.liveRoot`, `FGSA.eligible`, `jointSource`,
`proposerHead`, and `FGSA.fgHead`. The live root and C_fg read no vote argument;
the proposer reads the previous-slot pool and the finality head reads the
current-slot pool. `FGSA.fgInputs` supplies the finality head triple.
All reads factor through `Node.st`; only the emitted pair can read Λ.
-/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- P3 App. A.2: bp.sourceDiscipline.v1(b,c), 01 §8.4, 02 §§3.3–3.5.
C1: path justifications, finalizations, and strictly crossed entries. -/
def certified (W : FGBlock (Fin p.n)) : Set (FGBlock (Fin p.n)) :=
  {e | ∃ U, FGBlock.Preceq U W ∧
    (e = (derive p.E p.cfg U).J ∨ e = (derive p.E p.cfg U).F ∨
      (e = (derive p.E p.cfg U).T_h ∧
        (derive p.E p.cfg U).h < (derive p.E p.cfg W).h))}

-- equation export required by BUILD §7.2 B3a
theorem certified_def (W : FGBlock (Fin p.n)) : certified p W =
  {e | ∃ U, FGBlock.Preceq U W ∧
    (e = (derive p.E p.cfg U).J ∨ e = (derive p.E p.cfg U).F ∨
      (e = (derive p.E p.cfg U).T_h ∧
        (derive p.E p.cfg U).h < (derive p.E p.cfg W).h))} := rfl

/-- The admitted FG tree (bp.store.v1, 00:516–527). -/
def treeT (st : State p.n) : Finset (FGBlock (Fin p.n)) := st.fg.TF
/-- The substrate tree in its stored base-list order. -/
def treeErased (st : State p.n) : List Block := st.base.blocks
/-- The live FJ controls (bp.frame.v1, 00:581–587). -/
def frameR (st : State p.n) : Controls (Fin p.n) := FGSA.controls p st
/-- D(X) uses the controls of the current store, also for a smaller X. -/
def domainR (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    Finset (FGBlock (Fin p.n)) := filteredFrom p.E p.cfg (frameR p st) X
/-- The FG output before erasure. -/
def finR (st : State p.n) : FGBlock (Fin p.n) := st.fg.F
/-- A strict change of the finalized block. -/
def FAdvance (st st' : State p.n) : Prop := st.fg.F ≠ st'.fg.F
/-- The AC candidates of the scheduled gate: fast-write members with a live lease.
The set has no older-label fallback (01 §1.1, T-SRC). -/
def sourceCandidates (st : State p.n) : Finset Block :=
  ((fastWriteAt st (p.round (st.slot p) * p.R)).getD []).toFinset.filter (fun B =>
    (leaseOf st B).any (fun d => decide (st.base.now < d)))
/-- C_fg is the deepest candidate in D(Σ.T) (01:59–79). -/
def jointSource (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  FGSA.deepest ((domainR p st (treeT p st)).filter
    (fun B => decide (eraseFG B ∈ sourceCandidates p st)))
/-- The proposer head reads the previous-slot pool and its resolved support. -/
def proposerHead (st : State p.n) (s : Slot) : Block :=
  FGSA.getHead p st (FGSA.proposerVotes st s) (FGSA.proposerSupport st s)
/-- The AC output S (01 §1.2; T7.3 `fgsaOutputs`). -/
def outputS (st : State p.n) : Block := st.base.stableRecord

-- equation export required by BUILD §7.2 B3a
theorem frameR_def (st : State p.n) : frameR p st = FGSA.controls p st := by rw [frameR]
-- equation export required by BUILD §7.2 B3a
theorem jointSource_def (st : State p.n) :
    jointSource p st = FGSA.deepest ((domainR p st (treeT p st)).filter
      (fun B => decide (eraseFG B ∈ sourceCandidates p st))) := by rw [jointSource]
-- equation export required by BUILD §7.2 B3a
theorem sourceCandidates_def (st : State p.n) : sourceCandidates p st =
    ((fastWriteAt st (p.round (st.slot p) * p.R)).getD []).toFinset.filter (fun B =>
      (leaseOf st B).any (fun d => decide (st.base.now < d))) := by rw [sourceCandidates]
-- equation export required by BUILD §7.2 B3a
theorem domainR_def (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    domainR p st X = filteredFrom p.E p.cfg (frameR p st) X := by rw [domainR]
-- equation export required by BUILD §7.2 B3a
theorem treeT_def (st : State p.n) : treeT p st = st.fg.TF := by rw [treeT]
-- equation export required by BUILD §7.2 B3a
theorem proposerHead_def (st : State p.n) (s : Slot) : proposerHead p st s =
    FGSA.getHead p st (FGSA.proposerVotes st s) (FGSA.proposerSupport st s) := by
  rw [proposerHead]
-- equation export required by BUILD §7.2 B3a
theorem FAdvance_def (st st' : State p.n) :
    FAdvance p st st' = (st.fg.F ≠ st'.fg.F) := by rw [FAdvance]

variable {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

def R_at (i : Nat) (x : V) : Controls (Fin p.n) := frameR p (storeAt p c E rho i x)
def D_at (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) :
    Finset (FGBlock (Fin p.n)) := domainR p (storeAt p c E rho i x) X
def FAdvanceAt (i : Nat) (x : V) : Prop :=
  (∃ o t, rho.events[i]? = some (.deliver x o t)) ∧
    FAdvance p (storeAt p c E rho i x) (storeAt p c E rho (i + 1) x)
/-- The erased candidates at the post-clock FG action read. -/
def candidatesAt (x : V) (r : Nat) : Option (Finset Block) :=
  (postClock E rho x (p.actionTime r)).map (fun nd => sourceCandidates p nd.st)
/-- The proposer's post-clock head at t_s. -/
def proposalHeadAt (s : Slot) : Option Block :=
  (postClock E rho (V2.proposerOf rho (fgsaInterface p c) s)
    (V2.proposalTime (fgsaInterface p c) s)).map (fun nd => proposerHead p nd.st s)
def actionHead (x : V) (r : Nat) : Option Block :=
  (postClock E rho x (p.actionTime r)).map (fun nd => FGSA.fgHead p nd.st)
def actionTriple (x : V) (r : Nat) : Option HeadFields :=
  (postClock E rho x (p.actionTime r)).map (fun nd => (FGSA.fgInputs p nd.st).2)

/-- A row names a height and root, never an FG block (01 §8.4). -/
def namedEntry : NamedHeightPair → Option (Height × BlockId)
  | .empty => none
  | .vote h e _ => some (h, e)
/-- The named height and root are those of an ancestor of B. -/
def EntryBelow (e : Height × BlockId) (B : FGBlock (Fin p.n)) : Prop :=
  ∃ X, FGBlock.Preceq X B ∧ (hOf p.E p.cfg X, X.root) = e
/-- The FG seat of the signed row a belongs to x (S3c §2.7, M13). -/
def RowSigner (a : RowWire p.n) (x : V) : Prop :=
  ∃ r i, a.auth = .seat (.fg r) i ∧ rho.seatOf (RunLabel.base (.fg r)) i = x
/-- Honest y emitted the signed round-r row a at event j. -/
def HonestRowAt (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) : Prop :=
  y ∈ rho.honest ∧ a.round? = some r ∧
    ∃ t, rho.events[j]? = some (.tick y t) ∧ ofRow p a ∈ V2.Run.emitsAt E rho j
def HonestRowBefore (k : Nat) (y : V) (r : Nat) (a : RowWire p.n) : Prop :=
  ∃ j < k, HonestRowAt p c E rho j y r a
-- equation export required by BUILD §7.2 B3a
theorem HonestRowBefore_def (k : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    HonestRowBefore p c E rho k y r a = (∃ j < k, HonestRowAt p c E rho j y r a) := rfl
/-- A valid signed row with the specified round and holder. -/
def RowComplete (x : V) (r : Nat) (a : RowWire p.n) : Prop :=
  a.valid = true ∧ a.round? = some r ∧ RowSigner p c rho a x
/-- The honest proposal and the exact signed rows of its emitted wire. -/
def HonestCarrier (s : Slot) (Q : Block) (rows : List (RowWire p.n)) : Prop :=
  HonestProposal E rho (fgsaInterface p c) s Q ∧
    ∃ o raw sup, V2.Run.emits E rho (V2.proposerOf rho (fgsaInterface p c) s) o
        (V2.proposalTime (fgsaInterface p c) s) ∧ o.payload = .proposal Q raw sup rows
/-- The one held-block domain for later finality channels (S3 D25). -/
def HeldAt (i : Nat) (x : V) (W : FGBlock (Fin p.n)) : Prop :=
  x ∈ rho.honest ∧ W ∈ (storeAt p c E rho i x).fg.TF
/-- A block held at an honest read strictly before index i. -/
def BlockInRunBefore (i : Nat) (W : FGBlock (Fin p.n)) : Prop :=
  ∃ j < i, ∃ x, HeldAt p c E rho j x W

-- equation export required by BUILD §7.2 B3a
omit [DecidableEq V] in
theorem RowSigner_def (a : RowWire p.n) (x : V) : RowSigner p c rho a x =
    (∃ r i, a.auth = .seat (.fg r) i ∧ rho.seatOf (RunLabel.base (.fg r)) i = x) := by
  rw [RowSigner]
-- equation export required by BUILD §7.2 B3a
theorem HonestRowAt_def (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    HonestRowAt p c E rho j y r a = (y ∈ rho.honest ∧ a.round? = some r ∧
      ∃ t, rho.events[j]? = some (.tick y t) ∧ ofRow p a ∈ V2.Run.emitsAt E rho j) := by
  rw [HonestRowAt]

end AvailableChain.FGSA.Run
end
