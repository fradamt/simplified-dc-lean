module
public import AvailableChainFGSA.Statements.Invariants

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

-- The generated matcher bodies are definitionally equal.
set_option linter.auxLemma false in
private theorem hygiene_admitBlock_match_1_eq :
    @admitBlock.match_1 = @hygiene_admitBlock.match_1 := rfl

end AvailableChain.FGSA

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_admitRow (p : Params) (st : State p.n) (a : RowWire p.n) : State p.n :=
  match a.decode? with
  | some _ =>
      if a ∈ st.rowPool then st else { st with rowPool := st.rowPool ++ [a] }
  | none => st

-- The generated matcher bodies are definitionally equal.
set_option linter.auxLemma false in
private theorem hygiene_admitRow_match_1_eq :
    @admitRow.match_1 = @hygiene_admitRow.match_1 := rfl

end AvailableChain.FGSA

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_process (p : Params) (st : State p.n) (o : Wire p.n) : State p.n :=
  match o.decode with
  | some (.vote s i b) => admitHead p st s i b
  | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
  | some (.block s N) => admitBlock p st s N
  | none => st

-- The generated matcher bodies are definitionally equal.
set_option linter.auxLemma false in
private theorem hygiene_process_match_1_eq :
    @process.match_1 = @hygiene_process.match_1 := rfl

end AvailableChain.FGSA

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_headLabel {n : Nat} {mode : HeadMode} (o : Wire n mode) : Option Slot :=
  match o.auth, o.payload with
  | .seat r _, .head _ => some r
  | _, _ => none

-- The generated matcher bodies are definitionally equal.
set_option linter.auxLemma false in
private theorem hygiene_headLabel_match_1_eq :
    @headLabel?.match_1 = @hygiene_headLabel.match_1 := rfl

end AvailableChain.GridCO

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.FGSA.hygiene_admitBlock_match_1_eq] at *;
    try rw [AvailableChain.FGSA.hygiene_admitRow_match_1_eq] at *;
    try rw [AvailableChain.FGSA.hygiene_process_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_headLabel_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.FGSA.hygiene_admitBlock_match_1_eq] at *;
    try rw [AvailableChain.FGSA.hygiene_admitRow_match_1_eq] at *;
    try rw [AvailableChain.FGSA.hygiene_process_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_headLabel_match_1_eq] at *;
    all_goals split at $h:ident))

public section

namespace AvailableChain.FGSA

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] HEAD receipt preserves read metadata. -/
theorem admitVote_headDomain {n : Nat} {mode : GridCO.HeadMode}
    (p : GridCO.Params) (st : GridCO.State n mode) (o : GridCO.Wire n mode) :
    (GridCO.admitVote p st o).headDomain = st.headDomain := by
  unfold GridCO.admitVote
  hygiene_split <;> try rfl
  dsimp only
  split_ifs <;> rfl

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] Carried HEAD folds preserve metadata. -/
theorem foldVotes_headDomain {n : Nat} {mode : GridCO.HeadMode}
    (p : GridCO.Params) (st : GridCO.State n mode) (raw : List (GridCO.HeadWire n mode)) :
    (raw.foldl (fun acc row => GridCO.admitVote p acc (GridCO.fromHead row)) st).headDomain =
      st.headDomain := by
  induction raw generalizing st with
  | nil => rfl
  | cons a raw ih =>
      rw [List.foldl_cons, ih, admitVote_headDomain]

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] Proposal receipt preserves metadata. -/
theorem admitProposal_headDomain {n : Nat} {mode : GridCO.HeadMode}
    (p : GridCO.Params) (st : GridCO.State n mode) (o : GridCO.Wire n mode)
    (B : Block) (raw : List (GridCO.HeadWire n mode)) :
    (GridCO.admitProposal p st o B raw).headDomain = st.headDomain := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · rfl
  · exact foldVotes_headDomain p _ raw

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] Row receipt preserves metadata. -/
theorem admitRow_headDomain (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.headDomain = st.base.headDomain := by
  unfold admitRow
  hygiene_split <;> try rfl
  hygiene_split <;> rfl

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] Row folds preserve metadata. -/
theorem foldRows_headDomain (p : Params) (st : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).base.headDomain = st.base.headDomain := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih => rw [List.foldl_cons, ih, admitRow_headDomain]

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] Every local receipt preserves metadata. -/
theorem process_headDomain (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.headDomain = st.base.headDomain := by
  unfold process
  hygiene_split
  · exact admitVote_headDomain _ _ _
  · exact admitRow_headDomain _ _ _
  · unfold admitBlock
    hygiene_split
    · rfl
    · hygiene_split
      · rfl
      · hygiene_split
        · dsimp only
          rw [foldRows_headDomain]
          split_ifs
          · exact admitProposal_headDomain _ _ _ _ _
          · unfold reconcile normalizeS
            dsimp only
            split_ifs <;> exact admitProposal_headDomain _ _ _ _ _
        · rfl
  · rfl

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] A clock restores the cumulative metadata. -/
theorem clock_headDomain (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.headDomain = st.base.headDomain := by
  simp only [clock, clockPre, gateStep, normalizeS, onView, GridCO.expire]
  split_ifs <;> rfl

/-- [ROOT-DIGEST-2 W1; DC temporary resolution domain] Reachable cumulative stores keep none. -/
theorem base_headDomain_none (p : Params) {st : State p.n} (h : Reachable p st) :
    st.base.headDomain = none := by
  induction h with
  | init => rfl
  | tick t _ ih => rw [clock_headDomain, ih]
  | deliver o _ ih => rw [process_headDomain, ih]

end AvailableChain.FGSA
end
