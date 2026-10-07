module
public import AvailableChainPCSA.Model.Handlers
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool

public section

namespace AvailableChain.PCSA
open SimplexFG
variable {n : Nat}

/-- Normalization changes no FG field. -/
theorem pcsa_normalizeS_fg (st : State n) : (normalizeS st).fg = st.fg := by
  unfold normalizeS
  split <;> rfl

/-- Reconciliation changes no FG field. -/
theorem pcsa_reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  unfold reconcile
  rw [pcsa_normalizeS_fg]

/-- A row batch changes no FG field. -/
theorem pcsa_fold_admitRow_fg (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    delta admitRow
    cases hdecode : a.decode? <;> dsimp only
    split <;> rfl

/-- A raw ack batch changes no FG field. -/
theorem pcsa_fold_poolAckRaw_fg (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).fg = st.fg := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.2]

/-- Block admission changes FG only through the existing window handler. -/
theorem pcsa_admitBlock_fg_cases (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) :
    (admitBlock p st s N).fg = st.fg ∨
      ∃ P, parentFG st N.erase = some P ∧
        (admitBlock p st s N).fg =
          FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) := by
  delta admitBlock
  split
  · exact Or.inl rfl
  · cases hP : parentFG st N.erase
    · exact Or.inl rfl
    · rename_i P
      dsimp only
      split
      · right
        refine ⟨P, rfl, ?_⟩
        rw [pcsa_fold_admitRow_fg, (collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
        cases N.pc <;> dsimp only <;> split_ifs <;> simp only [pcsa_reconcile_fg] <;> rfl
      · exact Or.inl rfl

end AvailableChain.PCSA
end
