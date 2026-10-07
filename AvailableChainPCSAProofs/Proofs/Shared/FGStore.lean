module
public import AvailableChainFGSA.Proofs.WindowStore
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

/-- A delivery moves finality only to a descendant, for every store. -/
theorem pcsa_process_F_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    FGBlock.Preceq st.fg.F (process p st o).fg.F := by
  have pool_fg (a : AckWire p.n) : (poolAck p st a).fg = st.fg := by
    change (match a.decode? with
      | some (s, i, r) =>
          if st.slot p < s || !ackSlotOK st s r || a ∈ st.ackPool then st else
          if 2 ≤ (seatAcks st s i).length && !decide (r ∈ seatAcks st s i) then st else
          { st with ackPool := st.ackPool ++ [a] }
      | none => st).fg = st.fg
    cases hd : a.decode? with
    | none => rfl
    | some v =>
        rcases v with ⟨s, i, r⟩
        dsimp only
        split_ifs <;> rfl
  change FGBlock.Preceq st.fg.F (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | some (.ack _ _ b) => admitAck p st ⟨o.auth, b⟩
    | some (.pc c) => admitPC st c
    | none => st).fg.F
  cases hd : o.decode with
  | none =>
      dsimp only
      exact KitFG.preceq_refl _
  | some msg =>
      cases msg with
      | vote s i b =>
          dsimp only
          exact KitFG.preceq_refl _
      | row i body =>
          dsimp only
          have hr := pcsa_fold_admitRow_fg p st [⟨o.auth, body⟩]
          change (admitRow p st ⟨o.auth, body⟩).fg = st.fg at hr
          rw [hr]
          exact KitFG.preceq_refl _
      | block s N =>
          dsimp only
          rcases pcsa_admitBlock_fg_cases p st s N with he | ⟨P, _, he⟩
          · rw [he]
            exact KitFG.preceq_refl _
          · rw [he]
            exact FGSA.Window.window_on_block_F_mono p p.K_W st.fg _
      | ack s i b =>
          dsimp only
          change FGBlock.Preceq st.fg.F (collectPCs (poolAck p st ⟨o.auth, b⟩)).fg.F
          rw [(collectPCs_frame _).2.2.2.2, pool_fg]
          exact KitFG.preceq_refl _
      | pc cert =>
          dsimp only
          change FGBlock.Preceq st.fg.F
            (if cert.wellFormed then collectPCs (cert.acks.foldl poolAckRaw st) else st).fg.F
          cases hc : cert.wellFormed
          · exact KitFG.preceq_refl _
          · change FGBlock.Preceq st.fg.F (collectPCs (cert.acks.foldl poolAckRaw st)).fg.F
            rw [(collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
            exact KitFG.preceq_refl _

end AvailableChain.PCSA
end
