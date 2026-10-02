module
public import AvailableChainFGSA.Proofs.Metadata

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

private theorem admission_r6wW (p : Params) (st : State p.n) (h : CStoreInv p st)
    (valid : ∀ P s x rs, FGBlock.node P s x rs ∈ st.fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true)
    (s : Slot) (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    ∀ P t x rs, FGBlock.node P t x rs ∈ (admitBlock p st s b raw sup rows).fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  cases hP : parentFG st b with
  | none =>
      rw [admitBlock_refused p st s b raw sup rows (Or.inl hP)]
      exact valid
  | some P =>
      cases accepted : blockAccepted p st s b P rows with
      | false =>
          rw [admitBlock_refused p st s b raw sup rows (Or.inr ⟨P, hP, accepted⟩)]
          exact valid
      | true =>
          obtain ⟨pool, eq, _⟩ := admitBlock_accepted_eq p st s b raw sup P rows hP accepted
          intro Q t x rs stored a ha
          rw [eq] at stored
          dsimp only at stored
          rw [(accepted_st2 p st h s b raw sup P rows hP accepted).2.1,
            Finset.mem_insert] at stored
          rcases stored with new | old
          · change FGBlock.node Q t x rs = .node P b.slot (packInner (appOf b.body) rows)
              (rows.filterMap RowWire.toRow?) at new
            cases new
            obtain ⟨wire, hw, hd⟩ := List.mem_filterMap.mp ha
            have hv := (rowsValidForParent_iff p P b.slot rows).mp
              (blockAccepted_rowsValid accepted) wire hw
            rw [Window.rowValidW_def, hd] at hv
            exact hv
          · exact valid Q t x rs old a ha

private theorem process_r6wW (p : Params) (st : State p.n) (h : CStoreInv p st)
    (valid : ∀ P s x rs, FGBlock.node P s x rs ∈ st.fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true) (o : Wire p.n) :
    ∀ P s x rs, FGBlock.node P s x rs ∈ (process p st o).fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  change ∀ P s x rs, FGBlock.node P s x rs ∈ (match o.decode with
    | some (.vote t i b) => admitHead p st t i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block t b raw sup rows) => admitBlock p st t b raw sup rows
    | none => st).fg.TF → ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true
  cases decoded : o.decode with
  | none => exact valid
  | some input =>
      cases input with
      | vote t i b => exact valid
      | row i body =>
          change ∀ P s x rs,
            FGBlock.node P s x rs ∈ (admitRow p st ⟨o.auth, body⟩).fg.TF →
              ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true
          rcases admitRow_eq p st ⟨o.auth, body⟩ with eq | eq <;> rw [eq] <;> exact valid
      | block t b raw sup rows => exact admission_r6wW p st h valid t b raw sup rows

/-- [S4.2b r2 ruling] Every stored non-genesis block has R6W-valid decoded
rows at its immutable parent. Unchecked Reachable deliveries suffice for R6W.
This is a separate invariant; no field is added to either store invariant. -/
theorem stored_r6wW (p : Params) {st : State p.n} (reachable : Reachable p st) :
    ∀ P s x rs, FGBlock.node P s x rs ∈ st.fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  induction reachable with
  | init =>
      intro P s x rs stored
      change FGBlock.node P s x rs ∈ ({.genesis} : Finset (FGBlock (Fin p.n))) at stored
      simp only [Finset.mem_singleton] at stored
      cases stored
  | tick t _ ih =>
      simpa only [clock_fg] using ih
  | deliver o reachable ih =>
      exact process_r6wW p _ (storeInvariant p _ reachable) ih o

/-- Tree closure extends the new admission invariant to every ancestor row
of a stored block, at the active window parent view. -/
theorem stored_chain_r6wW (p : Params) {st : State p.n} (reachable : Reachable p st)
    (B : FGBlock (Fin p.n)) (stored : B ∈ st.fg.TF) :
    ∀ P s x rs, FGBlock.Preceq (.node P s x rs) B →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  intro P s x rs ancestor a ha
  have closed := KitFG.ancestor_closed_of_parent_closed st.fg.TF
    (storeInvariant p st reachable).fg.closed
  exact stored_r6wW p reachable P s x rs (closed B stored _ ancestor) a ha

end AvailableChain.FGSA
end
