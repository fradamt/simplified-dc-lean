module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainFGSA.Proofs.BlockAncestry

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The write sets of the steps (Task 7, Step 2): for each step, the fields that
it does not write, and the exact gate effects that K1 and K6 need. -/

variable {n : Nat}

/-! ### `admitHead` -/

/-- [helper] A vote writes no FG field. -/
theorem admitHead_fg (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) :
    (admitHead p st s i b).fg = st.fg := rfl
/-- [helper] A vote writes no block. -/
theorem admitHead_base_blocks (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) :
    (admitHead p st s i b).base.blocks = st.base.blocks :=
  @GridCO.admitVote_blocks GridCO.slowLeasePolicy _ _ _ _
/-- [helper] A vote does not write S. -/
theorem admitHead_base_stable (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) :
    (admitHead p st s i b).base.stableRecord = st.base.stableRecord :=
  @GridCO.admitVote_stable GridCO.slowLeasePolicy _ _ _ _
/-- [helper] A vote writes no lease. -/
theorem admitHead_obligations (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n)
    (b : Block) : (admitHead p st s i b).base.obligations = st.base.obligations :=
  @GridCO.admitVote_obligations GridCO.slowLeasePolicy _ _ _ _
/-- [helper] A vote does not write `fastWrite`. -/
theorem admitHead_fastWrite (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) :
    (admitHead p st s i b).fastWrite = st.fastWrite := rfl
/-- [helper] A vote writes no saved result. -/
theorem admitHead_genuine (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) :
    (admitHead p st s i b).base.genuine = st.base.genuine := by
  simp only [admitHead, GridCO.admitVote]
  split <;> rfl

/-! ### `admitRow` and `admitBlock` -/

/-- [helper] A row changes only the row pool: the state is unchanged, or the row
is appended. -/
theorem admitRow_eq (p : Params) (st : State p.n) (a : RowWire p.n) :
    admitRow p st a = st ∨ admitRow p st a = { st with rowPool := st.rowPool ++ [a] } := by
  unfold admitRow
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

/-- [helper] A refused block changes nothing: no stored parent, or a failed
acceptance test. -/
theorem admitBlock_refused (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (h : parentFG st b = none ∨
      ∃ P, parentFG st b = some P ∧ blockAccepted p st s b P rows = false) :
    admitBlock p st s b raw support rows = st := by
  unfold admitBlock
  rcases h with h | ⟨P, hP, ha⟩
  · rw [h]
  · rw [hP]
    simp only [ha, Bool.false_eq_true, ite_false]

/-! ### `onView`, `normalizeS`, `reconcile` -/

/-- [M2] `onView` writes no FG field. -/
theorem onView_fg (f : GridCO.State n → GridCO.State n) (st : State n) :
    (onView f st).fg = st.fg := rfl
/-- [M2] `onView` keeps the cumulative block list. -/
theorem onView_base_blocks (f : GridCO.State n → GridCO.State n) (st : State n) :
    (onView f st).base.blocks = st.base.blocks := rfl
/-- [M2] `onView` writes no proposal wire. -/
theorem onView_proposals (f : GridCO.State n → GridCO.State n) (st : State n) :
    (onView f st).proposals = st.proposals := rfl
/-- [M2] `onView` writes no row. -/
theorem onView_rowPool (f : GridCO.State n → GridCO.State n) (st : State n) :
    (onView f st).rowPool = st.rowPool := rfl
/-- [M2] `onView` does not write `fastWrite`. -/
theorem onView_fastWrite (f : GridCO.State n → GridCO.State n) (st : State n) :
    (onView f st).fastWrite = st.fastWrite := rfl

/-- [helper] `normalizeS` writes no FG field. -/
theorem normalizeS_fg (st : State n) : (normalizeS st).fg = st.fg := by
  unfold normalizeS
  split <;> rfl
/-- [helper] `normalizeS` writes only S: `S := F` if `F ⋠ S`. -/
theorem normalizeS_fields (st : State n) :
    normalizeS st = { st with base := { st.base with
      stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F } } := by
  unfold normalizeS
  split <;> rfl

/-- [helper] `reconcile` writes no FG field. -/
theorem reconcile_fg (st : State n) : (reconcile st).fg = st.fg := by
  unfold reconcile
  rw [normalizeS_fg]

/-! ### The GridCO steps that the tick runs keep `blocks` -/

/-- [helper] The freeze cache step keeps `blocks`. -/
theorem freeze_blocks (q : GridCO.Params) (v : GridCO.State n) (r : Slot) :
    (GridCO.freeze q v r).blocks = v.blocks := rfl
/-- [helper] The release step keeps `blocks`. -/
theorem release_blocks (p : SA.Params) (v : GridCO.State n) (r : Slot) :
    (SA.release p v r).blocks = v.blocks := rfl
/-- [helper] The SA gate with the walk from `a` keeps `blocks`. Proof:
`@GridCO.gateFrom_blocks GridCO.slowLeasePolicy p.engine n a v r` (the default
instance would elaborate the GRID gate). -/
theorem saGate_blocks (p : SA.Params) (a : Block) (v : GridCO.State n) (r : Slot) :
    (SA.gateFrom p a v r).blocks = v.blocks :=
  @GridCO.gateFrom_blocks GridCO.slowLeasePolicy p.engine n a v r

/-! ### The gate -/

/-- [helper] The gate writes no FG field. -/
theorem gateStep_fg (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).fg = st.fg := by
  unfold gateStep
  rw [normalizeS_fg]
  split <;> rfl
/-- [helper] The gate keeps the cumulative block list. -/
theorem gateStep_base_blocks (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).base.blocks = st.base.blocks := by
  unfold gateStep
  rw [normalizeS_fields]
  split <;> rfl
/-- [helper] The gate writes no proposal wire. -/
theorem gateStep_proposals (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).proposals = st.proposals := by
  unfold gateStep
  rw [normalizeS_fields]
  split <;> rfl
/-- [helper] The gate writes no row. -/
theorem gateStep_rowPool (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).rowPool = st.rowPool := by
  unfold gateStep
  rw [normalizeS_fields]
  split <;> rfl

/-- [helper] `savedGenuine` of a list with one appended label `s`, when `s` was
not saved: label `s` reads the new result, and every other label is unchanged. -/
theorem savedGenuine_append (v : GridCO.State n) (s : Slot) (x : Option Block)
    (hnew : GridCO.savedGenuine v s = none) (r : Slot) :
    GridCO.savedGenuine { v with genuine := v.genuine ++ [(s, x)] } r =
      if r = s then some x else GridCO.savedGenuine v r := by
  unfold GridCO.savedGenuine at hnew ⊢
  simp only [Option.map_eq_none_iff] at hnew
  rw [List.find?_append]
  split
  · next hr =>
    subst hr
    rw [hnew]
    simp
  · next hr =>
    cases hf : v.genuine.find? (fun row => row.1 == r) with
    | some row => simp
    | none =>
        have hne : ((s, x).1 == r) = false := beq_false_of_ne (Ne.symm hr)
        simp [List.find?, hne]

/-- [helper] The SA gate with the walk from `a`, on a view whose label `s` is not
saved, appends `(s, confirmationFrom a)` to `genuine` and writes no other saved
result. -/
theorem saGate_genuine (p : SA.Params) (a : Block) (v : GridCO.State n) (s : Slot)
    (hnew : GridCO.savedGenuine v s = none) :
    (SA.gateFrom p a v s).genuine = v.genuine ++ [(s, SA.confirmationFrom p a v s)] := by
  have hrec : ∀ x, @GridCO.recordGenuine GridCO.slowLeasePolicy n v s x =
      v.genuine ++ [(s, x)] := by
    intro x
    simp [GridCO.recordGenuine, hnew]
  have hfold : ∀ (bs : List Block) (f : Block → List Nat) (d : Time) (acc : GridCO.State n),
      (bs.foldl (fun acc b => (f b).foldl
        (fun acc g => GridCO.writeObligation acc b g d) acc) acc).genuine = acc.genuine := by
    intro bs f d
    induction bs with
    | nil => intro acc; rfl
    | cons b bs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        generalize f b = gs
        induction gs generalizing acc with
        | nil => rfl
        | cons g gs ihg => simp only [List.foldl_cons]; rw [ihg]; rfl
  simp only [SA.gateFrom, GridCO.gateFrom, SA.confirmationFrom]
  split
  · next hc => simp only [hrec, hc]
  · next h hc =>
    split
    · simp only [hrec, hc]
    · rw [hfold]
      simp only [hrec, hc]

/-- [bp bp.leaseOrigins.v1; K1, K6; spec 4e85ff34: 885–913, 1280–1297] A fresh
gate saves the confirmation of the view with the walk from `Σ.F`
(`genuine_result`) and adds exactly `fastSet` of the view at the same anchor; a
saved label changes neither. -/
theorem gateStep_fresh (p : Params) (st : State p.n) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) :
    GridCO.savedGenuine (gateStep p st s).base s =
      some (SA.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) ∧
    (∀ r ≠ s, GridCO.savedGenuine (gateStep p st s).base r = GridCO.savedGenuine st.base r) ∧
    (gateStep p st s).fastWrite =
      st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] := by
  have hv : GridCO.savedGenuine (actView st) s = none := hnew
  have hg := saGate_genuine p.toParams (eraseFG st.fg.F) (actView st) s hv
  have hsave : ∀ r, GridCO.savedGenuine (gateStep p st s).base r =
      if r = s then some (SA.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s)
      else GridCO.savedGenuine st.base r := by
    intro r
    have := savedGenuine_append (actView st) s
      (SA.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) hv r
    unfold gateStep
    rw [normalizeS_fields]
    simp only [hnew, Option.isSome_none, Bool.false_eq_true, ite_false]
    unfold onView
    simp only [GridCO.savedGenuine] at this ⊢
    rw [hg]
    exact this
  refine ⟨by simpa using hsave s, fun r hr => by simpa [hr] using hsave r, ?_⟩
  unfold gateStep
  rw [normalizeS_fields]
  simp [hnew]

/-- [helper] A saved label: the gate is `normalizeS` only. -/
theorem gateStep_saved (p : Params) (st : State p.n) (s : Slot)
    (hs : (GridCO.savedGenuine st.base s).isSome) : gateStep p st s = normalizeS st := by
  unfold gateStep
  simp only [hs, ite_true]

/-- [helper] Every member of `fastSet` at anchor `a` is a non-genesis prefix of
the confirmation with the walk from `a`. -/
theorem fastSet_prefix (p : Params) (a : Block) (v : GridCO.State p.n) (s : Slot)
    {B : Block} (hB : B ∈ fastSet p a v s) :
    ∃ h, SA.confirmationFrom p.toParams a v s = some h ∧ Block.Preceq B h ∧ B ∈ v.blocks ∧
      B ≠ .genesis := by
  unfold fastSet at hB
  split at hB
  · simp at hB
  · next h hc =>
    split at hB
    · simp at hB
    · simp only [List.mem_filter, Bool.and_eq_true] at hB
      exact ⟨h, hc, hB.2.1.2, hB.1, by simpa using hB.2.1.1⟩

/-! ### The tick -/

/-- [helper] The tick before the gate writes no FG field, no block, no proposal
wire, no row, no saved result and no `fastWrite` set. -/
theorem clockPre_fields (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fg = st.fg ∧ (clockPre p st t).base.blocks = st.base.blocks ∧
    (clockPre p st t).proposals = st.proposals ∧ (clockPre p st t).rowPool = st.rowPool ∧
    (clockPre p st t).base.genuine = st.base.genuine ∧
    (clockPre p st t).fastWrite = st.fastWrite := by
  unfold clockPre
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- [helper] The tick before the gate writes no FG field. -/
theorem clockPre_fg (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fg = st.fg := (clockPre_fields p st t).1
/-- [helper] The tick before the gate writes no saved result. -/
theorem clockPre_genuine (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.genuine = st.base.genuine := (clockPre_fields p st t).2.2.2.2.1
/-- [helper] The tick before the gate does not write `fastWrite`. -/
theorem clockPre_fastWrite (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).fastWrite = st.fastWrite := (clockPre_fields p st t).2.2.2.2.2

/-- [helper] The tick writes no FG field. -/
theorem clock_fg (p : Params) (st : State p.n) (t : Time) : (clock p st t).fg = st.fg := by
  unfold clock
  dsimp only
  split
  · rw [gateStep_fg, clockPre_fg]
  · exact clockPre_fg p st t
/-- [helper] The tick keeps the cumulative block list. -/
theorem clock_base_blocks (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.blocks = st.base.blocks := by
  unfold clock
  dsimp only
  split
  · rw [gateStep_base_blocks]; exact (clockPre_fields p st t).2.1
  · exact (clockPre_fields p st t).2.1
/-- [helper] The tick writes no proposal wire. -/
theorem clock_proposals (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  unfold clock
  dsimp only
  split
  · rw [gateStep_proposals]; exact (clockPre_fields p st t).2.2.1
  · exact (clockPre_fields p st t).2.2.1
/-- [helper] The tick writes no row. -/
theorem clock_rowPool (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).rowPool = st.rowPool := by
  unfold clock
  dsimp only
  split
  · rw [gateStep_rowPool]; exact (clockPre_fields p st t).2.2.2.1
  · exact (clockPre_fields p st t).2.2.2.1

end AvailableChain.FGSA
end
