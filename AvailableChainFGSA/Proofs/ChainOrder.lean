module
public import AvailableChainSimplexFG.ChainState
public import Mathlib.Data.List.Dedup

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-! The chain-state fold is order-free (T7.W extra item). `process_row` only
inserts the signer into `finalize`, `target_participation` and `progress`; its
tests read `h_F`, `h_j`, `J.root`, `h` and `T_h.root`, which the fold does not
write. So the fold commutes and is idempotent, and `transition` depends only on
the set of rows. -/

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- [helper; T7.W] Insert `i` into `S` when `c` holds. -/
def insertIf (c : Bool) (i : V) (S : Finset V) : Finset V := if c then insert i S else S

omit [RowCodec V] in
/-- [helper] Two conditional inserts commute. -/
theorem insertIf_comm (c d : Bool) (i j : V) (S : Finset V) :
    insertIf c i (insertIf d j S) = insertIf d j (insertIf c i S) := by
  cases c <;> cases d <;> simp [insertIf, Finset.insert_comm]

omit [RowCodec V] in
/-- [helper] A conditional insert is idempotent. -/
theorem insertIf_idem (c : Bool) (i : V) (S : Finset V) :
    insertIf c i (insertIf c i S) = insertIf c i S := by
  cases c <;> simp [insertIf]

/-- [helper; T7.W] The finality test of `process_row`. It reads `h_F`, `h_j`
and `J`. -/
def finHit (σ : ChainState V) (row : Row V) : Bool :=
  decide (σ.h_F < σ.h_j) && decide (row.finality_pair = some ⟨σ.h_j, σ.J.root⟩)

/-- [helper; T7.W] The progress test of `process_row`. It reads `h` and `T_h`. -/
def progHit (σ : ChainState V) (row : Row V) : Bool :=
  row.height_pair.matchesEntry σ.h σ.T_h.root

/-- [helper; T7.W] The target test of `process_row`: the progress test and not a
timeout. -/
def targetHit (σ : ChainState V) (row : Row V) : Bool :=
  progHit σ row && match row.height_pair with
    | .vote _ _ timeout => !timeout
    | .empty => false

/-- [helper; T7.W] The normal form of a row step: three conditional inserts. The
tests read only fields that the step does not write. -/
theorem process_row_eq (σ : ChainState V) (row : Row V) :
    process_row σ row = { σ with
      finalize := insertIf (finHit σ row) row.signer σ.finalize
      target_participation := insertIf (targetHit σ row) row.signer σ.target_participation
      progress := insertIf (progHit σ row) row.signer σ.progress } := by
  rcases row with ⟨i, hp, fp⟩
  cases σ
  unfold process_row finHit targetHit progHit insertIf
  cases hp with
  | empty =>
      simp only [NamedHeightPair.matchesEntry]
      split_ifs <;> simp_all
  | vote h e t =>
      simp only [NamedHeightPair.matchesEntry]
      cases t <;> split_ifs <;> simp_all

/-- [T7.W] Two row steps commute. -/
theorem process_row_comm (σ : ChainState V) (a b : Row V) :
    process_row (process_row σ a) b = process_row (process_row σ b) a := by
  simp only [process_row_eq]
  congr 1 <;> exact insertIf_comm _ _ _ _ _

/-- [T7.W] A row step is idempotent. -/
theorem process_row_idem (σ : ChainState V) (a : Row V) :
    process_row (process_row σ a) a = process_row σ a := by
  simp only [process_row_eq]
  congr 1 <;> exact insertIf_idem _ _ _

/-- [helper] The row fold with a row moved to the end. -/
theorem foldl_process_row_push (σ : ChainState V) (a : Row V) (l : List (Row V)) :
    l.foldl process_row (process_row σ a) = process_row (l.foldl process_row σ) a := by
  induction l generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [process_row_comm σ a x, ih]

/-- [helper] A row that is in the list has no further effect on the fold. -/
theorem foldl_process_row_absorb (σ : ChainState V) {a : Row V} {l : List (Row V)}
    (ha : a ∈ l) : process_row (l.foldl process_row σ) a = l.foldl process_row σ := by
  induction l generalizing σ with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 ha with rfl | hm
      · rw [foldl_process_row_push, process_row_idem]
      · exact ih _ hm

/-- [helper] The row fold equals the fold over the list without duplicates. -/
theorem foldl_process_row_dedup (σ : ChainState V) (l : List (Row V)) :
    l.foldl process_row σ = l.dedup.foldl process_row σ := by
  induction l generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x ∈ xs
      · rw [List.dedup_cons_of_mem hx, List.foldl_cons, foldl_process_row_push,
          foldl_process_row_absorb σ hx, ih]
      · rw [List.dedup_cons_of_notMem hx, List.foldl_cons, List.foldl_cons, ih]

/-- [helper] The row fold does not depend on the order of the rows. -/
theorem foldl_process_row_perm (σ : ChainState V) {rs rs' : List (Row V)} (h : rs.Perm rs') :
    rs.foldl process_row σ = rs'.foldl process_row σ :=
  h.foldl_eq' (fun x _ y _ z => process_row_comm z x y) σ

variable [Fintype V]

/-- [T7.W] `transition` does not depend on the order of the rows. -/
theorem transition_perm (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (g : FGBlock V) {rs rs' : List (Row V)} (h : rs.Perm rs') :
    transition E cfg σ g rs = transition E cfg σ g rs' := by
  unfold transition
  rw [foldl_process_row_perm _ h]

/-- [T7.W] `transition` depends only on the members of the row list (no order,
no multiplicity). -/
theorem transition_eq_of_mem_iff (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (g : FGBlock V) {rs rs' : List (Row V)} (h : ∀ x, x ∈ rs ↔ x ∈ rs') :
    transition E cfg σ g rs = transition E cfg σ g rs' := by
  have hp : rs.dedup.Perm rs'.dedup :=
    (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2
      (fun x => by rw [List.mem_dedup, List.mem_dedup, h])
  unfold transition
  rw [foldl_process_row_dedup _ rs, foldl_process_row_dedup _ rs',
    foldl_process_row_perm _ hp]

/-- [T7.W] `transition` depends only on the row set. -/
theorem transition_eq_of_toFinset (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (g : FGBlock V) {rs rs' : List (Row V)} (h : rs.toFinset = rs'.toFinset) :
    transition E cfg σ g rs = transition E cfg σ g rs' :=
  transition_eq_of_mem_iff E cfg σ g (fun x => by
    rw [← List.mem_toFinset, h, List.mem_toFinset])

end AvailableChain.FGSA
end
