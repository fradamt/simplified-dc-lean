module
public import AvailableChainFGSA.Model.Frame

public section

namespace AvailableChain.FGSA

/-- Stores differ only by a permutation of the row pool. -/
def StoreSetEq {n : Nat} (st st' : State n) : Prop :=
  st' = { st with rowPool := st'.rowPool } ∧ st.rowPool.Perm st'.rowPool

private theorem pool_step_perm {n : Nat} (xs ys : List (RowWire n))
    (h : xs.Perm ys) (a : RowWire n) :
    (if decide (a ∈ xs) || 2 ≤ (xs.filter (fun x =>
      x.decode?.map (fun y => (y.1, y.2.1)) == a.decode?.map (fun y => (y.1, y.2.1)))).length
      then xs else xs ++ [a]).Perm
    (if decide (a ∈ ys) || 2 ≤ (ys.filter (fun x =>
      x.decode?.map (fun y => (y.1, y.2.1)) == a.decode?.map (fun y => (y.1, y.2.1)))).length
      then ys else ys ++ [a]) := by
  simp only [h.mem_iff, (h.filter _).length_eq]
  split <;> first | exact h | exact h.append_right _

/-- Admission uses only membership, key counts and the common clock. -/
theorem admitRow_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (a : RowWire p.n) :
    StoreSetEq (admitRow p st a) (admitRow p st' a) := by
  obtain ⟨he, hp⟩ := h
  rw [he] at hp ⊢
  unfold admitRow
  cases hd : a.decode? with
  | some val =>
    obtain ⟨r, i, body⟩ := val
    dsimp only
    have hf := hp.filter (fun c => c.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))
    dsimp only at hf
    have hm : decide (a ∈ st.rowPool.filter (fun c =>
        c.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))) =
        decide (a ∈ st'.rowPool.filter (fun c =>
        c.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))) :=
      decide_eq_decide.mpr hf.mem_iff
    rw [hm, hf.length_eq]
    have aux (test : Bool) :
        StoreSetEq (if test then st else { st with rowPool := st.rowPool ++ [a] })
          (if test then { st with rowPool := st'.rowPool }
           else { st with rowPool := st'.rowPool ++ [a] }) := by
      cases test
      · exact ⟨rfl, hp.append_right _⟩
      · exact ⟨rfl, hp⟩
    exact aux _
  | none => exact ⟨rfl, hp⟩

/-- Proposal row selection keeps permutations, including its per-key cap. -/
theorem proposalRows_perm_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (H : Block) :
    (proposalRows p st H).Perm (proposalRows p st' H) := by
  obtain ⟨he, hp⟩ := h
  rw [he] at hp ⊢
  let A := st.rowPool.filter (fun a =>
    (a.round?.map (fun r' => decide (p.round (st.slot p) ≤ r' + p.wF) &&
      decide (r' ≤ p.round (st.slot p)))).getD false && !decide (a ∈ chainWireRows st H))
  let B := st'.rowPool.filter (fun a =>
    (a.round?.map (fun r' => decide (p.round (st.slot p) ≤ r' + p.wF) &&
      decide (r' ≤ p.round (st.slot p)))).getD false && !decide (a ∈ chainWireRows st H))
  have hAB : A.Perm B := hp.filter _
  let step := fun (acc : List (RowWire p.n)) a =>
    if decide (a ∈ acc) || 2 ≤ (acc.filter (fun x =>
      x.decode?.map (fun y => (y.1, y.2.1)) == a.decode?.map (fun y => (y.1, y.2.1)))).length
    then acc else acc ++ [a]
  have fold : ∀ (rest : List (RowWire p.n)) xs ys, xs.Perm ys →
      (rest.foldl step xs).Perm (rest.foldl step ys) := by
    intro rest
    induction rest with
    | nil => exact fun _ _ h => h
    | cons a rest ih => exact fun xs ys h => ih _ _ (pool_step_perm xs ys h a)
  change ((List.filter (fun a => !decide (a ∈ chainWireRows st H) && !decide (a ∈ A))
    (blockWireRows p st (fun r' => decide (p.round (st.slot p) ≤ r' + p.wF) &&
      decide (r' ≤ p.round (st.slot p))))).foldl step A).Perm
    ((List.filter (fun a => !decide (a ∈ chainWireRows st H) && !decide (a ∈ B))
    (blockWireRows p st (fun r' => decide (p.round (st.slot p) ≤ r' + p.wF) &&
      decide (r' ≤ p.round (st.slot p))))).foldl step B)
  simp only [hAB.mem_iff]
  exact fold _ _ _ hAB

/-- Both proposals have the same parent, slot, votes and support; their
row lists are permutations. The packed block identities can differ. -/
theorem propose_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (s : Slot) (hs : s ≠ 0) :
    ∃ H raw sup rows rows', rows.Perm rows' ∧
      propose p st s = some (.proposal (.node H s (packBody 0 rows)) raw sup rows) ∧
      propose p st' s = some (.proposal (.node H s (packBody 0 rows')) raw sup rows') := by
  have hr := proposalRows_perm_setEq p h
  obtain ⟨he, hp⟩ := h
  rw [he] at hr ⊢
  refine ⟨getHead p st (proposerVotes st s) (proposerSupport st s),
    (proposerVotes st s).filterMap liftHead?, (proposerSupport st s).filterMap liftHead?,
    _, _, hr (getHead p st (proposerVotes st s) (proposerSupport st s)), ?_, ?_⟩ <;>
    dsimp only [propose]
  all_goals simp only [hs, ↓reduceIte]
  · rfl

end AvailableChain.FGSA
end
