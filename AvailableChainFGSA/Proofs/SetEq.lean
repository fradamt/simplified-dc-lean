module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Proofs.RowSelection

public section

namespace AvailableChain.FGSA

/-- Stores differ only by a permutation of the row pool. -/
def StoreSetEq {n : Nat} (st st' : State n) : Prop :=
  st' = { st with rowPool := st'.rowPool } ∧ st.rowPool.Perm st'.rowPool

/-- Admission uses only decoding and full-wire membership. -/
theorem admitRow_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (a : RowWire p.n) :
    StoreSetEq (admitRow p st a) (admitRow p st' a) := by
  obtain ⟨he, hp⟩ := h
  rw [he] at hp ⊢
  unfold admitRow
  cases hd : a.decode? with
  | none => exact ⟨rfl, hp⟩
  | some val =>
      simp only [hp.mem_iff]
      split
      · exact ⟨rfl, hp⟩
      · exact ⟨rfl, hp.append_right _⟩

/-- R7 selection preserves permutations of held content. -/
theorem proposalRows_perm_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (H : Block) :
    (proposalRows p st H).Perm (proposalRows p st' H) := by
  obtain ⟨he, hp⟩ := h
  rw [he] at hp ⊢
  change (proposalRowsFor p st (st.slot p) H).Perm
    (proposalRowsFor p { st with rowPool := st'.rowPool } (st.slot p) H)
  exact proposalRowsFor_perm p (st := st) (st' := { st with rowPool := st'.rowPool })
    rfl hp (List.Perm.refl _) _ _

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
