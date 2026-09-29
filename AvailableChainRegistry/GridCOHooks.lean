module
public import AvailableChainFramework
public import AvailableChainGridCO.Proofs.ClockBounds
public import AvailableChainKit.Engine.Stable

@[expose] public section

namespace AvailableChain.Registry.GridCO

open AvailableChain AvailableChain.Generic AvailableChain.Framework AvailableChain.GridCO
open AvailableChain.Statements.Generic
open AvailableChain.Engine (stateBefore_stable)

/-- Permanent rejection (design E4): a HEAD for label `r` after slot `r+1`
(the clock only goes forward), or a new HEAD from a seat that already
equivocates at `r`. Both make `admitVote` return the state unchanged. -/
def gridExcludes (p : Params) {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      decide (r + 1 < (st.now / (4 * p.Δ)).toNat) ||
        (!decide (o ∈ st.votes) && equivocates (votesAt st r) i)
  | _, _ => false

/-- Grid CO with the E4 `excludes`. Every other field is `gridCO`'s. -/
def gridCOx [LeasePolicy] (p : Params) : ProtocolSpec p.n :=
  { gridCO p with excludes := gridExcludes p }

-- Keep the brief's statements, which carry the policy instance.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

theorem gridExcludes_inert (p : Params) (st : State p.n) (o : Wire p.n)
    (h : gridExcludes p st o = true) : process p st o = st := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | seat r i =>
      cases payload with
      | head x =>
          simp only [gridExcludes, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_false_iff_not] at h
          simp only [process, admitVote]
          rw [if_pos]
          rcases h with h | ⟨_, h⟩
          · simp only [Bool.or_eq_true, decide_eq_true_eq]
            exact Or.inl (Or.inl (Or.inl (Nat.lt_sub_of_add_lt h)))
          · simp [h]
      | proposal b raw support => simp [gridExcludes] at h
  | proposer s => cases payload <;> simp [gridExcludes] at h
  | none => cases payload <;> simp [gridExcludes] at h

private theorem foldl_votes {n : Nat} {α : Type}
    (f : State n → α → State n) (xs : List α) (st : State n)
    (hf : ∀ acc x, (f acc x).votes = acc.votes) :
    (xs.foldl f st).votes = st.votes := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, hf]

theorem gate_votes (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).votes = st.votes := by
  cases hc : confirmation p st r with
  | none => simp [gate, hc]
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simp [gate, hc, hguard]
      | false =>
          simp only [gate, hc, hguard]
          apply foldl_votes
          intro acc b
          apply foldl_votes
          intro acc g
          rfl

/-- Step 1 finding: no clock evaluation (`expire`, `freeze`, the early save,
`release`, `gate`) changes the stored HEADs. -/
theorem clock_votes (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).votes = st.votes := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
    gate p s3 dSlot else s3).votes = st.votes
  have h0 : s0.votes = st.votes := rfl
  have h1 : s1.votes = s0.votes := by
    dsimp [s1]
    split <;> rfl
  have h2 : s2.votes = s1.votes := by
    dsimp [s2]
    split <;> rfl
  have h3 : s3.votes = s2.votes := by
    dsimp [s3]
    split <;> rfl
  split
  · exact (gate_votes p s3 dSlot).trans (h3.trans (h2.trans (h1.trans h0)))
  · exact h3.trans (h2.trans (h1.trans h0))

private theorem votesAt_subset {n : Nat} (a b : State n) (r : Slot)
    (hsub : a.votes ⊆ b.votes) : votesAt a r ⊆ votesAt b r := by
  intro o ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  exact List.mem_filter.mpr ⟨hsub hm, hl⟩

/-- An absent HEAD whose seat equivocates stays absent, and the seat
stays equivocating, after one HEAD call. -/
private theorem admitVote_keeps_refusal (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (x : Block) (o : Wire n)
    (hm : (⟨.seat r i, .head x⟩ : Wire n) ∉ st.votes)
    (he : equivocates (votesAt st r) i = true) :
    (⟨.seat r i, .head x⟩ : Wire n) ∉ (admitVote p st o).votes ∧
      equivocates (votesAt (admitVote p st o) r) i = true := by
  refine ⟨?_, equivocates_mono _ _ i
    (votesAt_subset _ _ r (admitVote_votes_subset p st o)) he⟩
  unfold admitVote
  split
  · rename_i r' i' x' hauth hpay
    dsimp only
    split
    · exact hm
    · rename_i hguard
      simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨hm, fun heq => hguard ?_⟩
      have ho : o = ⟨.seat r i, .head x⟩ := heq.symm
      subst ho
      simp only [Auth.seat.injEq, Msg.head.injEq] at hauth hpay
      obtain ⟨rfl, rfl⟩ := hauth
      simp [he]
  · exact hm

private theorem fold_keeps_refusal (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) (r : Slot) (i : Fin n) (x : Block)
    (hm : (⟨.seat r i, .head x⟩ : Wire n) ∉ st.votes)
    (he : equivocates (votesAt st r) i = true) :
    let post := raw.foldl (fun acc row => admitVote p acc (fromHead row)) st
    (⟨.seat r i, .head x⟩ : Wire n) ∉ post.votes ∧
      equivocates (votesAt post r) i = true := by
  induction raw generalizing st with
  | nil => exact ⟨hm, he⟩
  | cons row raw ih =>
      obtain ⟨hm', he'⟩ := admitVote_keeps_refusal p st r i x (fromHead row) hm he
      exact ih _ hm' he'

private theorem process_keeps_refusal (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (x : Block) (o : Wire n)
    (hm : (⟨.seat r i, .head x⟩ : Wire n) ∉ st.votes)
    (he : equivocates (votesAt st r) i = true) :
    (⟨.seat r i, .head x⟩ : Wire n) ∉ (process p st o).votes ∧
      equivocates (votesAt (process p st o) r) i = true := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact ⟨hm, he⟩
    | exact admitVote_keeps_refusal p st r i x _ hm he
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact ⟨hm, he⟩
  · exact fold_keeps_refusal p raw _ r i x hm he

private theorem fold_votes_subset (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) : st.votes ⊆
      (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).votes := by
  induction raw generalizing st with
  | nil => exact List.Subset.refl _
  | cons row raw ih => exact (admitVote_votes_subset p st (fromHead row)).trans (ih _)

private theorem process_votes_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.votes ⊆ (process p st o).votes := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact List.Subset.refl _
    | exact admitVote_votes_subset p st _
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact List.Subset.refl _
  · refine List.Subset.trans ?_ (fold_votes_subset p raw _)
    exact List.Subset.refl _

private theorem fold_blocks {n : Nat} (p : Params) (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simp only [List.foldl_cons]
      rw [ih, admitVote_blocks]

private theorem process_blocks_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.blocks ⊆ (process p st o).blocks := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact List.Subset.refl _
    | exact (admitVote_blocks p st _).symm ▸ List.Subset.refl _
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact List.Subset.refl _
  · rw [fold_blocks]
    exact List.subset_append_left _ _

/-- `gridCOx` has the clock laws of `gridCO`. -/
def engineClockx (p : Params) : AvailableChain.Engine.ClockLaws (gridCOx p) where
  now := State.now
  init := rfl
  clock := clock_now p
  process := process_now p

theorem gridCOx_hooks (p : Params) : HooksSound (gridCOx p) where
  excludes_inert := gridExcludes_inert p
  excludes_stable := by
    intro V _ _ E rho hs v o i j hij h
    obtain ⟨auth, payload⟩ := o
    cases auth with
    | seat r s =>
        cases payload with
        | head x =>
            dsimp only [gridCOx] at h ⊢
            simp only [gridExcludes, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
              Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
            rcases h with h | h
            · left
              have hnow := AvailableChain.Engine.stateBefore_now_mono
                (engineClockx p) E rho hs hij v
              have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
              have hdiv := Int.ediv_le_ediv hd hnow
              have htn := Int.toNat_le_toNat hdiv
              exact lt_of_lt_of_le h htn
            · right
              exact stateBefore_stable (P := gridCOx p)
                (fun st => (⟨.seat r s, .head x⟩ : Wire p.n) ∉ st.votes ∧
                  equivocates (votesAt st r) s = true)
                (fun st t hq => by
                  change _ ∉ (clock p st t).votes ∧ equivocates (votesAt (clock p st t) r) s = true
                  rw [show votesAt (clock p st t) r = votesAt st r by
                    simp only [votesAt, clock_votes], clock_votes]
                  exact hq)
                (fun st o hq => process_keeps_refusal p st r s x o hq.1 hq.2)
                rho hij v h
        | proposal b raw support => simp [gridCOx, gridExcludes] at h
    | proposer s => cases payload <;> simp [gridCOx, gridExcludes] at h
    | none => cases payload <;> simp [gridCOx, gridExcludes] at h
  processed_stable := by
    intro V _ _ E rho _ v o i j hij h
    exact stateBefore_stable (P := gridCOx p) (fun st => processed st o = true)
      (fun st t hq => by
        change processed (clock p st t) o = true
        obtain ⟨auth, payload⟩ := o
        cases payload with
        | head x =>
            simpa [processed, clock_votes] using hq
        | proposal b raw support =>
            simpa [processed, blockKnown, clock_blocks] using hq)
      (fun st o' hq => by
        change processed (process p st o') o = true
        obtain ⟨auth, payload⟩ := o
        cases payload with
        | head x =>
            simp only [processed, decide_eq_true_eq] at hq ⊢
            exact process_votes_subset p st o' hq
        | proposal b raw support =>
            simp only [processed, blockKnown, decide_eq_true_eq] at hq ⊢
            exact process_blocks_subset p st o' hq)
      rho hij v h
  deps_stable := by
    intro V _ _ E rho _ v o i j hij h
    exact stateBefore_stable (P := gridCOx p) (fun st => depsPresent st o = true)
      (fun st t hq => by
        change depsPresent (clock p st t) o = true
        obtain ⟨auth, payload⟩ := o
        cases payload with
        | head x => rfl
        | proposal b raw support =>
            simpa [depsPresent, blockKnown, clock_blocks] using hq)
      (fun st o' hq => by
        change depsPresent (process p st o') o = true
        obtain ⟨auth, payload⟩ := o
        cases payload with
        | head x => rfl
        | proposal b raw support =>
            simp only [depsPresent, blockKnown, decide_eq_true_eq] at hq ⊢
            exact process_blocks_subset p st o' hq)
      rho hij v h
  handles_carries := by
    intro st o o' h
    change handles p st o o' at h
    change o = o' ∨ carries o o'
    rcases h with h | h
    · exact Or.inl h
    · right
      unfold carries
      cases hp : o.payload with
      | head x => simp [hp] at h
      | proposal b raw support =>
          simp only [hp] at h
          exact Or.inl h.2.2

/-- Review Focus 3: an in-window, new, non-equivocating HEAD is not excluded. -/
theorem inWindow_not_excluded (p : Params) (st : State p.n) (r : Slot)
    (i : Fin p.n) (x) (hr : (st.now / (4 * p.Δ)).toNat ≤ r + 1)
    (heq : equivocates (votesAt st r) i = false) :
    gridExcludes p st ⟨.seat r i, .head x⟩ = false := by
  simp [gridExcludes, heq, Nat.not_lt.mpr hr]

end AvailableChain.Registry.GridCO

end
