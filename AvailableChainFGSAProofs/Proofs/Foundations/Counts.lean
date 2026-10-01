module
public import AvailableChainFGSA.Model.Objects
public import AvailableChainKitFG.Certificates

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure SimplexFG

/-- P3 D40: the claim-local `a ≤ f` is `a ≤ (p.n - 1) / 3`.
The sole FaultX producer is Gen.Pure.count_rec. -/
theorem fgsa_faultX_count_rec (p : Params) {a : Nat} (hf : a ≤ (p.n - 1) / 3) :
    FaultX p.n a := count_rec p.nPos hf

/-- Recovery quorum membership from count_rec. Gen has no FaultX-to-FaultQ lemma;
only the projection arithmetic is local. This is not a Clean producer. -/
theorem fgsa_faultQ_of_count (p : Params) {a : Nat} (hf : a ≤ (p.n - 1) / 3) :
    FaultQ p.n a := by
  have hx := (fgsa_faultX_count_rec p hf).lt
  constructor
  rw [qF_def] at hx ⊢
  omega

private theorem fgsa_target_fold_covered (p : Params) (rows : List (Row (Fin p.n)))
    (σ : ChainState (Fin p.n)) (i : Fin p.n)
    (hi : i ∈ σ.target_participation ∨ ∃ r ∈ rows, r.signer = i ∧
      r.height_pair = .vote σ.h σ.T_h.root false) :
    i ∈ (rows.foldl process_row σ).target_participation := by
  induction rows generalizing σ with
  | nil =>
    rcases hi with hi | ⟨r, hr, _⟩
    · exact hi
    · cases hr
  | cons r rows ih =>
    apply ih
    have fields := KitFG.process_row_fields σ r
    rcases hi with hi | ⟨a, ha, hs, hp⟩
    · left
      rw [KitFG.process_row_target]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi
    · rcases List.mem_cons.mp ha with rfl | ha
      · left
        rw [KitFG.process_row_target, ite_eq_left hp, hs]
        exact Finset.mem_insert_self _ _
      · right
        exact ⟨a, ha, hs, by rw [fields.2.2.1, fields.2.2.2.1]; exact hp⟩

/-- 22 I7, target part: exact rows or existing bits for at least `n - a`
identities justify the parent's entry and advance once. The FG chain state has
no `nj` field; the target test is unconditional. No restriction on δt. -/
theorem fgsa_target_exact_quorum (p : Params) {a : Nat}
    (hf : a ≤ (p.n - 1) / 3) (H : Finset (Fin p.n)) (hH : p.n - a ≤ H.card)
    (B : FGBlock (Fin p.n)) (s : Slot) (x : Nat) (rows : List (Row (Fin p.n)))
    (hcov : ∀ i ∈ H, i ∈ (derive p.E p.cfg B).target_participation ∨
      ∃ r ∈ rows, r.signer = i ∧
        r.height_pair = .vote (derive p.E p.cfg B).h (derive p.E p.cfg B).T_h.root false) :
    (derive p.E p.cfg (.node B s x rows)).J = (derive p.E p.cfg B).T_h ∧
    (derive p.E p.cfg (.node B s x rows)).h_j = (derive p.E p.cfg B).h ∧
    (derive p.E p.cfg (.node B s x rows)).h = (derive p.E p.cfg B).h + 1 := by
  let σ := KitFG.foldRows (derive p.E p.cfg B) (.node B s x rows) rows
  have hsub : H ⊆ σ.target_participation := by
    intro i hi
    exact fgsa_target_fold_covered p rows
      { derive p.E p.cfg B with s := (FGBlock.node B s x rows).slot } i (hcov i hi)
  have hcard := Finset.card_le_card hsub
  have hq : p.E.q = qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  have hw : p.E.weightOf σ.target_participation = σ.target_participation.card := by
    change (∑ _i ∈ σ.target_participation, (1 : Nat)) = σ.target_participation.card
    simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
  have hn := p.nPos
  have hbound : qF p.n ≤ p.n - a := by
    rw [qF_def]
    omega
  have htarget : (KitFG.afterFin p.E σ).targetQuorum p.E = true := by
    change decide (p.E.q ≤ p.E.weightOf (KitFG.afterFin p.E σ).target_participation) = true
    rw [KitFG.afterFin_target_participation, hq, hw]
    exact decide_eq_true (hbound.trans (hH.trans hcard))
  have fields := KitFG.foldRows_fields (derive p.E p.cfg B) (.node B s x rows) rows
  rw [KitFG.derive_node]
  change (process_height_events p.E p.cfg σ).J = _ ∧
    (process_height_events p.E p.cfg σ).h_j = _ ∧
    (process_height_events p.E p.cfg σ).h = _
  rw [KitFG.process_height_events_eq, ite_eq_left htarget]
  exact ⟨(KitFG.afterFin_T_h p.E σ).trans fields.2.2.1,
    (KitFG.afterFin_h p.E σ).trans fields.2.1,
    congrArg (· + 1) ((KitFG.afterFin_h p.E σ).trans fields.2.1)⟩

end AvailableChain.FGSA.Run
end
