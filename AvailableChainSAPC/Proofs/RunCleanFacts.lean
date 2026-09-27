module
public import AvailableChainSAPC.Proofs.RunCleanTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A capped source path is available at an actual honest input in its
own event prefix. Stored unrelated proposals do not supply this source. -/
theorem cleanRunPath_accessible_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) (index : Nat) (b : Block)
    (hb : cleanRunPath p rho index b) : b = .genesis ∨
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true := by
  by_cases hg : b = .genesis
  · exact Or.inl hg
  right
  have stored (v : V) (hv : v ∈ rho.honest) (i : Nat) (hi : i ≤ index)
      (c : Block) (hc : c ∈ (Run.stateBefore (sapc p) rho i v).base.blocks)
      (hp : Block.Preceq b c) :
      ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
        pathKnown (Run.stateBefore (sapc p) rho i v) b = true := by
    exact ⟨v, hv, i, hi, stored_pathKnown_at_fold p (rho.events.take i) v b
      ((paths_at_fold p _ v).1 c hc b hg hp)⟩
  rcases (cleanRunPath_capped_sources p E rho hx cap index b).mp hb with
    hgen | ⟨j, hj, v, hv, r, c, ht, hc, hp⟩ | ⟨r, c, source, hp⟩
  · exact (hg hgen).elim
  · rcases @GridCO.confirmation_mem GridCO.slowLeasePolicy p.engine p.n _ r c hc
      with hgen | hm
    · subst c
      exact (hg (by simpa [Block.Preceq, Block.preceq] using hp)).elim
    · exact stored v hv j (by omega) c hm hp
  · obtain ⟨v, hv, j, hj, _, saved⟩ := source
    obtain ⟨k, hk, _, candidate⟩ := savedTimely_origin_before p rho (j + 1) v r c saved
    have candidate := timelyCandidate_of_timelyInput p _
      (base_receiptStamped_at_fold p _ v) (archiveStamped_at_fold p _ v) r c _ candidate
    have path := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp candidate).1).2
    have mem : c ∈ (Run.stateBefore (sapc p) rho k v).base.blocks := by
      cases c with
      | genesis => exact of_decide_eq_true (Bool.and_eq_true_iff.mp path).1
      | node parent slot root =>
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp path).1).1
    exact stored v hv k (by omega) c mem hp

/-- Source and receipt facts are independent of clean comparability.
Only the chain and actual genuine continuation need induction. -/
theorem cleanPathFacts_capped_of_chain_and_transfer
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) (index : Nat)
    (chain : CleanPath (cleanRunPath p rho index))
    (transfer : ∀ j, j < index → ∀ v ∈ rho.honest, ∀ r b,
      rho.events[j]? = some (.tick v (gateTime p r)) →
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b →
      ∀ k, k < index → ∀ w ∈ rho.honest, ∀ s, r < s →
        rho.events[k]? = some (.tick w (voteTime p s)) →
        Block.Preceq b (headTarget p
          (clock p (Run.stateBefore (sapc p) rho k w) (voteTime p s)) s)) :
    CleanPathFacts p E rho index (cleanRunPath p rho index) := by
  refine ⟨chain, ?_, cleanRunPath_accessible_capped p E rho hx cap index,
    ?_, ?_, transfer, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi v hv
    have h := state_on_cleanRunPath p rho i v hv
    exact ⟨cleanRunPath_mono p rho hi h.stable, cleanRunPath_mono p rho hi h.goldfish,
      fun b g d hm => cleanRunPath_mono p rho hi (h.finite b g d hm),
      fun r b hm => cleanRunPath_mono p rho hi (h.saved r b hm)⟩
  · intro v _ b g d hm
    exact run_target_genuine_origin p rho index v b g d hm
  · intro j hj v hv r b ht raw
    exact Or.inr ⟨b, .genuine j hj v hv r b ht raw, GridCO.block_preceq_self b⟩
  · intro i hi v _ c hc
    obtain ⟨w, hw, j, hj, ht, saved⟩ := validPC_prior_timely p E rho hx
      (capped_quorum_above_faults p rho cap) i v c hc
    exact ⟨⟨w, hw, j, by omega, ht, saved⟩, fun _ =>
      cleanRunPath_mono p rho hi (validPC_on_cleanRunPath p E rho hx cap i v c hc)⟩
  · intro i hi v hv r b saved
    obtain ⟨j, hj, ht, saved⟩ := savedTimely_first_save p E rho hx.toScheduleWellFormed
      i v r b saved
    exact ⟨⟨v, hv, j, hj, ht, saved⟩, fun _ => Or.inr ⟨b,
      .timely r b cap ⟨v, hv, j, hj.trans_le hi, ht, saved⟩, GridCO.block_preceq_self b⟩⟩
  · intro _ i _ v _
    exact capBroken_false_before p E rho hx cap v i
  · intro i _ v _
    exact archive_authenticated_before p E rho hx.toUnforgeableSignatures i v
  · intro i hi v hv r c ht ha hc
    exact Or.inr ⟨c.target, .gate i hi v hv r c ht ha hc, GridCO.block_preceq_self _⟩
  · intro i hi v hv r c ht ha hc
    exact Or.inr ⟨c.target, .head i hi v hv r c ht ha hc, GridCO.block_preceq_self _⟩
  · intro i hi v hv r c ht ha hc
    exact Or.inr ⟨c.target, .proposal i hi v hv r c ht ha hc, GridCO.block_preceq_self _⟩

/-- Restrict the actual invariant to an earlier event prefix. The earlier
path is its own source closure, not the current path reused at that time. -/
theorem JointCleanInvariant.restrict_capped {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {rho : Run V (sapc p)}
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) {i j : Nat} (hle : j ≤ i)
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho j := by
  constructor
  · apply cleanPathFacts_capped_of_chain_and_transfer p E rho hx cap j
    · exact ⟨Or.inl rfl, cleanRunPath_closed p rho j,
        fun a b ha hb => h.facts.chain.comparable a b
          (cleanRunPath_mono p rho hle ha) (cleanRunPath_mono p rho hle hb)⟩
    · intro k hk v hv r b ht raw l hl w hw s hrs tick
      exact h.facts.transferred k (hk.trans_le hle) v hv r b ht raw
        l (hl.trans_le hle) w hw s hrs tick
  · intro k hk l hl
    exact h.ordered k (hk.trans_le hle) l (hl.trans_le hle)

end AvailableChain.SAPC
end
