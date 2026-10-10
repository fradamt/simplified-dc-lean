module
public import AvailableChainFGSAProofs.Proofs.Outage.GateCount
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceSleep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
open scoped Classical in
private theorem outage_joinedHonest_unfold (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (t : Time) :
    joinedHonest p E rho t = rho.honest.filter
      (fun v => joinedAt p E rho v (slotAt p t) t) := rfl

/-- The good seats are exactly the joined honest voters outside W at this
label. The linked duty gives their exact cardinality. -/
theorem outage_good_seats (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (fast : Bool) (b₀ : Time) (r s : Slot) :
    ∃ H : Finset (Fin p.n),
      (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈
        outageH p E rho s \ outageW p E rho fast b₀ r) ∧
      H.card = (outageH p E rho s \ outageW p E rho fast b₀ r).card := by
  classical
  let good := outageH p E rho s \ outageW p E rho fast b₀ r
  let seat : Fin p.n → V := rho.seatOf (.base (.head s))
  let H : Finset (Fin p.n) := Finset.univ.filter (fun k => seat k ∈ good)
  have hH : ∀ k, k ∈ H ↔ seat k ∈ good := by
    intro k
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective seat := hC (.base (.head s)) trivial
  have himage : H.image seat = good := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact (hH k).mp hk
    · intro hy
      obtain ⟨k, rfl⟩ := hbij.surjective y
      exact Finset.mem_image.mpr ⟨k, (hH k).mpr hy, rfl⟩
  refine ⟨H, hH, ?_⟩
  change H.card = good.card
  rw [← himage, Finset.card_image_of_injective _ hbij.injective]

/-- Every stored honest HEAD was emitted by a joined voter. Thus a late
seat outside the good set maps into A union W, even at a restarted receiver.
No awake-all-receivers or global monotonicity premise is used. -/
theorem outage_late_opponent_bound [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (s : Slot) (fast : Bool) (b₀ : Time) (r : Slot)
    (H : Finset (Fin p.n))
    (hH : ∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈
      outageH p E rho s \ outageW p E rho fast b₀ r) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card := by
  classical
  intro v
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    by_cases hh : rho.seatOf (.base (.head s)) k ∈ rho.honest
    · apply Finset.mem_union_right
      by_contra hw
      apply hn ((hH k).mpr (Finset.mem_sdiff.mpr ⟨?_, hw⟩))
      obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
      have hlabel : GridCO.headLabel? o = some s :=
        beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
      have hm : o ∈ (storeAt p c E rho i x).base.votes := by
        have hm := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
        change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
        rw [(Internal.clockPre_vn _ _).1] at hm
        exact hm
      have hJ := fgsa_stored_honest_head_joined E rho hE i x s k o hm hlabel hs hh
      have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
        slotOf_offset p s p.Δ p.deltaPos.le
          (by have hd := p.deltaPos; dsimp [Time] at *; omega)
      change rho.seatOf (.base (.head s)) k ∈ joinedHonest p E rho _
      simp only [outage_joinedHonest_unfold E rho, hslot, Finset.mem_filter]
      exact ⟨hh, hJ⟩
    · apply Finset.mem_union_left
      rw [Gen.V2.Duty.faulty_def]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

/-- E gives the exact good-seat majority and opponent bound for each
protected label. It applies to every receiver store, including W. Receipt
membership and compatible targets are separate joint-invariant obligations. -/
theorem outage_good_batch_of_e [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hBase : Base₂ p c E rho)
    {fast : Bool} {b₀ b₁ : Time} (hE : OutageE p E rho fast b₀ b₁) :
    ∃ r, FirstRestored p b₁ r ∧ ∀ s, r ≤ s → s ≤ r + p.k + 1 →
      ∃ H : Finset (Fin p.n),
        (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈
          outageH p E rho s \ outageW p E rho fast b₀ r) ∧
        (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card < H.card ∧
        ∀ i x, let v := actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))
          ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
            (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card := by
  obtain ⟨r, hr, hCount⟩ := hE
  refine ⟨r, hr, ?_⟩
  intro s hrs hsr
  obtain ⟨H, hH, hCard⟩ := outage_good_seats E rho hBase.cstar fast b₀ r s
  refine ⟨H, hH, hCard.symm ▸ hCount s hrs hsr, ?_⟩
  intro i x
  exact outage_late_opponent_bound E rho hBase.valid hBase.cstar i x s fast b₀ r H hH

/-- Before the first restored label, a good joined voter is covered by G.
This step uses membership in W, not a continuous-awake premise for all honest nodes. -/
theorem outage_good_covered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {fast : Bool} {b₀ : Time} {r s : Slot} {y : V}
    (hy : y ∈ outageH p E rho s \ outageW p E rho fast b₀ r)
    (hb : b₀ ≤ SA.voteTime p.toParams s) (hsr : s ≤ r) :
    y ∈ coveredNodes p E rho fast b₀ := by
  classical
  obtain ⟨hH, hW⟩ := Finset.mem_sdiff.mp hy
  change y ∈ joinedHonest p E rho (SA.voteTime p.toParams s) at hH
  rw [outage_joinedHonest_unfold] at hH
  obtain ⟨hHonest, hJ⟩ := Finset.mem_filter.mp hH
  by_contra hn
  apply hW
  change y ∈ rho.honest.filter _
  exact Finset.mem_filter.mpr ⟨hHonest, hn, s, hb, hsr, hJ.1⟩

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; instantiate the compatible-batch
count at the actual pre-gate active view. The sleep caller bounds the
complement by A union W. Authenticity gives resolved targets. Receipts stay explicit. -/
theorem outageV_gate_of_receipts {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (B C : Block) (H : Finset (Fin p.n))
    (a : Nat) (hpart : a < H.card)
    (hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s)).toFinset
        \ H).card ≤ a)
    (hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
        (ofHead p ⟨.seat (.head s) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      K ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      K.slot ≤ s ∧
      GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine s ∧
      GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        K < GridCO.earlyTime p.toParams.engine s ∧ Block.Compatible K B)
    (hresult : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s = some C) :
    Block.Compatible C B := by
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  let v := actView pre
  have hstore : CStoreInv p pre := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _
  have hd : pre.base.headDomain = none := by
    rw [clockPre_headDomain]
    exact base_headDomain_none p (reachable_stateBefore E rho i x)
  have hraw : GridCO.cleanSupport p.toParams.engine v s ⊆ GridCO.lateVotes p.toParams.engine v s :=
    fun _ ho => fgsa_early_subset_late p v s (List.mem_filter.mp ho).1
  apply outageV_gate_of_compatible_batch p.toParams.engine v (eraseFG pre.fg.F) B C s H
    a ?_ hraw hrest hpart
    (fun k _ => fgsa_cleanSupport_no_equivocation p v s k) ?_ hresult
  · intro k hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _⟩ := hheads k hk
    have hsupp := fgsa_active_support_of_receipt E rho hE i x s k K K t
      hh he hv hK hslot hvs hbs (Gen.Pure.block_preceq_refl K)
    obtain ⟨o, ho, hseat, _⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k K).mp hsupp
    exact (Gen.AC.Root.vote_pool_mem_seats _ k).mpr ⟨o, hraw ho, hseat⟩
  · intro o ho k hk hseat X hX
    obtain ⟨K, t, hh, he, _, hK, _, _, _, hKB⟩ := hheads k hk
    have hl : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have hm := (List.mem_filter.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).1).1
      change o ∈ pre.base.votes at hm
      rw [(Internal.clockPre_vn _ _).1] at hm
      exact hm
    have heq := fgsa_honest_head_eq_of_stored E rho hE i x s k K.root t hh he o hm hl hseat
    rw [heq] at hX
    have hresolve : Gen.AC.Root.resolvedTarget? (GridCO.resolutionTree v)
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) = some K := by
      rw [actView_resolutionTree]
      change Gen.AC.Root.resolvedTarget? (pre.base.headDomain.getD pre.base.blocks) _ = _
      rw [hd]
      exact resolvedTarget_of_mem _ (baseBlocks_rootInj p pre hstore) _
        (List.mem_filter.mp hK).1 rfl
    have hXK : X = K := Option.some.inj (hX.symm.trans hresolve)
    exact hXK.symm ▸ hKB

/-- A write can only add one of its supplied targets. Old rows can remain
incompatible; this lemma promises compatibility only for new rows. -/
theorem outage_writeKeys_new_compatible {n : Nat} (keys : List (Block × Nat))
    (lim : Time) (st : GridCO.State n .root) (B : Block)
    (hkeys : ∀ key ∈ keys, Block.Compatible key.1 B) :
    ∀ row ∈ (GridCO.writeKeys st keys lim).obligations,
      row ∈ st.obligations ∨ Block.Compatible row.1 B := by
  induction keys generalizing st with
  | nil => exact fun row hr => Or.inl hr
  | cons key keys ih =>
    intro row hr
    rw [@GridCO.writeKeys_def GridCO.slowLeasePolicy, List.foldl_cons,
      ← @GridCO.writeKeys_def GridCO.slowLeasePolicy] at hr
    rcases ih (GridCO.writeObligation st key.1 key.2 lim)
      (fun k hk => hkeys k (List.mem_cons_of_mem _ hk)) row hr with hrow | hc
    · change row ∈ st.obligations.filter _ ++ [_] at hrow
      rcases List.mem_append.mp hrow with hold | hnew
      · exact Or.inl (List.mem_filter.mp hold).1
      · have he := List.mem_singleton.mp hnew
        rw [he]
        exact Or.inr (hkeys key (List.mem_cons_self ..))
    · exact Or.inr hc

/-- Every new gate lock is compatible when the passed result is compatible.
This local late-write step applies to every receiver store, including W;
the joint proof must still supply result compatibility at every actual gate. -/
theorem outage_gate_writeKeys_compatible {n : Nat} (params : GridCO.Params)
    (st : GridCO.State n .root) (s : Slot) (C B : Block) (lim : Time)
    (hCB : Block.Compatible C B) :
    ∀ row ∈ (GridCO.writeKeys st (GridCO.gateWriteKeys params st s C) lim).obligations,
      row ∈ st.obligations ∨ Block.Compatible row.1 B := by
  apply outage_writeKeys_new_compatible
  intro key hk
  rw [GridCO.gateWriteKeys_def] at hk
  obtain ⟨X, hX, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨g, _, he⟩ := List.mem_map.mp hk
  subst key
  have hXC := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hX).2).2
  exact Gen.Pure.block_compatible_of_preceq_compatible hXC hCB

end AvailableChain.FGSA.Run
end
