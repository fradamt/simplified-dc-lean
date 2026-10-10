module
public import AvailableChainFGSARun.Proofs.ReceiptCoverage
public import AvailableChainFGSARun.Proofs.RootResolution
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainGeneric.Statements.V2.Duty.Counts

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem count_head_keys (o : GridCO.Wire p.n .root) (s : Slot) (k : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ K, o = ⟨.seat s k, .head K⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> cases hl
  | proposer r => cases payload <;> cases hl
  | seat r j =>
    cases payload with
    | proposal B raw sup => cases hl
    | head K =>
      have hr : r = s := Option.some.inj hl
      have hj : j = k := Option.some.inj hk
      subst r; subst j
      exact ⟨K, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1. Class (ii), receipt/authenticity instance.
DC: Protocol/Handlers/GoldfishVotePool.lean:320 (unique honest vote per label).
Same uniqueness conclusion; FG-SA also permits carried HEAD receipts. -/
theorem fgsa_honest_head_eq_of_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot) (k : Fin p.n)
    (K : BlockId) (t : Time) (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K⟩) t)
    (o : GridCO.Wire p.n .root) (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    o = baseVote (⟨.seat (.head s) k, K⟩ : HeadWire p.n) := by
  obtain ⟨C, rfl⟩ := count_head_keys o s k hl hk
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at ho
  rw [← fgsa_vote_stamp_keys E rho i x] at ho
  obtain ⟨⟨v, stamp⟩, hv, hvEq⟩ := List.mem_map.mp ho
  dsimp only at hvEq
  subst v
  obtain ⟨j, _, u, ha, _⟩ := fgsa_vote_stamp_source E rho i x s k C stamp hv
  have heq := Gen.V2.Duty.honest_unique_singleDuty_statement (P := fgsa p c) E rho
    hE.nodup hE.toUnforgeableSignatures (fgsaHooks p c).handles_carries
    (.base (.head s)) (fgsa_head_singleDuty s) k hh (ofHead p ⟨.seat (.head s) k, C⟩)
    (ofHead p ⟨.seat (.head s) k, K⟩) rfl rfl
    (Or.inr ⟨j, x, u, ha.1⟩) (Or.inl ⟨t, he⟩)
  have hCK : C = K := congrArg (fun o : Obj p => o.payload) heq |> Msg.head.inj
  subst C
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1 and §5.4. Class (ii), active receipt instance.
DC: Goldfish/Confirmation:494,508. INTENTIONAL: resolved support is restricted
by the current F; the receipt must retain its target (P3:4921–4929).
The read is the actual pre-gate store, including clockPre. -/
theorem fgsa_active_support_of_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (k : Fin p.n) (K B : Block) (t : Time)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K.root⟩) t)
    (hv : baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
      (storeAt p c E rho i x).base.votes)
    (hK : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks)
    (hslot : K.slot ≤ s)
    (hvote : GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))) (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) <
      GridCO.earlyTime p.toParams.engine s)
    (hblock : GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s)
    (hBK : Block.Preceq B K) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    Gen.AC.Root.poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) k B = true := by
  intro v
  let o : GridCO.Wire p.n .root := ⟨.seat s k, .head K.root⟩
  have hvotes : v.votes = (storeAt p c E rho i x).base.votes :=
    (Internal.clockPre_vn (storeAt p c E rho i x) _).1
  change K ∈ v.blocks at hK
  change GridCO.stampVote v o < _ at hvote
  change GridCO.stampBlock v K < _ at hblock
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  have hstore := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x)
    (SA.gateTime p.toParams s)
  have hdomain : pre.base.headDomain = none := by
    rw [clockPre_headDomain]
    exact base_headDomain_none p (reachable_stateBefore E rho i x)
  have hresolve : GridCO.resolvedHead? v o = some K :=
    actView_resolve_of_mem p pre hstore hdomain hK s k
  have hlookup : Block.findByRoot? v.blocks K.root = some K :=
    Block.findByRoot?_of_unique hK (fun A hA C hC =>
      baseBlocks_rootInj p pre hstore A (List.mem_filter.mp hA).1 C (List.mem_filter.mp hC).1)
  have hmem : o ∈ GridCO.earlyVotes p.toParams.engine v s := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨?_, by exact beq_self_eq_true _⟩, ?_⟩
    · rw [hvotes]; exact hv
    · unfold GridCO.resolvedBefore
      rw [hresolve]
      change ((decide (K.slot ≤ s) &&
        decide (GridCO.stampVote v o < GridCO.earlyTime p.toParams.engine s)) &&
        decide (GridCO.stampBlock v K < GridCO.earlyTime p.toParams.engine s)) = true
      simp only [hslot, hvote, hblock, decide_true, Bool.true_and]
  have hclean : o ∈ GridCO.cleanSupport p.toParams.engine v s := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    rw [Bool.not_eq_true']
    apply List.any_eq_false.mpr
    intro u hu
    by_cases hs : GridCO.sameSeat u o = true
    · have hl : GridCO.headLabel? u = some s := by
        exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hu).1).2
      have hk : GridCO.headSeat? u = some k := by
        rcases u with ⟨ua, up⟩
        cases ua with
        | none => cases up <;> cases hl
        | proposer r => cases up <;> cases hl
        | seat r j =>
          cases up with
          | proposal C raw sup => cases hl
          | head C =>
            change (r == s && j == k) = true at hs
            have hj := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hs).2
            subst j
            rfl
      have hum : u ∈ (storeAt p c E rho i x).base.votes := by
        rw [← hvotes]
        exact (List.mem_filter.mp (List.mem_filter.mp hu).1).1
      have hue := fgsa_honest_head_eq_of_stored E rho hE i x s k K.root t hh he u hum
        hl hk
      change u = o at hue
      rw [hue]
      simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true]
    · simp only [Bool.eq_false_iff.mpr hs, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
  apply (Gen.AC.Root.vote_pool_support_witness _ _ k B).mpr
  refine ⟨o, hclean, rfl, ?_⟩
  unfold Gen.AC.Root.voteSupports Gen.AC.Root.resolvedTarget?
  change (match Block.findByRoot? v.blocks K.root with
    | none => false
    | some C => decide (C ∈ v.blocks) && decide (C.slot ≤ s) && Block.preceq B C) = true
  rw [hlookup]
  change (decide (K ∈ v.blocks) && decide (K.slot ≤ s) && Block.preceq B K) = true
  simp only [hK, hslot, decide_true, Bool.true_and]
  exact hBK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 F1b.1, K8 and blueprint 02 §5.4:531–541. Class (ii), active path
instance. DC: no exact counterpart for active F filtering. INTENTIONAL: compatibility
through every intervening F (the K8 `compat` field, P3:4921–4929).
A received path whose head extends the final F stays in the active view. -/
theorem fgsa_active_path_of_coverage (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoveragePremises E rho dl cut D first x K required paths)
    (hpath : paths K D)
    (hFK : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage E rho dl cut D first x K required paths
    hroots hDelta hE hN hx hcov).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hKF, _⟩ | ⟨_, _, hpaths⟩
    · have heq : K = eraseFG st.fg.F := Gen.Pure.block_preceq_antisymm hKF hFK
      rw [heq]
      exact (actView_genesis_F p st hb).2
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (Gen.Pure.block_preceq_refl K)
      apply (actView_blocks st K).mpr
      refine ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, ?_⟩
      exact Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFK
  intro X hX
  exact actView_ancestor_closed p st hb hK hX

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1. Class (ii), late-participant instance.
DC: Goldfish/Confirmation:494,508; same honest participation bound.
Authenticity retains the HEAD label and exact vote duty time. -/
theorem fgsa_stored_honest_head_awake (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (s : Slot) (k : Fin p.n) (o : GridCO.Wire p.n .root)
    (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true := by
  obtain ⟨K, rfl⟩ := count_head_keys o s k hl hk
  change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes at ho
  rw [← fgsa_vote_stamp_keys E rho i x] at ho
  obtain ⟨⟨v, stamp⟩, hv, hvEq⟩ := List.mem_map.mp ho
  dsimp only at hvEq
  subst v
  obtain ⟨j, _, u, ha, _⟩ := fgsa_vote_stamp_source E rho i x s k K stamp hv
  obtain ⟨parent, hd, hhandles⟩ := ha.1
  have horigin : ∃ t, t ≤ u ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
      (ofHead p ⟨.seat (.head s) k, K⟩) t := by
    rcases (fgsaHooks p c).handles_carries _ parent _ hhandles with hp | hc
    · subst parent
      exact hE.unforgeable x _ u ⟨j, hd⟩ _ hh rfl
    · exact hE.carried x parent u ⟨j, hd⟩ _ hc _ hh rfl
  obtain ⟨t, _, j', ht, he⟩ := horigin
  rw [(V2.D.Run.step_tick_eq E rho ht).2] at he
  have hem := (fgsa_emits_head E rho _ _ t s k K).mp he
  rw [hem.2.1]
  exact hem.1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §2.1. Class (ii), label-seat count instance.
DC: Goldfish/Confirmation:494,508; same honest/rest partition. The selected
batch contains all honest holders awake at the vote duty.
Stored-vote authenticity supplies this timing fact with the original label. -/
theorem fgsa_late_rest_bound [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hE : V2.D.ExecutionValid E rho) (i : Nat) (x : V) (s : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head s)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true → k ∈ H) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset \ H).card ≤
      (Gen.V2.Duty.faulty rho).card := by
  intro v
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    have hlabel : GridCO.headLabel? o = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have h := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at h
      rw [(Internal.clockPre_vn _ _).1] at h
      exact h
    exact fgsa_stored_honest_head_awake E rho hE i x s k o hm hlabel hs hh
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1, blueprint 02 §5.4:531–541. Class (ii), Gen batch instance.
DC: Goldfish/Confirmation:494,508,567. INTENTIONAL: two supported prefixes,
including the F anchor, and only the stored suffix (P3:4900–4945).
This is the count boundary over the actual pre-gate store. Receipt resolution
and head-history facts are explicit; they are not assumed count conclusions. -/
theorem fgsa_gate_batch_premises [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (s : Slot) (B : Block) (H : Finset (Fin p.n))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hH : ∀ k, rho.seatOf (.base (.head s)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true → k ∈ H)
    (hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) k)
        (ofHead p ⟨.seat (.head s) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      K ∈ (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))).blocks ∧
      K.slot ≤ s ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)))
        (baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)) < GridCO.earlyTime
            p.toParams.engine s ∧
      GridCO.stampBlock
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) K <
        GridCO.earlyTime p.toParams.engine s ∧
      Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  intro pre v a
  have hsupp (X : Block) (hX : X = a ∨ X = B) :
      ∀ k ∈ H, Gen.AC.Root.poolSupports v.blocks
        (GridCO.cleanSupport p.toParams.engine v s) k X = true := by
    intro k hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, haK, hBK⟩ := hheads k hk
    apply fgsa_active_support_of_receipt E rho hE i x s k K X t hh he hv hK hslot hvs hbs
    rcases hX with rfl | rfl
    · exact haK
    · exact hBK
  have hrest := fgsa_late_rest_bound E rho hC hE i x s H hH
  have hcount (X : Block) (hX : X = a ∨ X = B) :
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.Root.prefixSupport p.toParams v s X := by
    have hc := Gen.AC.Root.batch_counts v.blocks (GridCO.lateVotes p.toParams.engine v s)
      (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s)
      H H.card (Gen.V2.Duty.faulty rho).card X
      (fun _ ho => fgsa_early_subset_late p v s (List.mem_filter.mp ho).1)
      (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p v s k)
      (hsupp X hX) hrest hbatch
    have he := actView_score p pre
      (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      (GridCO.cleanSupport p.toParams.engine v s) (GridCO.cleanSupport p.toParams.engine v s) X
    change _ < 2 * GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks _ _ X
    rw [he]
    exact (hc.2.2.1 X (Gen.Pure.block_preceq_refl X)).2
  refine ⟨hcount a (Or.inl rfl), hcount B (Or.inr rfl), ?_⟩
  intro X _ hXB _
  have hpos : 0 < H.card := lt_of_le_of_lt (Nat.zero_le _) hbatch.lt
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  obtain ⟨K, _, _, _, _, hK, _, _, _, _, hBK⟩ := hheads k hk
  have hstore := cstoreInv_clockPre p (storeAt p c E rho i x)
    (storeBundle_stateBefore E rho i x).cstore (SA.gateTime p.toParams s)
  exact actView_ancestor_closed p pre hstore hK (Gen.Pure.block_preceq_trans hXB hBK)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.1; blueprint 02 §5.4, genesis case (f2-5a1 finding (a)).
Class (ii), active honest batch instance. DC: Goldfish/Confirmation:494,508,567;
INTENTIONAL: the optional F-anchored result must pass the anchor test.
Honest genesis receipts give a strict majority and exclude every non-genesis
result at this actual pre-gate store. Receipt stamps remain explicit inputs. -/
theorem fgsa_gate_zero_of_receipts [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (i : Nat) (x : V) (H : Finset (Fin p.n))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card)
    (hH : ∀ k, rho.seatOf (.base (.head 0)) k ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head 0)) k) (SA.voteTime p.toParams 0) = true → k ∈ H)
    (hF : eraseFG (storeAt p c E rho i x).fg.F = .genesis)
    (hreceipts : ∀ k ∈ H, ∃ t,
      rho.seatOf (.base (.head 0)) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head 0)) k)
        (ofHead p ⟨.seat (.head 0) k, genesisRoot⟩) t ∧
      baseVote (⟨.seat (.head 0) k, genesisRoot⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)))
        (baseVote (⟨.seat (.head 0) k, genesisRoot⟩ : HeadWire p.n)) <
          GridCO.earlyTime p.toParams.engine 0)
    (hgen : GridCO.stampBlock
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0))) .genesis <
        GridCO.earlyTime p.toParams.engine 0) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams 0)
    let v := actView pre
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v 0) <
      2 * SA.Root.prefixSupport p.toParams v 0 .genesis ∧
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) v 0 = some .genesis := by
  intro pre v
  have hstore := cstoreInv_clockPre p (storeAt p c E rho i x)
    (storeBundle_stateBefore E rho i x).cstore (SA.gateTime p.toParams 0)
  have hg : Block.genesis ∈ v.blocks := (actView_genesis_F p pre hstore).1
  have hsupp : ∀ k ∈ H,
      Gen.AC.Root.poolSupports v.blocks
        (GridCO.cleanSupport p.toParams.engine v 0) k .genesis = true := by
    intro k hk
    obtain ⟨t, hh, he, hv, hvs⟩ := hreceipts k hk
    exact fgsa_active_support_of_receipt E rho hE i x 0 k .genesis .genesis t hh he hv
      hg (Nat.le_refl 0) hvs hgen (Gen.Pure.block_preceq_refl _)
  have hc := Gen.AC.Root.batch_counts v.blocks (GridCO.lateVotes p.toParams.engine v 0)
    (GridCO.cleanSupport p.toParams.engine v 0) (GridCO.cleanSupport p.toParams.engine v 0)
    H H.card (Gen.V2.Duty.faulty rho).card .genesis
    (fun _ ho => fgsa_early_subset_late p v 0 (List.mem_filter.mp ho).1)
    (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p v 0 k)
    hsupp (fgsa_late_rest_bound E rho hC hE i x 0 H hH) hbatch
  have hscore (B : Block) : SA.Root.prefixSupport p.toParams v 0 B =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v 0)
        (GridCO.cleanSupport p.toParams.engine v 0) B :=
    actView_score p pre hstore
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      _ _ B
  have hmajor := (hc.2.2.1 .genesis (Gen.Pure.block_preceq_refl _)).2
  let score := GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v 0)
    (GridCO.cleanSupport p.toParams.engine v 0)
  let elig := fun X => decide (GridCO.voterCount (GridCO.lateVotes p.toParams.engine v 0) <
    2 * score X)
  have hno (C : Block) (hne : C ≠ .genesis) (k : Fin p.n) (hk : k ∈ H) :
      Gen.AC.Root.poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v 0) k C = false
          := by
    apply Bool.eq_false_iff.mpr
    intro hs
    obtain ⟨o, ho, hseat, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k C).mp hs
    have hearly := (List.mem_filter.mp ho).1
    have hlabel : GridCO.headLabel? o = some 0 :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
    have hm : o ∈ (storeAt p c E rho i x).base.votes := by
      have hm := (List.mem_filter.mp (List.mem_filter.mp hearly).1).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
      rw [(Internal.clockPre_vn _ _).1] at hm
      exact hm
    obtain ⟨t, hh, he, _, _⟩ := hreceipts k hk
    have heq := fgsa_honest_head_eq_of_stored E rho hE i x 0 k genesisRoot t hh he
      o hm hlabel hseat
    rw [heq] at hvote
    have hlookup : Block.findByRoot? v.blocks genesisRoot = some .genesis :=
      Block.findByRoot?_of_unique hg (fun A hA B hB =>
        baseBlocks_rootInj p pre hstore A (List.mem_filter.mp hA).1 B (List.mem_filter.mp hB).1)
    change (match Block.findByRoot? v.blocks genesisRoot with
      | none => false
      | some B => decide (B ∈ v.blocks) && decide (B.slot ≤ 0) && Block.preceq C B) = true
      at hvote
    rw [hlookup] at hvote
    change (_ && _ && decide (C = Block.genesis)) = true at hvote
    exact hne (of_decide_eq_true (Bool.and_eq_true_iff.mp hvote).2)
  have hdom : Gen.Pure.DominatedSuffix .genesis .genesis v.blocks score elig := by
    rw [Gen.Pure.DominatedSuffix_def]
    intro C hstrict hC
    have heq : C = .genesis := of_decide_eq_true hC
    subst C
    change (false && _) = true at hstrict
    cases hstrict
  have hstop : Gen.Pure.NoEligibleChild v.blocks elig .genesis := by
    rw [Gen.Pure.NoEligibleChild_def]
    intro C _ hp
    have hne : C ≠ .genesis := by intro h; subst C; cases hp
    have hbound := hc.2.2.2.2 C (hno C hne)
    exact decide_eq_false (Nat.not_lt_of_ge hbound)
  have hw := Gen.Pure.walk_exact_of_dominated_suffix .genesis .genesis
    v.blocks score elig (Gen.Pure.block_preceq_refl _) hdom hstop
  refine ⟨by rw [hscore]; exact hmajor, ?_⟩
  have ha : eraseFG pre.fg.F = .genesis := by
    change eraseFG (clockPre p _ _).fg.F = _
    rw [clockPre_fg]
    exact hF
  rw [ha]
  have hscoreFn : GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks
      (GridCO.cleanSupport p.toParams.engine v 0)
      (GridCO.cleanSupport p.toParams.engine v 0) = score := funext hscore
  unfold SA.Root.confirmationFrom GridCO.confirmationFrom
  dsimp only
  rw [hscoreFn]
  change (if GridCO.voterCount (GridCO.lateVotes p.toParams.engine v 0) <
      2 * score (GridCO.ghost .genesis v.blocks score elig) then
        some (GridCO.ghost .genesis v.blocks score elig) else none) = _
  rw [hw]
  exact ite_eq_left hmajor

end AvailableChain.FGSA.Run
end
