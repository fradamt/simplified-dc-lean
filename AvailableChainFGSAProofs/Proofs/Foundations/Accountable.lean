module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainFGSAProofs.Proofs.Foundations.Client
public import AvailableChainGeneric.Proofs.V2.Linked
public import AvailableChainFGSARun.Proofs.Receipts

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- A finalized certificate names both the target and its certificate height, as in DC. -/
def FGFinalizedAt (K T : FGBlock (Fin p.n)) (h : Nat) : Prop :=
  (derive p.E p.cfg K).F = T ∧ (derive p.E p.cfg K).h_F = h

/-- The same proposal/ancestor carrier as the frozen RunFGBlock, stated here
without a Claims import. It includes emitted and delivered run proposals. -/
def FinalityRunBlock (X : FGBlock (Fin p.n)) : Prop :=
  ∃ o b raw sup rows,
    o.payload = Msg.proposal b raw sup rows ∧
    ((∃ x t, V2.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) b

/-- DC store_attestations: the union of all stored chain rows. -/
def finalityStoreRows (st : State p.n) : Finset (Row (Fin p.n)) :=
  st.fg.TF.biUnion chainRows

/-- DC DecoupledConsensusModel/Protocol/Evidence.lean:67 (store_attestations):
the evidence pool contains every raw row on every held chain, including ancestor
rows. No divergence; the direct rowPool is not used for this pool. -/
theorem fgsa_finalityStoreRows_contains (st : State p.n) (K : FGBlock (Fin p.n))
    (hK : K ∈ st.fg.TF) : chainRows K ⊆ finalityStoreRows p st := by
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨K, hK, hu⟩

/-- Honest carriage is separate from weight-level evidence. -/
def FinalityCarriage (A : Finset (Row (Fin p.n))) : Prop :=
  ∀ u ∈ A, ∃ (a : RowWire p.n) (r : Nat),
    a.toRow? = some u ∧ a.auth = .seat (.fg r) u.signer ∧
    ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a

/-- Run-free accountable finality. Root injectivity is automatic in FG-SA;
the explicit scoped _hroot premise is unused and keeps the DC interface visible. -/
theorem fgsa_pureAccountable (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat)
    (_hroot : KitFG.RootInjectiveOn K W)
    (hK : FGFinalizedAt p K T₁ h₁) (hW : FGFinalizedAt p W T₂ h₂) :
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true :=
  (KitFG.slashableWeight_or_finalized_compatible p.E p.cfg K W).imp id
    (fun h => hK.1 ▸ hW.1 ▸ h)

theorem fgsa_pureAgreement (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat)
    (hroot : KitFG.RootInjectiveOn K W)
    (hK : FGFinalizedAt p K T₁ h₁) (hW : FGFinalizedAt p W T₂ h₂)
    (hb : ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) :
    FGBlock.compatible T₁ T₂ = true :=
  (fgsa_pureAccountable p K W T₁ T₂ h₁ h₂ hroot hK hW).resolve_left hb

/-- All three DC observation clauses. No honesty behaviour, authenticity,
fault bound, or schedule assumption occurs in this evidence contract. -/
structure FGWholeRunAccountable : Prop where
  chains : ∀ K W T₁ T₂ h₁ h₂,
    FinalityRunBlock p c E rho K → FinalityRunBlock p c E rho W →
    FGFinalizedAt p K T₁ h₁ → FGFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true
  eventPrefixes : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween p.E (finalityStoreRows p (storeAt p c E rho i u))
      (finalityStoreRows p (storeAt p c E rho j v)) ∨
      FGBlock.compatible (storeAt p c E rho i u).fg.F (storeAt p c E rho j v).fg.F = true
  reads : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween p.E (finalityStoreRows p (V2.Run.readAt E rho t u).st)
      (finalityStoreRows p (V2.Run.readAt E rho t' v).st) ∨
      FGBlock.compatible (V2.Run.readAt E rho t u).st.fg.F
        (V2.Run.readAt E rho t' v).st.fg.F = true

private theorem store_accountable (st st' : State p.n)
    (hs : CStoreInv p st) (hs' : CStoreInv p st') :
    HasSlashableWeightBetween p.E (finalityStoreRows p st) (finalityStoreRows p st') ∨
      FGBlock.compatible st.fg.F st'.fg.F = true := by
  obtain ⟨K, hK, hKF⟩ := hs.fg.Fcar
  obtain ⟨W, hW, hWF⟩ := hs'.fg.Fcar
  rcases KitFG.slashableWeight_or_finalized_compatible p.E p.cfg K W with hev | hc
  · obtain ⟨S, hw, he⟩ := hev
    refine Or.inl ⟨S, hw, ?_⟩
    intro i hi
    obtain ⟨a, ha, b, hb, hai, hbi, hab⟩ := he i hi
    exact ⟨a, Finset.mem_biUnion.mpr ⟨K, hK, ha⟩,
      b, Finset.mem_biUnion.mpr ⟨W, hW, hb⟩, hai, hbi, hab⟩
  · exact Or.inr (hKF ▸ hWF ▸ hc)

/-- FG-SA's reachable time reader needs no sorting. Content roots satisfy
KitFG.rootInjectiveOn_all, so there is no extra execution premise. -/
theorem fgsa_wholeRunAccountable : FGWholeRunAccountable p c E rho where
  chains := fun K W T₁ T₂ h₁ h₂ _ _ hK hW =>
    fgsa_pureAccountable p K W T₁ T₂ h₁ h₂ (KitFG.rootInjectiveOn_all K W) hK hW
  eventPrefixes := fun u _ v _ i j => store_accountable p _ _
    (storeBundle_stateBefore E rho i u).cstore (storeBundle_stateBefore E rho j v).cstore
  reads := fun u _ v _ t t' => store_accountable p _ _
    (storeBundle_readAt E rho t u).cstore (storeBundle_readAt E rho t' v).cstore

/-- DC DecoupledConsensusInternal/Legacy/Assumptions/Weight.lean:30:
no slashable weight between ALL run blocks, including ancestors of emitted or
delivered proposals. FinalityRunBlock is definitionally the frozen RunFGBlock;
it does not require held-chain membership. No scope divergence. -/
def FGSASlashableBound : Prop :=
  ∀ K W, FinalityRunBlock p c E rho K → FinalityRunBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)

/-- DC DecoupledConsensusInternal/Legacy/Assumptions/Weight.lean:30 (SlashableBound).
The defining equation lets other lane modules use the all-run bound. -/
theorem FGSASlashableBound_def : FGSASlashableBound p c E rho ↔
    ∀ K W, FinalityRunBlock p c E rho K → FinalityRunBlock p c E rho W →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) := by rfl

private theorem stored_finality_delivery (i : Nat) (x : V) (K : FGBlock (Fin p.n))
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hne : K ≠ .genesis) :
    ∃ o raw sup rows y t, o.payload = Msg.proposal (eraseFG K) raw sup rows ∧
      V2.Event.deliver y o t ∈ rho.events := by
  obtain ⟨slot, raw, sup, wires, _, j, o, t, _, hd, he⟩ :=
    stored_block_wire_delivery p c E rho i x K hK hne
  refine ⟨o, raw, sup, wires, x, t, ?_, List.mem_of_getElem? hd⟩
  rw [he]
  rfl

private theorem read_finality_runBlock (t : Time) (x : V) (K : FGBlock (Fin p.n))
    (hK : K ∈ (V2.Run.readAt E rho t x).st.fg.TF) (hne : K ≠ .genesis) :
    FinalityRunBlock p c E rho K := by
  let rho' := { rho with events := rho.events.filter (fun e => decide (e.time ≤ t)) }
  have hs : V2.World.step E rho' = V2.World.step E rho := by
    funext w e
    cases e <;> rfl
  have hst : storeAt p c E rho' rho'.events.length x = (V2.Run.readAt E rho t x).st := by
    change ((rho'.events.take rho'.events.length).foldl
      (V2.World.step E rho') V2.World.init x).st = _
    rw [List.take_length, hs]
    rfl
  obtain ⟨o, raw, sup, rows, y, s, ho, hd⟩ :=
    stored_finality_delivery p c E rho' rho'.events.length x K (hst ▸ hK) hne
  exact ⟨o, eraseFG K, raw, sup, rows, ho,
    Or.inr ⟨y, s, (List.mem_filter.mp hd).1⟩, eraseFG_preceq (KitFG.preceq_refl K)⟩

private theorem store_agreement_of_bound (hb : FGSASlashableBound p c E rho)
    (st st' : State p.n) (hs : CStoreInv p st) (hs' : CStoreInv p st')
    (hcar : ∀ K ∈ st.fg.TF, K ≠ .genesis → FinalityRunBlock p c E rho K)
    (hcar' : ∀ K ∈ st'.fg.TF, K ≠ .genesis → FinalityRunBlock p c E rho K) :
    FGBlock.compatible st.fg.F st'.fg.F = true := by
  obtain ⟨K, hK, hKF⟩ := hs.fg.Fcar
  obtain ⟨W, hW, hWF⟩ := hs'.fg.Fcar
  by_cases hk : K = .genesis
  · subst K
    rw [← hKF]
    exact Bool.or_eq_true_iff.mpr (Or.inl (KitFG.genesis_preceq _))
  by_cases hw : W = .genesis
  · subst W
    rw [← hWF]
    exact Bool.or_eq_true_iff.mpr (Or.inr (KitFG.genesis_preceq _))
  have hc := fgsa_pureAgreement p K W _ _ _ _ (KitFG.rootInjectiveOn_all K W)
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (hb K W (hcar K hK hk) (hcar' W hW hw))
  exact hKF ▸ hWF ▸ hc

/-- DC DecoupledConsensusInternal/Legacy/Definitions/FinalitySafety.lean:83
(WholeRunFinalitySafety), event-prefix corollary under the all-run bound.
INTENTIONAL: FG-SA content roots are injective without a run premise.
The reachable-store invariant covers every node, so no honesty premise is needed. -/
theorem fgsa_eventPrefixAgreement_of_bound (hb : FGSASlashableBound p c E rho)
    (e e' : Nat) (x y : V) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true := by
  apply store_agreement_of_bound p c E rho hb _ _
    (storeBundle_stateBefore E rho e x).cstore (storeBundle_stateBefore E rho e' y).cstore
  · intro K hK hne
    obtain ⟨o, raw, sup, rows, z, t, ho, hd⟩ := stored_finality_delivery p c E rho e x K hK hne
    exact ⟨o, eraseFG K, raw, sup, rows, ho, Or.inr ⟨z, t, hd⟩,
      eraseFG_preceq (KitFG.preceq_refl K)⟩
  · intro K hK hne
    obtain ⟨o, raw, sup, rows, z, t, ho, hd⟩ := stored_finality_delivery p c E rho e' y K hK hne
    exact ⟨o, eraseFG K, raw, sup, rows, ho, Or.inr ⟨z, t, hd⟩,
      eraseFG_preceq (KitFG.preceq_refl K)⟩

/-- DC WholeRunFinalitySafety with the same SlashableBound over all run blocks.
Time-read carriage uses the filtered run, so FG-SA needs no sorting premise. -/
theorem fgsa_wholeRunAgreement (hb : FGSASlashableBound p c E rho) :
    (∀ K W T₁ T₂ h₁ h₂, FinalityRunBlock p c E rho K → FinalityRunBlock p c E rho W →
      FGFinalizedAt p K T₁ h₁ → FGFinalizedAt p W T₂ h₂ →
      FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      FGBlock.compatible (V2.Run.readAt E rho t u).st.fg.F
        (V2.Run.readAt E rho t' v).st.fg.F = true) := by
  have ha := fgsa_wholeRunAccountable p c E rho
  refine ⟨fun K W T₁ T₂ h₁ h₂ hK hW hf hg =>
    (ha.chains K W T₁ T₂ h₁ h₂ hK hW hf hg).resolve_left (hb K W hK hW), ?_⟩
  intro u _ v _ t t'
  exact store_agreement_of_bound p c E rho hb _ _
    (storeBundle_readAt E rho t u).cstore (storeBundle_readAt E rho t' v).cstore
    (read_finality_runBlock p c E rho t u) (read_finality_runBlock p c E rho t' v)

/-- Slashable identities on two held chains give distinct faulty holders.
Linked transports row identities before any fault bound is used. -/
private theorem slashable_pool_count [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (A B : Finset (Row (Fin p.n)))
    (hA : FinalityCarriage p c E rho A) (hB : FinalityCarriage p c E rho B)
    (hev : HasSlashableWeightBetween p.E A B) :
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card := by
  classical
  obtain ⟨S, hw, hs⟩ := hev
  have hcard := Gen.V2.linked_card_le_of_holders hL (S.image Fin.val)
    (Gen.V2.faulty rho) (by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨u, hu, v, hv, hui, hvi, huv⟩ := hs i hi
      obtain ⟨a, r, hau, har, hea⟩ := hA u hu
      obtain ⟨b, s, hbv, hbs, heb⟩ := hB v hv
      let z := rho.seatOf (.base (.fg r)) u.signer
      have heq : rho.seatOf (.base (.fg s)) v.signer = z :=
        Gen.V2.linked_holder_eq hL (ℓ := .base (.fg s)) (ℓ' := .base (.fg r))
          (by trivial) (by trivial) v.signer u.signer
          (congrArg Fin.val (hvi.trans hui.symm))
      have ha : RowSigner p c rho a z := (rowSigner_iff_holder p c rho a z).mpr
        ⟨⟨r, u.signer, har⟩, by
          change V2.Run.holder rho (ofAuth p a.auth) = some z
          rw [har]
          rfl⟩
      have hb : RowSigner p c rho b z := (rowSigner_iff_holder p c rho b z).mpr
        ⟨⟨s, v.signer, hbs⟩, by
          change V2.Run.holder rho (ofAuth p b.auth) = some z
          rw [hbs]
          exact congrArg some heq⟩
      have hz : z ∉ rho.honest := by
        intro hzh
        exact hC z hzh a b (hea z ha hzh) (heb z hb hzh) u v hau hbv huv
      refine ⟨.base (.fg r), by trivial, u.signer, congrArg Fin.val hui, ?_⟩
      rw [Gen.V2.faulty_def]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩)
  have hcS : (S.image Fin.val).card = S.card :=
    Finset.card_image_of_injective S Fin.val_injective
  rw [hcS] at hcard
  have htotal : p.E.totalWeight = p.n := by
    change (∑ _i : Fin p.n, (1 : Nat)) = p.n
    simp
  have hunit : p.E.weightOf S = S.card := by
    change (∑ _i ∈ S, (1 : Nat)) = S.card
    simp
  have hq : p.E.q = Gen.Pure.qF p.n := by
    change (2 * p.E.totalWeight + 2) / 3 = Gen.Pure.qF p.n
    rw [htotal, Gen.Pure.qF_def]
  change 2 * p.E.q ≤ p.E.totalWeight + p.E.weightOf S at hw
  rw [hq, htotal, hunit] at hw
  omega

/-- The stored-tree union inherits honest carriage from each held chain. -/
private theorem store_carriage (hU : V2.UnforgeableSignatures E rho)
    (i : Nat) (x : V) (hx : x ∈ rho.honest) :
    FinalityCarriage p c E rho (finalityStoreRows p (storeAt p c E rho i x)) := by
  intro u hu
  obtain ⟨K, hK, hu⟩ := Finset.mem_biUnion.mp hu
  exact held_chain_row_origin p c E rho hU i x K ⟨hx, hK⟩ u hu

/-- Fault-count attribution is separate from the evidence theorem. -/
theorem fgsa_slashable_faulty_count [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (e e' : Nat) (x y : V) (K W : FGBlock (Fin p.n))
    (hK : HeldAt p c E rho e x K) (hW : HeldAt p c E rho e' y W)
    (hev : HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) :
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card :=
  slashable_pool_count p c E rho hL (fgsa_clientSafeAll p c E rho hL) _ _
    (held_chain_row_origin p c E rho hU e x K hK)
    (held_chain_row_origin p c E rho hU e' y W hW) hev

/-- The event-prefix agreement form excludes only the observed weight evidence. -/
theorem fgsa_eventPrefixAgreement (e e' : Nat) (x y : V)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hb : ¬ HasSlashableWeightBetween p.E
      (finalityStoreRows p (storeAt p c E rho e x))
      (finalityStoreRows p (storeAt p c E rho e' y))) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F (storeAt p c E rho e' y).fg.F = true :=
  ((fgsa_wholeRunAccountable p c E rho).eventPrefixes x hx y hy e e').resolve_left hb

/-- Faults exclude store evidence only after identity transport and client safety. -/
theorem fgsa_storeSlashableBound_of_faults [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.faulty rho).card)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    ¬ HasSlashableWeightBetween p.E (finalityStoreRows p (storeAt p c E rho e x))
      (finalityStoreRows p (storeAt p c E rho e' y)) := by
  intro hev
  have hc := slashable_pool_count p c E rho hL hC _ _
    (store_carriage p c E rho hU e x hx) (store_carriage p c E rho hU e' y hy) hev
  have ht := hX.lt
  omega

/-- DC DecoupledConsensusProofs/Protocol/ChainState/AlignedRoundLemmas.lean:284
(slashableBound_of_belowOneThird). Unit weights turn the strict one-third bound
into faulty.card ≤ (n - 1) / 3 because p.nPos. Carriage covers ALL run blocks.
Motivated divergence: Linked transports FG-SA rotating seat identities to holders;
DC rows use validator identities directly. hC is the expanded ClientSafeAll Prop,
which avoids a Claims import under X5.
fgsa_runBlock_carriage supplies hcar from ExecutionValid, as in DC. -/
theorem fgsa_slashableBound_of_faults [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hbot : (Gen.V2.faulty rho).card ≤ (p.n - 1) / 3)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (hcar : ∀ K, FinalityRunBlock p c E rho K → FinalityCarriage p c E rho (chainRows K)) :
    FGSASlashableBound p c E rho := by
  intro K W hK hW hev
  have hc := slashable_pool_count p c E rho hL hC _ _ (hcar K hK) (hcar W hW) hev
  have ht := (Gen.Pure.count_rec p.nPos hbot).lt
  omega

/-- DC counterpart: none (store-scope base adapter).
The fault bridge keeps hC; this adapter supplies it from BaseSet.linked.
BaseSet retains noRestart, delta and cstar; these fields are unused here. -/
theorem fgsa_storeSlashableBound_of_base [Fintype V] (hb : BaseSet p c E rho)
    (hbot : (Gen.V2.faulty rho).card ≤ (p.n - 1) / 3)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    ¬ HasSlashableWeightBetween p.E (finalityStoreRows p (storeAt p c E rho e x))
      (finalityStoreRows p (storeAt p c E rho e' y)) :=
  fgsa_storeSlashableBound_of_faults p c E rho hb.linked hb.valid.toUnforgeableSignatures
    (Gen.Pure.count_rec p.nPos hbot) (fgsa_clientSafeAll p c E rho hb.linked) e e' x y hx hy

/-- Validator attribution for two honest store observations. -/
theorem fgsa_accountable [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true ∨
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card := by
  rcases (fgsa_wholeRunAccountable p c E rho).eventPrefixes x hx y hy e e' with hev | hc
  · exact Or.inr (slashable_pool_count p c E rho hL (fgsa_clientSafeAll p c E rho hL) _ _
      (store_carriage p c E rho hU e x hx) (store_carriage p c E rho hU e' y hy) hev)
  · exact Or.inl hc

-- Keep the original observation binders; pure evidence does not use their proofs.
set_option linter.unusedVariables false in
set_option linter.unusedFintypeInType false in
/-- Weight evidence for R-XING, with the explicit accepted carrier K.
Honesty and held membership describe the observations only; no behaviour is assumed.
The retained hx and hK proofs are unused; the evidence holds for any K and W.
The retained hW proof and its e', y indices are unused for the same reason.
The retained Fintype instance is unused by pure weight evidence. -/
theorem fgsa_finalLock_ev [Fintype V]
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest)
    (K W : FGBlock (Fin p.n))
    (hK : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (derive p.E p.cfg K).F = (storeAt p c E rho e x).fg.F)
    (hW : HeldAt p c E rho e' y W)
    (hh : (derive p.E p.cfg K).h_F < (derive p.E p.cfg W).h) :
    FGBlock.Preceq (storeAt p c E rho e x).fg.F W ∨
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) :=
  (KitFG.slashableWeight_or_finalized_preceq p.E p.cfg K W hh).symm.imp
    (fun h => hKF ▸ h) id

/-- The former finalLock_ev count conclusion, now a separate attribution corollary. -/
theorem fgsa_finalLock_faulty_count [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest)
    (K W : FGBlock (Fin p.n))
    (hK : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (derive p.E p.cfg K).F = (storeAt p c E rho e x).fg.F)
    (hW : HeldAt p c E rho e' y W)
    (hh : (derive p.E p.cfg K).h_F < (derive p.E p.cfg W).h) :
    FGBlock.Preceq (storeAt p c E rho e x).fg.F W ∨
      2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card :=
  (fgsa_finalLock_ev p c E rho e e' x y hx K W hK hKF hW hh).imp id
    (fgsa_slashable_faulty_count p c E rho hL hU e e' x y K W ⟨hx, hK⟩ hW)

/-- BaseSet discharges both attribution inputs.
The retained noRestart, delta and cstar fields are unused by attribution. -/
theorem fgsa_accountable_base [Fintype V] (hb : BaseSet p c E rho)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true ∨
      2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card :=
  fgsa_accountable p c E rho hb.linked (fgsa_unforgeable_of_base p c E rho hb) e e' x y hx hy

/-- DC counterpart: none (processed-proposal row helper).
The decoded rows of a processed proposal carry honest emissions. -/
theorem carried_rows_carriage (hU : V2.UnforgeableSignatures E rho)
    (v : V) (o : Obj p) (t : Time) (hp : V2.Run.processes rho v o t)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o.payload = Msg.proposal b raw sup rows) :
    FinalityCarriage p c E rho (rows.filterMap RowWire.toRow?).toFinset := by
  intro u hu
  obtain ⟨a, ha, hau⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hu)
  have auth : ∃ r, a.auth = .seat (.fg r) u.signer := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => cases hau
    | proposer s => cases hau
    | seat label i =>
        cases label with
        | head s => cases hau
        | fg r =>
            have he : (⟨i, payload.height_pair, payload.finality_pair⟩ : Row (Fin p.n)) = u :=
              Option.some.inj hau
            exact ⟨r, by rw [← he]⟩
  obtain ⟨r, har⟩ := auth
  have hc : (fgsa p c).carries o (ofRow p a) := by
    change carriesS p o (ofRow p a)
    unfold carriesS
    rw [ho]
    exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
  refine ⟨a, r, hau, har, ?_⟩
  intro z hz hzh
  obtain ⟨t', _, k, hk, hem⟩ := fgsa_carried_row E rho hU v z o t hp a hc hzh
    ((rowSigner_iff_holder p c rho a z).mp hz).2
  exact ⟨k, t', hk, hem⟩

/-- All-run carriage, DELIVERED case: ExecutionValid (wire check `rowsOk`,
dependency check `parentFG`, honest-only schedule, unforgeability) gives honest
carriage for every FG block whose erasure is an ancestor of a delivered
proposal block. This is the FG-SA analogue of DC
DecoupledConsensusProofs/Protocol/Handlers/StoreBridge.lean:376
`carriedByHonest_of_runBlock` (AdmissibleCore). -/
theorem delivered_runBlock_carriage (hv : V2.ExecutionValid E rho)
    (i : Nat) (v : V) (o : Obj p) (t : Time)
    (hd : rho.events[i]? = some (.deliver v o t))
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o.payload = Msg.proposal b raw sup rows)
    (K : FGBlock (Fin p.n)) (hK : Block.Preceq (eraseFG K) b) :
    FinalityCarriage p c E rho (chainRows K) := by
  have hvh : v ∈ rho.honest := hv.honest_only _ (List.mem_of_getElem? hd)
  have hwf : FGSA.wellFormed p (toWire p o) = true := hv.wire i v o t hd
  have hdep : depsS p (V2.Run.stateBefore E rho i v).st o = true := hv.deps i v o t hd
  have hw : toWire p o = ⟨toAuth p o.auth, .proposal b raw sup rows⟩ := by
    change (⟨toAuth p o.auth, o.payload⟩ : Wire p.n) = _
    rw [ho]
  change (match (toWire p o).decode with
    | some (.block _ b _ _ _) => (parentFG (V2.Run.stateBefore E rho i v).st b).isSome
    | _ => true) = true at hdep
  rw [hw] at hwf hdep
  generalize toAuth p o.auth = au at hwf hdep
  cases au with
  | none => change false = true at hwf; cases hwf
  | seat l j => cases l <;> change false = true at hwf <;> cases hwf
  | proposer s =>
    change (_ && rowsOk b rows) = true at hwf
    have hb0 : b ≠ .genesis := by
      have hg := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hwf).1).1).1).1).1).1
      intro he
      subst b
      cases hg
    have hrok : rowsOk b rows = true := (Bool.and_eq_true_iff.mp hwf).2
    change (parentFG (V2.Run.stateBefore E rho i v).st b).isSome = true at hdep
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hdep
    obtain ⟨hPT, hPe⟩ := pickPair_some_spec _ _ hP
    have hPe : eraseFG P = b.parent := of_decide_eq_true hPe
    have hcarP : FinalityCarriage p c E rho (chainRows P) :=
      held_chain_row_origin p c E rho hv.toUnforgeableSignatures i v P ⟨hvh, hPT⟩
    have hcarTop := carried_rows_carriage p c E rho hv.toUnforgeableSignatures v o t ⟨i, hd⟩
      b raw sup rows ho
    have htop : eraseFG (fgBlock P b rows) = b := eraseFG_fgBlock hb0 hPe rows hrok
    cases b with
    | genesis => exact absurd rfl hb0
    | node H s x =>
      change (decide (eraseFG K = Block.node H s x) || Block.preceq (eraseFG K) H) = true at hK
      rcases Bool.or_eq_true_iff.mp hK with he | hpre
      · have hKe : K = fgBlock P (.node H s x) rows :=
          eraseFG_injective ((of_decide_eq_true he).trans htop.symm)
        subst hKe
        intro u hu
        change u ∈ (rows.filterMap RowWire.toRow?).toFinset ∪ chainRows P at hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact hcarTop u hu
        · exact hcarP u hu
      · have hHP : H = eraseFG P := hPe.symm
        subst hHP
        have hKP : FGBlock.Preceq K P := ((fgsa_carrier_geometry K P).2.1).mpr hpre
        intro u hu
        exact hcarP u (KitFG.chainRows_mono hKP hu)


/-- DC counterpart: none (proposal row selection helper).
The rows chosen by `propose` come from the pool or from stored proposal wires. -/
theorem proposalRows_source (st : State p.n) (H : Block) :
    ∀ a ∈ proposalRows p st H, a ∈ st.rowPool ∨
      ∃ w ∈ st.proposals, ∃ s b raw sup rows,
        w.decode = some (.block s b raw sup rows) ∧ a ∈ rows := by
  let r := p.round (st.slot p)
  let inI := fun r' => decide (r ≤ r' + p.wF) && decide (r' ≤ r)
  let good := fun a : RowWire p.n => a ∈ st.rowPool ∨
      ∃ w ∈ st.proposals, ∃ s b raw sup rows,
        w.decode = some (.block s b raw sup rows) ∧ a ∈ rows
  have blocks : ∀ a ∈ blockWireRows p st inI, good a := by
    intro a ha
    obtain ⟨xs, hx, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp hx
    change (match w.decode with
      | some (.block _ b _ _ rows) => if inI (p.round b.slot) then
          some (rows.filter (fun a => (a.round?.map inI).getD false)) else none
      | _ => none) = some xs at he
    cases hd : w.decode with
    | none => rw [hd] at he; cases he
    | some m =>
      cases m with
      | vote s j b => rw [hd] at he; cases he
      | row r j body => rw [hd] at he; cases he
      | block s b raw sup rows =>
        rw [hd] at he
        dsimp only at he
        split at he
        · cases he
          exact Or.inr ⟨w, hw, s, b, raw, sup, rows, hd, (List.mem_filter.mp ha).1⟩
        · cases he
  let A := st.rowPool.filter (fun a => (a.round?.map inI).getD false &&
    !decide (a ∈ chainWireRows st H))
  have hA : ∀ a ∈ A, good a := fun a ha => Or.inl (List.mem_filter.mp ha).1
  change ∀ a ∈ (List.filter (fun a => !decide (a ∈ chainWireRows st H) && !decide (a ∈ A))
    (blockWireRows p st inI)).foldl (fun acc a =>
      if decide (a ∈ acc) || 2 ≤ (acc.filter (fun x =>
        x.decode?.map (fun y => (y.1, y.2.1)) == a.decode?.map (fun y => (y.1, y.2.1)))).length
      then acc else acc ++ [a]) A, good a
  apply List.foldlRecOn (motive := fun xs => ∀ a ∈ xs, good a) _ _ hA
  intro acc hacc a ha
  split
  · exact hacc
  · intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hacc a' hm
    · have he := List.mem_singleton.mp hm
      subst a'
      exact blocks a (List.mem_filter.mp ha).1

/-- DC counterpart: none (stored row origin helper).
A pool row or a stored proposal row of any node has honest-holder origin. -/
theorem store_wire_origin (hU : V2.UnforgeableSignatures E rho) (i : Nat) (x : V)
    (a : RowWire p.n)
    (ha : a ∈ (V2.Run.stateBefore E rho i x).st.rowPool ∨
      ∃ w ∈ (V2.Run.stateBefore E rho i x).st.proposals, ∃ s b raw sup rows,
        w.decode = some (.block s b raw sup rows) ∧ a ∈ rows) :
    ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a := by
  intro z hz hzh
  have hh := ((rowSigner_iff_holder p c rho a z).mp hz).2
  have carried (o : Obj p) (t : Time) (hp : V2.Run.processes rho x o t)
      (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
      (ho : o.payload = Msg.proposal b raw sup rows) (har : a ∈ rows) :
      EmitsRow p c E rho z a := by
    have hc : (fgsa p c).carries o (ofRow p a) := by
      change carriesS p o (ofRow p a)
      unfold carriesS
      rw [ho]
      exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, har, rfl⟩))
    obtain ⟨t', _, k, hk, hem⟩ := fgsa_carried_row E rho hU x z o t hp a hc hzh hh
    exact ⟨k, t', hk, hem⟩
  rcases ha with hm | ⟨w, hw, s, b, raw, sup, rows, hd, har⟩
  · obtain ⟨j, t, _, ⟨o', hd, hhs⟩, _⟩ := rowPool_provenance E rho i x a hm
    change handlesS p (V2.Run.stateBefore E rho j x).st o' (ofRow p a) at hhs
    unfold handlesS at hhs
    rcases hhs with he | hb
    · subst he
      obtain ⟨t', _, k, hk, hem⟩ := hU.unforgeable x (ofRow p a) t ⟨j, hd⟩ z hzh hh
      exact ⟨k, t', hk, hem⟩
    · cases hdec : (toWire p o').decode with
      | none => rw [hdec] at hb; exact hb.elim
      | some m =>
        cases m with
        | vote s i b => rw [hdec] at hb; exact hb.elim
        | row r i body => rw [hdec] at hb; exact hb.elim
        | block s b raw sup rows =>
          rw [hdec] at hb
          have hw := decode_eq_block.mp hdec
          have hpay : o'.payload = Msg.proposal b raw sup rows := congrArg (·.payload) hw
          have hc : (fgsa p c).carries o' (ofRow p a) := by
            change carriesS p o' (ofRow p a)
            unfold carriesS
            rw [hpay]
            rcases hb.2 with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          obtain ⟨t', _, k, hk, hem⟩ :=
            fgsa_carried_row E rho hU x z o' t ⟨j, hd⟩ a hc hzh hh
          exact ⟨k, t', hk, hem⟩
  · obtain ⟨j, o, t, _, hdj, hwo, _, _⟩ := stored_proposal_delivered E rho i x w hw
    have hw' := decode_eq_block.mp hd
    have hpay : o.payload = Msg.proposal b raw sup rows := by
      have := congrArg (·.payload) (hwo.trans hw')
      exact this
    exact carried o t ⟨j, hdj⟩ b raw sup rows hpay har

/-- All-run carriage, EMITTED case: a proposal emitted at an honest tick has a
stored parent and rows from the pool or from stored proposal wires.
DC DecoupledConsensusProofs/Protocol/Handlers/StoreBridge.lean:376
(carriedByHonest_of_runBlock), emitted case. -/
theorem emitted_runBlock_carriage (hv : V2.ExecutionValid E rho)
    (x : V) (o : Obj p) (t : Time) (hem : V2.Run.emits E rho x o t)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o.payload = Msg.proposal b raw sup rows)
    (K : FGBlock (Fin p.n)) (hK : Block.Preceq (eraseFG K) b) :
    FinalityCarriage p c E rho (chainRows K) := by
  obtain ⟨i, hi, ho'⟩ := hem
  have hxh : x ∈ rho.honest := hv.honest_only _ (List.mem_of_getElem? hi)
  rw [(V2.Run.step_tick_eq E rho hi).2] at ho'
  obtain ⟨auth, m⟩ := o
  change m = _ at ho
  subst ho
  cases auth with
  | none =>
    exfalso
    change (⟨.none, _⟩ : Obj p) ∈ (if E.awake x t then
      (duties p t).flatMap (fun l => (rho.ownSeats l x).filterMap (fun j =>
        ((fgsa p c).act ((fgsa p c).clock (V2.Run.stateBefore E rho i x) t) l
          (rho.input x t)).map (fun m => ⟨.seat l j, m⟩))) ++ [] else []) at ho'
    split at ho'
    · rw [List.append_nil] at ho'
      obtain ⟨l, _, hm⟩ := List.mem_flatMap.mp ho'
      obtain ⟨j, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m', _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    · exact List.not_mem_nil ho'
  | seat l j =>
    have ha := (V2.Engine.mem_tick_seat_iff E rho _ x t l j _).mp ho'
    cases l with
    | base l =>
      cases l with
      | head s => have := Option.some.inj ha.2.2.2; cases this
      | fg r => have := Option.some.inj ha.2.2.2; cases this
    | prop s =>
      have ht : SA.proposalTime p.toParams s = t := ha.2.1
      subst ht
      let st := FGSA.clock p (V2.Run.stateBefore E rho i x).st (SA.proposalTime p.toParams s)
      have hm : (propose p st s).map
          (withApp (c.app (rho.input x (SA.proposalTime p.toParams s)))) =
          some (.proposal b raw sup rows) := ha.2.2.2
      have hs0 : s ≠ 0 := by
        intro h0
        subst h0
        cases hm
      let H := getHead p st (proposerVotes st s) (proposerSupport st s)
      let R := proposalRows p st H
      let a := c.app (rho.input x (SA.proposalTime p.toParams s))
      have hshape : Msg.proposal (Block.node H s (packBody a R))
          ((proposerVotes st s).filterMap liftHead?)
          ((proposerSupport st s).filterMap liftHead?) R = .proposal b raw sup rows := by
        change (if s = 0 then none else some (Msg.proposal (.node H s (packBody 0 R))
          ((proposerVotes st s).filterMap liftHead?)
          ((proposerSupport st s).filterMap liftHead?) R)).map (withApp a) = _ at hm
        rw [ite_eq_right hs0] at hm
        exact Option.some.inj hm
      obtain ⟨hb, -, -, hrows⟩ := Msg.proposal.inj hshape
      subst hb
      subst hrows
      have hbundle := storeBundle_postClock E rho i x (SA.proposalTime p.toParams s)
      have hH : H ∈ st.base.blocks := getHead_stored p st hbundle.cstore _ _
      obtain ⟨P, hPT, hPe⟩ := (hbundle.cstore.baseTree H).mp hH
      have hPT' : P ∈ (storeAt p c E rho i x).fg.TF := by
        have := clock_fg p (V2.Run.stateBefore E rho i x).st (SA.proposalTime p.toParams s)
        change P ∈ st.fg.TF at hPT
        change P ∈ (V2.Run.stateBefore E rho i x).st.fg.TF
        rw [← this]
        exact hPT
      have hcarP : FinalityCarriage p c E rho (chainRows P) :=
        held_chain_row_origin p c E rho hv.toUnforgeableSignatures i x P ⟨hxh, hPT'⟩
      have hcarTop : FinalityCarriage p c E rho (R.filterMap RowWire.toRow?).toFinset := by
        intro u hu
        obtain ⟨w, hwR, hwu⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hu)
        have auth : ∃ r, w.auth = .seat (.fg r) u.signer := by
          rcases w with ⟨auth, payload⟩
          cases auth with
          | none => cases hwu
          | proposer s => cases hwu
          | seat label i =>
              cases label with
              | head s => cases hwu
              | fg r =>
                  have he : (⟨i, payload.height_pair, payload.finality_pair⟩ : Row (Fin p.n)) = u :=
                    Option.some.inj hwu
                  exact ⟨r, by rw [← he]⟩
        obtain ⟨r, hwr⟩ := auth
        refine ⟨w, r, hwu, hwr, ?_⟩
        apply store_wire_origin p c E rho hv.toUnforgeableSignatures i x w
        rcases proposalRows_source p st H w hwR with hpool | hprop
        · left
          rw [← clock_rowPool p _ (SA.proposalTime p.toParams s)]
          exact hpool
        · right
          rw [← clock_proposals p _ (SA.proposalTime p.toParams s)]
          exact hprop
      have hrok : rowsOk (Block.node H s (packBody a R)) R = true := by
        change (packBody a R == packBody (appOf (packBody a R)) R) = true
        rw [appOf_packBody]
        exact beq_self_eq_true _
      have htop : eraseFG (fgBlock P (Block.node H s (packBody a R)) R) =
          Block.node H s (packBody a R) :=
        eraseFG_fgBlock (by intro h; cases h) hPe R hrok
      change (decide (eraseFG K = Block.node H s (packBody a R)) ||
        Block.preceq (eraseFG K) H) = true at hK
      rcases Bool.or_eq_true_iff.mp hK with he | hpre
      · have hKe : K = fgBlock P (Block.node H s (packBody a R)) R :=
          eraseFG_injective ((of_decide_eq_true he).trans htop.symm)
        subst hKe
        intro u hu
        change u ∈ (R.filterMap RowWire.toRow?).toFinset ∪ chainRows P at hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact hcarTop u hu
        · exact hcarP u hu
      · rw [← hPe] at hpre
        have hKP : FGBlock.Preceq K P := ((fgsa_carrier_geometry K P).2.1).mpr hpre
        intro u hu
        exact hcarP u (KitFG.chainRows_mono hKP hu)

/-- ALL-RUN carriage: the premise `hcar` of `fgsa_slashableBound_of_faults`
follows from ExecutionValid, as DC `carriedByHonest_of_runBlock` follows from
AdmissibleCore (DecoupledConsensusProofs/Protocol/Handlers/StoreBridge.lean:376). -/
theorem fgsa_runBlock_carriage (hv : V2.ExecutionValid E rho) :
    ∀ K, FinalityRunBlock p c E rho K → FinalityCarriage p c E rho (chainRows K) := by
  rintro K ⟨o, b, raw, sup, rows, ho, (⟨x, t, hem⟩ | ⟨x, t, hd⟩), hK⟩
  · exact emitted_runBlock_carriage p c E rho hv x o t hem b raw sup rows ho K hK
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hd
    exact delivered_runBlock_carriage p c E rho hv i x o t hi b raw sup rows ho K hK

/-- The all-run bound from BaseSet and the fault bound alone.
DC DecoupledConsensusProofs/Protocol/ChainState/AlignedRoundLemmas.lean:284
(slashableBound_of_belowOneThird), with carriage from StoreBridge.lean:376.
INTENTIONAL: Linked transports rotating seats to holders (SYN L41).
BaseSet retains noRestart, delta and cstar; these fields are unused here. -/
theorem fgsa_slashableBound_of_base [Fintype V] (hb : BaseSet p c E rho)
    (hbot : (Gen.V2.faulty rho).card ≤ (p.n - 1) / 3) :
    FGSASlashableBound p c E rho :=
  fgsa_slashableBound_of_faults p c E rho hb.linked hbot
    (fgsa_clientSafeAll p c E rho hb.linked)
    (fgsa_runBlock_carriage p c E rho hb.valid)



end AvailableChain.FGSA.Run
end
