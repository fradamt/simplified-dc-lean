module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainFGSAProofs.Proofs.Foundations.Client
public import AvailableChainGeneric.Proofs.V2.Linked

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

/-- Honest carriage is separate from weight-level evidence. -/
def FinalityCarriage (A : Finset (Row (Fin p.n))) : Prop :=
  ∀ u ∈ A, ∃ (a : RowWire p.n) (r : Nat),
    a.toRow? = some u ∧ a.auth = .seat (.fg r) u.signer ∧
    ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a

/-- Run-free accountable finality. Root injectivity is automatic in FG-SA;
the explicit scoped premise keeps the DC interface visible. -/
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

/-- DC SlashableBound: no slashable weight between two run certificates.
This bounds accountable evidence, not the total faulty weight. -/
def FGSASlashableBound : Prop :=
  ∀ K W, FinalityRunBlock p c E rho K → FinalityRunBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)

private theorem stored_finality_delivery (i : Nat) (x : V) (K : FGBlock (Fin p.n))
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hne : K ≠ .genesis) :
    ∃ o raw sup rows y t, o.payload = Msg.proposal (eraseFG K) raw sup rows ∧
      V2.Event.deliver y o t ∈ rho.events := by
  have hs := storeBundle_stateBefore E rho i x
  obtain ⟨slot, raw, sup, wires, hw, _⟩ := stored_wire_of_block p _ hs.cstore hs.«meta» hK hne
  obtain ⟨j, o, t, _, hd, ho, _, _⟩ := stored_proposal_delivered E rho i x _ hw
  have he : o = ofWire p ⟨.proposer slot, .proposal (eraseFG K) raw sup wires⟩ := by
    apply toWire_injective
    rw [toWire_ofWire, ho]
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

/-- DC WholeRunFinalitySafety with the same chain-scoped SlashableBound.
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

/-- DC's fault-to-slashable-bound bridge keeps honest carriage explicit.
Linked transports identities; client safety rules out honest E1/E2 pairs. -/
theorem fgsa_slashableBound_of_faults [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.faulty rho).card)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (hcar : ∀ K, FinalityRunBlock p c E rho K → FinalityCarriage p c E rho (chainRows K)) :
    FGSASlashableBound p c E rho := by
  intro K W hK hW hev
  have hc := slashable_pool_count p c E rho hL hC _ _ (hcar K hK) (hcar W hW) hev
  have ht := hX.lt
  omega

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
Honesty and held membership describe the observations only; no behaviour is assumed. -/
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

/-- BaseSet discharges both attribution inputs. -/
theorem fgsa_accountable_base [Fintype V] (hb : BaseSet p c E rho)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true ∨
      2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card :=
  fgsa_accountable p c E rho hb.linked (fgsa_unforgeable_of_base p c E rho hb) e e' x y hx hy

end AvailableChain.FGSA.Run
end
