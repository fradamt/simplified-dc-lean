module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainGeneric.Proofs.V2.Linked
public import AvailableChainGeneric.Statements.V2.Counts

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- Slashable identities on two held chains give distinct faulty holders.
Linked transports row identities before any fault bound is used. -/
theorem fgsa_slashable_faulty_count [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (e e' : Nat) (x y : V) (K W : FGBlock (Fin p.n))
    (hK : HeldAt p c E rho e x K) (hW : HeldAt p c E rho e' y W)
    (hev : HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) :
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card := by
  classical
  obtain ⟨S, hw, hs⟩ := hev
  have hcard := Gen.V2.linked_card_le_of_holders hL (S.image Fin.val)
    (Gen.V2.faulty rho) (by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨u, hu, v, hv, hui, hvi, huv⟩ := hs i hi
      obtain ⟨a, r, hau, har, hea⟩ := held_chain_row_origin p c E rho hU e x K
        hK u hu
      obtain ⟨b, s, hbv, hbs, heb⟩ := held_chain_row_origin p c E rho hU e' y W hW v hv
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

/-- Accountable safety for any two honest store reads, with no fault bound. -/
theorem fgsa_accountable [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true ∨
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card := by
  obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho e x).cstore.fg.Fcar
  obtain ⟨W, hW, hWF⟩ := (storeBundle_stateBefore E rho e' y).cstore.fg.Fcar
  rcases KitFG.slashableWeight_or_finalized_compatible p.E p.cfg K W with hev | hc
  · exact Or.inr (fgsa_slashable_faulty_count p c E rho hL hU hC e e' x y K W
      ⟨hx, hK⟩ ⟨hy, hW⟩ hev)
  · exact Or.inl (hKF ▸ hWF ▸ hc)

/-- Unconditional final lock with an explicit stored certificate carrier.
The held read can have any index; no ordering or fault bound is needed. -/
theorem fgsa_finalLock_ev [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hU : V2.UnforgeableSignatures E rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest)
    (K W : FGBlock (Fin p.n))
    (hK : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (derive p.E p.cfg K).F = (storeAt p c E rho e x).fg.F)
    (hW : HeldAt p c E rho e' y W)
    (hh : (derive p.E p.cfg K).h_F < (derive p.E p.cfg W).h) :
    FGBlock.Preceq (storeAt p c E rho e x).fg.F W ∨
    2 * Gen.Pure.qF p.n - p.n ≤ (Gen.V2.faulty rho).card := by
  rcases KitFG.slashableWeight_or_finalized_preceq p.E p.cfg K W hh with hev | hf
  · exact Or.inr (fgsa_slashable_faulty_count p c E rho hL hU hC e e' x y K W
      ⟨hx, hK⟩ hW hev)
  · exact Or.inl (hKF ▸ hf)

end AvailableChain.FGSA.Run
end
