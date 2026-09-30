module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainGeneric.Proofs.V2.Linked
public import AvailableChainGeneric.Statements.V2.Counts

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- The accepted certificate height at a store read: zero for genesis,
otherwise `h_F` of a held carrier supplied by the store invariant.
This selects an existing certificate; it adds no store field. -/
noncomputable def fgsa_finheight (e : Nat) (x : V) : Nat :=
  if (storeAt p c E rho e x).fg.F = .genesis then 0
  else (derive p.E p.cfg
    (Classical.choose (storeBundle_stateBefore E rho e x).cstore.fg.Fcar)).h_F

/-- Strict R-XING (01 §1.3), the run form of `fg.finalLock.v2`.
The held block can be outside the active view. Identity transport precedes
application of `FaultX`. The proof also permits an earlier held read. -/
theorem fgsa_finalLock [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.faulty rho).card)
    (hU : V2.UnforgeableSignatures E rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (x : V) (hx : x ∈ rho.honest) (e e' : Nat) (_hee : e ≤ e')
    (y : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e' y W)
    (hh : fgsa_finheight p c E rho e x < hOf p.E p.cfg W) :
    FGBlock.Preceq (storeAt p c E rho e x).fg.F W := by
  classical
  by_cases hg : (storeAt p c E rho e x).fg.F = .genesis
  · rw [hg]
    exact KitFG.genesis_preceq W
  let hc := (storeBundle_stateBefore E rho e x).cstore.fg.Fcar
  let K := Classical.choose hc
  have hK := Classical.choose_spec hc
  change K ∈ (storeAt p c E rho e x).fg.TF ∧
    (derive p.E p.cfg K).F = (storeAt p c E rho e x).fg.F at hK
  have hheight : (derive p.E p.cfg K).h_F < (derive p.E p.cfg W).h := by
    change (if (storeAt p c E rho e x).fg.F = .genesis then 0
      else (derive p.E p.cfg K).h_F) < (derive p.E p.cfg W).h at hh
    rw [ite_eq_right hg] at hh
    exact hh
  rcases KitFG.slashableWeight_or_finalized_preceq p.E p.cfg K W hheight with hev | hF
  · obtain ⟨S, hw, hs⟩ := hev
    have hcard := Gen.V2.linked_card_le_of_holders hL (S.image Fin.val)
      (Gen.V2.faulty rho) (by
        intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨u, hu, v, hv, hui, hvi, huv⟩ := hs i hi
        obtain ⟨a, r, hau, har, hea⟩ := held_chain_row_origin p c E rho hU e x K
          ⟨hx, hK.1⟩ u hu
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
    have hbound := hX.lt
    omega
  · exact hK.2 ▸ hF

/-- Erasure of strict R-XING to the base block order. -/
theorem fgsa_finalLock_erased [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.faulty rho).card)
    (hU : V2.UnforgeableSignatures E rho)
    (hC : ∀ z ∈ rho.honest, EmittedRowsNoSlash p c E rho z)
    (x : V) (hx : x ∈ rho.honest) (e e' : Nat) (hee : e ≤ e')
    (y : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e' y W)
    (hh : fgsa_finheight p c E rho e x < hOf p.E p.cfg W) :
    Block.Preceq (eraseFG (storeAt p c E rho e x).fg.F) (eraseFG W) :=
  eraseFG_preceq (fgsa_finalLock p c E rho hL hX hU hC x hx e e' hee y W hW hh)

end AvailableChain.FGSA.Run
end
