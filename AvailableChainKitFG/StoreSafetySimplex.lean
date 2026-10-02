module
public import AvailableChainKitFG.StoreSafety
public import AvailableChainKitFG.AccountableSimplex
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Project the existing SimplexFG store invariant into the shared structure. -/
theorem simplexStoreInvariant (E : Electorate V) (cfg : FGConfig) (st : Store V)
    (hi : StoreInv E cfg st) :
    FGStoreInvariant (simplexHeightView E cfg) (simplexFinalityView E cfg) st := by
  refine ⟨hi.closed, hi.gen, hi.Fmem, hi.hmax, ?_, hi.FJ, hi.Fcar⟩
  obtain ⟨D, hD, hDF⟩ := hi.Fcar
  have hDJ : FGBlock.Preceq st.F (derive E cfg D).J :=
    hDF ▸ derive_F_preceq_J E cfg D
  obtain ⟨C, hC, hFC, hpair, hmax⟩ :=
    lexMax_spec E cfg st.F st.TF (viewRootInj_all _) ⟨D, hD, hDJ⟩
  have heq := hi.pair.trans hpair
  refine ⟨⟨C, hC, hFC, congrArg Prod.fst heq, congrArg Prod.snd heq⟩, ?_⟩
  intro B hB hFB
  change lexKey ((derive E cfg B).h_j, (derive E cfg B).J) ≤ lexKey (st.h_j, st.J)
  rw [heq]
  exact hmax B hB hFB

/-- The SimplexFG store uses its existing step and a computed immutable cache. -/
theorem simplexStoreSafety (E : Electorate V) (cfg : FGConfig) :
    FGStoreSafety E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (id : Store V → Store V)
      (fun _ B => (simplexHeightView E cfg B, simplexFinalityView E cfg B))
      Store.init (on_block E cfg) (StoreInv E cfg) :=
  FGStoreSafety.of_certificate E _ _ (simplexCertificateLaws E cfg)
    id _ Store.init (on_block E cfg) (StoreInv E cfg)
    (storeInv_init E cfg) (simplexStoreInvariant E cfg)
    (fun st B hi => storeInv_on_block E cfg st B hi (fun _ => viewRootInj_all _))
    (fun st B _ => on_block_TF_subset E cfg st B)
    (fun st B _ => on_block_F_mono E cfg st B) (fun _ _ _ _ => rfl)

end AvailableChain.KitFG
end
