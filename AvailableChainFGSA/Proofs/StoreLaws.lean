module
public import AvailableChainFGSA.Statements.FinalityView
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainKitFG.StoreSafetySimplex

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The active height view is still the simplex view. -/
theorem heightView_eq_simplex (p : Params) :
    heightView p = simplexHeightView p.E p.cfg := rfl

/-- The active finality view is still the simplex view. -/
theorem finalityView_eq_simplex (p : Params) :
    finalityView p = simplexFinalityView p.E p.cfg := rfl

/-- Certificate laws for the active model views. J4 replaces this proof. -/
theorem fgCertificateLaws (p : Params) :
    FGCertificateLaws p.E (heightView p) (finalityView p) :=
  simplexCertificateLaws p.E p.cfg

/-- Justification laws for the active height view. -/
theorem fgJustificationLaws (p : Params) : FGJustificationLaws (heightView p) :=
  FGJustificationLaws.of_bridge (heightView_bridge p)

private theorem fgStoreInvariant_to_simplex (p : Params) (st : Store (Fin p.n))
    (hi : FGStoreInvariant (heightView p) (finalityView p) st) :
    StoreInv p.E p.cfg st := by
  refine ⟨hi.closed, hi.gen, hi.Fmem, hi.hmax, ?_, hi.FJ, hi.Fcar⟩
  obtain ⟨C, hC, hFC, hh, hJ⟩ := hi.pair.1
  rw [lexMax_eq_of_greatest p.E p.cfg st.F st.TF (viewRootInj_all _) C hC hFC]
  · exact Prod.ext hh hJ
  · intro W hW hFW
    have hm := hi.pair.2 W hW hFW
    rw [hh, hJ] at hm
    exact hm

/-- The old block step preserves the generic invariant. J4 replaces this proof. -/
theorem fgStoreInvariant_on_block (p : Params) (st : Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (hi : FGStoreInvariant (heightView p) (finalityView p) st) :
    FGStoreInvariant (heightView p) (finalityView p) (on_block p.E p.cfg st B) :=
  simplexStoreInvariant p.E p.cfg _
    (storeInv_on_block p.E p.cfg st B (fgStoreInvariant_to_simplex p st hi)
      (fun _ => viewRootInj_all _))

/-- Store safety uses the generic invariant itself as the good-state predicate. -/
theorem fgStoreSafety (p : Params) :
    FGStoreSafety p.E (heightView p) (finalityView p)
      (id : Store (Fin p.n) → Store (Fin p.n))
      (fun _ B => (heightView p B, finalityView p B))
      Store.init (on_block p.E p.cfg) (FGStoreInvariant (heightView p) (finalityView p)) :=
  FGStoreSafety.of_certificate p.E _ _ (fgCertificateLaws p)
    id _ Store.init (on_block p.E p.cfg) (FGStoreInvariant (heightView p) (finalityView p))
    (simplexStoreInvariant p.E p.cfg _ (storeInv_init p.E p.cfg)) (fun _ hi => hi)
    (fgStoreInvariant_on_block p)
    (fun st B _ => on_block_TF_subset p.E p.cfg st B)
    (fun st B _ => on_block_F_mono p.E p.cfg st B) (fun _ _ _ _ => rfl)

end AvailableChain.FGSA
end
