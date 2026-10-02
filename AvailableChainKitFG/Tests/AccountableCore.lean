module
public import AvailableChainKitFG.AccountableCore

public section

namespace AvailableChain.KitFG.Tests.AccountableCore

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- The complete chain certificate supplies the shared safety core.
theorem accountable_certificate_bundle_test (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (r : FGSelectionView V)
    (hc : FGChainCertificate E H f r) (B₁ B₂ : FGBlock V) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (f B₁).F (f B₂).F = true :=
  accountable_of_certificate E H f hc.laws B₁ B₂

-- The safety argument needs no selection, retention, capacity, or timing premise.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (B W : FGBlock V)
    (hh : (f B).h_F < (H W).h) (hfork : ¬ FGBlock.Preceq (f B).F W) :
    HasE1WeightBetween E (chainRows B) (chainRows W) :=
  (e1Weight_or_finalized_preceq_of_certificate E H f hc B W hh).resolve_right hfork

-- Unequal justified blocks at one height give slashable evidence.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (B₁ B₂ : FGBlock V)
    (hh : (H B₁).h_j = (H B₂).h_j) (hne : (H B₁).J ≠ (H B₂).J) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) :=
  (slashableWeight_or_justified_eq_of_certificate E H f hc B₁ B₂ hh).resolve_right hne

-- The exact finality QC remains available when before has no retained entry.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hc : FGChainCertificate E H f r)
    (B : FGBlock V) (_hempty : r.before B = []) (hnz : (f B).h_F ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q,
      ∃ a ∈ chainRows B, a.signer = i ∧
        a.finality_pair = some ⟨(f B).h_F, (f B).F.root⟩ := by
  obtain ⟨_, _, rfl, Q, hQ, hw⟩ := finality_certificate_of_certificate E H f hc.laws B hnz
  refine ⟨Q, hQ, fun i hi => ?_⟩
  obtain ⟨carrier, a, hcarrier, ha, hai, hpair⟩ := hw i hi
  exact ⟨a, mem_chainRows_of_carrier hcarrier ha, hai, hpair⟩

-- The zero-finality case gives genesis ancestry directly.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (B W : FGBlock V) (hz : (f B).h_F = 0) :
    FGBlock.Preceq (f B).F W := by
  rw [hc.finalized_zero B hz]
  exact genesis_preceq W

-- The concrete corollaries use the LF2 instance and keep the concrete chain types.
example (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  finalLock_simplex_certificate E cfg B W hh

example (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true :=
  accountable_simplex_certificate E cfg B₁ B₂

-- Both certificate keys for genesis reach the shared records.
example : (simplexFinalityView E4 cfg1 .genesis).h_F = 0 ∧
    (simplexHeightView E4 cfg1 B1).h_j = 1 := by decide

#print axioms accountable_certificate_bundle_test
#print axioms finalized_preceq_chain_of_certificate
#print axioms finalized_below_height_of_certificate
#print axioms finality_certificate_of_certificate
#print axioms justification_certificate_rows_of_certificate
#print axioms slashableWeight_or_justified_eq_of_certificate
#print axioms uniqueJust_chains_of_certificate
#print axioms e1Weight_or_finalized_preceq_of_certificate
#print axioms finalLock_e1_of_certificate
#print axioms slashableWeight_or_finalized_preceq_of_certificate
#print axioms finalLock_of_certificate
#print axioms e1Weight_or_finalized_compatible_of_le_of_certificate
#print axioms accountable_oriented_of_certificate
#print axioms slashableWeight_or_finalized_compatible_of_certificate
#print axioms accountable_of_certificate
#print axioms justification_certificate_rows_simplex_certificate
#print axioms slashableWeight_or_justified_eq_simplex_certificate
#print axioms uniqueJust_chains_simplex_certificate
#print axioms e1Weight_or_finalized_preceq_simplex_certificate
#print axioms finalLock_e1_simplex_certificate
#print axioms slashableWeight_or_finalized_preceq_simplex_certificate
#print axioms finalLock_simplex_certificate
#print axioms e1Weight_or_finalized_compatible_of_le_simplex_certificate
#print axioms accountable_oriented_simplex_certificate
#print axioms slashableWeight_or_finalized_compatible_simplex_certificate
#print axioms accountable_simplex_certificate

end AvailableChain.KitFG.Tests.AccountableCore
end
