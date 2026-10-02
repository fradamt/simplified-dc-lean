module
public import AvailableChainKitFG.Accountable
public import AvailableChainKitFG.CertificateCoreDef

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Finality is on the carrier chain, by the record's anchor order. -/
theorem finalized_preceq_chain_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B : FGBlock V) : FGBlock.Preceq (f B).F B :=
  preceq_trans (hc.finalized_preceq_justified B)
    (preceq_trans (hc.height.justified_preceq_entry B) (hc.height.entry_preceq B))

/-- A finalized height is below the carrier's current height. -/
theorem finalized_below_height_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B : FGBlock V) : (f B).h_F < (H B).h :=
  Nat.lt_of_le_of_lt (hc.heights_ordered B) (hc.height.justified_below_height B)

/-- Extract the exact historical QC. No current bit set or selection list is read. -/
theorem finality_certificate_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D : FGBlock V) (hnz : (f D).h_F ≠ 0) :
    ∃ F : FGBlock V, FGBlock.Preceq F D ∧ F = (f D).F ∧
      ∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier : FGBlock V, ∃ a : Row V,
          FGBlock.Preceq carrier D ∧ a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨(f D).h_F, F.root⟩ := by
  obtain ⟨C, W, _, hWD, _, _, _, Q, hQ, hw⟩ := hc.finality_origin D hnz
  refine ⟨(f D).F, finalized_preceq_chain_of_certificate E H f hc D, rfl, Q, hQ, ?_⟩
  intro i hi
  obtain ⟨carrier, a, _, hcarrier, ha, hai, hpair⟩ := hw i hi
  exact ⟨carrier, a, preceq_trans hcarrier hWD, ha, hai, hpair⟩

/-- Height-law form of `justification_certificate_rows`. -/
theorem justification_certificate_rows_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (hH : FGHeightLaws E H) (D : FGBlock V)
    (hnz : (H D).h_j ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ a ∈ chainRows D, a.signer = i ∧
      a.height_pair = .vote (H D).h_j (H D).J.root false := by
  obtain ⟨Q, hQ, hw⟩ := hH.justification_certificate D hnz
  refine ⟨Q, hQ, fun i hi => ?_⟩
  obtain ⟨carrier, a, hc, ha, hai, hpa⟩ := hw i hi
  exact ⟨a, mem_chainRows_of_carrier hc ha, hai, hpa⟩

/-- Shared record form of `slashableWeight_or_justified_eq`. -/
theorem slashableWeight_or_justified_eq_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f) (B₁ B₂ : FGBlock V)
    (hh : (H B₁).h_j = (H B₂).h_j) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      (H B₁).J = (H B₂).J := by
  by_cases hz : (H B₁).h_j = 0
  · refine Or.inr ?_
    rw [hc.justified_zero B₁ hz,
      hc.justified_zero B₂ (hh.symm.trans hz)]
  · by_cases hr : (H B₁).J.root = (H B₂).J.root
    · exact Or.inr (FGBlock.root_injective hr)
    · obtain ⟨Q₁, hQ₁, hw₁⟩ :=
        justification_certificate_rows_of_heightLaws E H hc.height B₁ hz
      obtain ⟨Q₂, hQ₂, hw₂⟩ :=
        justification_certificate_rows_of_heightLaws E H hc.height B₂ (hh ▸ hz)
      rw [← hh] at hw₂
      exact Or.inl (uniqueJust_slashable E hr hQ₁ hQ₂ hw₁ hw₂)

/-- Shared record form of `e1Weight_or_finalized_preceq`. -/
theorem e1Weight_or_finalized_preceq_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f) (B W : FGBlock V)
    (hh : (f B).h_F < (H W).h) :
    HasE1WeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (f B).F W := by
  by_cases hz : (f B).h_F = 0
  · refine Or.inr ?_
    rw [hc.finalized_zero B hz]
    exact genesis_preceq W
  · obtain ⟨F, -, rfl, Qf, hQf, hwf⟩ := finality_certificate_of_certificate E H f hc B hz
    obtain ⟨X, hXW, -, Qc, hQc, hwc⟩ :=
      hc.height.height_crossing W _ (Nat.one_le_iff_ne_zero.mpr hz) hh
    by_cases hr : X.root = (f B).F.root
    · refine Or.inr ?_
      rw [← FGBlock.root_injective hr]
      exact hXW
    · refine Or.inl ⟨Qf ∩ Qc, quorum_intersection E hQf hQc, fun i hi => ?_⟩
      obtain ⟨hf, hc⟩ := Finset.mem_inter.mp hi
      obtain ⟨cB, b, hcB, hb, hbi, hbf⟩ := hwf i hf
      obtain ⟨cW, a, hcW, ha, hai, ham⟩ := hwc i hc
      exact ⟨b, mem_chainRows_of_carrier hcB hb, a, mem_chainRows_of_carrier hcW ha, hbi, hai,
        e1Slashable_of_matchesEntry b a _ X.root _ (hbi.trans hai.symm) hbf ham hr⟩

/-- Shared record form of `slashableWeight_or_finalized_preceq`. -/
theorem slashableWeight_or_finalized_preceq_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f) (B W : FGBlock V)
    (hh : (f B).h_F < (H W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (f B).F W :=
  (e1Weight_or_finalized_preceq_of_certificate E H f hc B W hh).imp
    hasSlashableWeightBetween_of_hasE1WeightBetween id

/-- Shared record form of `e1Weight_or_finalized_compatible_of_le`. -/
theorem e1Weight_or_finalized_compatible_of_le_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B₁ B₂ : FGBlock V)
    (hle : (f B₁).h_F ≤ (f B₂).h_F) :
    HasE1WeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (f B₁).F (f B₂).F = true := by
  have hlt : (f B₁).h_F < (H B₂).h :=
    Nat.lt_of_le_of_lt hle (finalized_below_height_of_certificate E H f hc B₂)
  rcases e1Weight_or_finalized_preceq_of_certificate E H f hc B₁ B₂ hlt with hev | hF
  · exact Or.inl hev
  · exact Or.inr (compatible_of_preceq_common hF
      (finalized_preceq_chain_of_certificate E H f hc B₂))

/-- Shared record form of `slashableWeight_or_finalized_compatible`. -/
theorem slashableWeight_or_finalized_compatible_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B₁ B₂ : FGBlock V) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (f B₁).F (f B₂).F = true := by
  rcases Nat.le_total (f B₁).h_F (f B₂).h_F with hle | hle
  · exact (e1Weight_or_finalized_compatible_of_le_of_certificate E H f hc B₁ B₂ hle).imp
      hasSlashableWeightBetween_of_hasE1WeightBetween id
  · rcases e1Weight_or_finalized_compatible_of_le_of_certificate E H f hc B₂ B₁ hle with hev | hc
    · exact Or.inl (hasSlashableWeightBetween_of_hasE1WeightBetween_swap hev)
    · exact Or.inr ((compatible_comm _ _).trans hc)

end AvailableChain.KitFG
end
