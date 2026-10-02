module
public import AvailableChainKitFG.ProvenanceCore

public section

namespace AvailableChain.KitFG.Tests.ProvenanceCore

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- The existing honest-row statement needs no concrete fold or client.
omit [DecidableEq V] [RowCodec V] in
theorem provenance_generic_honest_row_test (E : Electorate V) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (rows : Finset (Row V)) (Q : Finset V)
    (hQ : E.IsQuorum Q) (hw : ∀ i ∈ Q, ∃ a ∈ rows, a.signer = i) :
    ∃ a ∈ rows, a.signer ∉ faulty :=
  provenance_honestRow E faulty hcap rows Q hQ hw

-- A released pair at or below current finality cannot satisfy emission.
theorem provenance_stale_emission_rejected_test (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (Λ : Record) (Hd : FGBlock V) (p : FinalityPair) (hstale : p.height ≤ (f Hd).h_F) :
    finality_pair Λ (certificateHeadFields H f Hd) ≠ some p := by
  intro hemit
  have h := (provenance_finalityRow_of_certificate E H f hc Λ Hd p hemit).2.2.1
  exact (Nat.not_lt_of_ge hstale) h

-- Use the bundle and the explicit released-pair premise for QC provenance.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hc : FGChainCertificate E H f r)
    (faulty : Finset V) (hcap : E.weightOf faulty < E.q)
    (rows : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q) (p : FinalityPair)
    (hw : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some p)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some p →
      ∃ Λ Hd, finality_pair Λ (certificateHeadFields H f Hd) = some p) :
    ∃ Hd, p.height = (H Hd).h_j ∧ p.target = (H Hd).J.root ∧
      TargetQCAt E Hd p.height (H Hd).J :=
  provenance_finalityQC_of_certificate E H f hc.laws faulty hcap rows Q hQ p hw hemit

private def pcFinalOne : FGBlock (Fin 4) :=
  .node B1 2 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

-- The same pair is emitted at B1 and rejected after it has finalized.
private theorem provenance_stale_head_fixture_test :
    finality_pair Record.initial
        (certificateHeadFields (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) B1) =
      some ⟨1, genesisRoot⟩ ∧
    finality_pair Record.initial
        (certificateHeadFields (simplexHeightView E4 cfg1)
          (simplexFinalityView E4 cfg1) pcFinalOne) = none := by decide

-- Genesis at height zero cannot stand for the emitted height-one key.
example : finality_pair Record.initial
    (certificateHeadFields (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) B1) ≠
      some ⟨0, genesisRoot⟩ := by decide

-- A prior timeout also prevents finality emission.
example : finality_pair (Record.initial.with_timeout 1)
    (certificateHeadFields (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) B1) =
      none := by decide

-- The field-level entry companion accepts the projected source directly.
example : (1 : Height) = (simplexHeightView E4 cfg1 .genesis).h ∧
    genesisRoot = (simplexHeightView E4 cfg1 .genesis).T_h.root ∧
    FGBlock.Preceq (simplexHeightView E4 cfg1 .genesis).T_h .genesis :=
  provenance_entry_of_certificate E4 _ _ (simplexCertificateLaws E4 cfg1)
    Record.initial .genesis none 1 genesisRoot false (by decide)

#print axioms provenance_honestRow
#print axioms provenance_generic_honest_row_test
#print axioms provenance_stale_emission_rejected_test
#print axioms provenance_stale_head_fixture_test

#print axioms certificateHeadFields_def
#print axioms provenance_entry_of_certificate
#print axioms provenance_finalityRow_of_certificate
#print axioms provenance_finalityQC_of_certificate
#print axioms provenance_finality_of_certificate
#print axioms provenance_entry_simplex_certificate
#print axioms provenance_finalityRow_simplex_certificate
#print axioms provenance_finalityQC_simplex_certificate
#print axioms provenance_finality_simplex_certificate

end AvailableChain.KitFG.Tests.ProvenanceCore
end
