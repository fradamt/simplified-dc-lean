module
public import AvailableChainFGSA.Proofs.WindowCertificates
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainKitFG.CrossingCore

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.KitFG

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_entry (p : Params) (K : Nat) (hK : 2 ≤ K)
    (Λ : Record) (C : FGBlock (Fin p.n)) (fp : Option FinalityPair)
    (h : Height) (T : BlockId) (t : Bool)
    (hemit : height_pair Λ
      (some ((certificateHeight p K C).h, (certificateHeight p K C).T_h.root)) fp = .vote h T t) :
    h = (certificateHeight p K C).h ∧ T = (certificateHeight p K C).T_h.root ∧
      FGBlock.Preceq (certificateHeight p K C).T_h C :=
  provenance_entry_of_heightLaws p.E (certificateHeight p K) (windowHeightLaws p K hK)
    Λ C fp h T t hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_finalityRow (p : Params) (K : Nat) (hK : 2 ≤ K)
    (Λ : Record) (Hd : FGBlock (Fin p.n)) (pair : FinalityPair)
    (hemit : finality_pair Λ (certificateHeadFields (certificateHeight p K)
      (certificateFinality p K) Hd) = some pair) :
    pair.height = (certificateHeight p K Hd).h_j ∧ pair.target = (certificateHeight p K Hd).J.root ∧
      (certificateFinality p K Hd).h_F < pair.height ∧ TargetQCAt p.E Hd pair.height
      (certificateHeight p K Hd).J :=
  provenance_finalityRow_of_heightLaws p.E (certificateHeight p K) (certificateFinality p K)
    (windowHeightLaws p K hK) Λ Hd pair hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_provenance_finalityQC (p : Params) (K : Nat) (hK : 2 ≤ K)
    (faulty : Finset (Fin p.n)) (hcap : p.E.weightOf faulty < p.E.q)
    (rows : Finset (Row (Fin p.n))) (Q : Finset (Fin p.n))
    (hQ : p.E.IsQuorum Q) (pair : FinalityPair)
    (hrows : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some pair)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some pair →
      ∃ Λ Hd, finality_pair Λ (certificateHeadFields (certificateHeight p K)
      (certificateFinality p K) Hd) = some pair) :
    ∃ Hd, pair.height = (certificateHeight p K Hd).h_j ∧
      pair.target = (certificateHeight p K Hd).J.root ∧
      TargetQCAt p.E Hd pair.height (certificateHeight p K Hd).J :=
  provenance_finalityQC_of_heightLaws p.E (certificateHeight p K) (certificateFinality p K)
    (windowHeightLaws p K hK) faulty hcap rows Q hQ pair hrows hemit

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_exists_crossing_quorum_ne_justified (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B W : FGBlock (Fin p.n))
    (hJ : (certificateHeight p K B).h_j ≠ 0)
    (hW : (certificateHeight p K B).h_j < (certificateHeight p K W).h)
    (hnot : ¬ FGBlock.Preceq (certificateHeight p K B).J W) :
    ∃ X : FGBlock (Fin p.n), X.root ≠ (certificateHeight p K B).J.root ∧
      ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (certificateHeight p K B).h_j X.root = true :=
  exists_crossing_quorum_ne_justified_of_heightLaws p.E (certificateHeight p K)
    (windowHeightLaws p K hK) B W hJ hW hnot

/-- Window views supply the height laws; all client premises stay explicit. -/
theorem window_exists_honest_timeout_of_crossing (p : Params) (K : Nat) (hK : 2 ≤ K)
    (faulty : Finset (Fin p.n))
    (B W : FGBlock (Fin p.n))
    (hcap : p.E.weightOf faulty + p.E.totalWeight < 2 * p.E.q)
    (hJ : (certificateHeight p K B).h_j ≠ 0)
    (hW : (certificateHeight p K B).h_j < (certificateHeight p K W).h)
    (hnot : ¬ FGBlock.Preceq (certificateHeight p K B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (certificateHeight p K B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair =
          .vote (certificateHeight p K B).h_j (certificateHeight p K B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair = .vote (certificateHeight p K B).h_j X true) :=
  exists_honest_timeout_of_crossing_of_heightLaws p.E (certificateHeight p K)
    (windowHeightLaws p K hK)
    faulty B W hcap hJ hW hnot hhonest

/-- Honest votes name only the latest pair; an older retained entry gains bits
only from stale-arm rows emitted earlier (R6W StaleUseful). The head read is
independent of the retained entries. Emission also checks the client record. -/
theorem window_headFields_latest (p : Params) (K : Nat)
    (Hd : FGBlock (Fin p.n)) (Λ : Record) :
    certificateHeadFields (certificateHeight p K) (certificateFinality p K) Hd =
      ⟨(derive p K Hd).h_j, (derive p K Hd).J.root, (derive p K Hd).h_F⟩ ∧
    finality_pair Λ (certificateHeadFields (certificateHeight p K) (certificateFinality p K) Hd) =
      (if (derive p K Hd).h_F < (derive p K Hd).h_j ∧
          (Λ.target (derive p K Hd).h_j = none ∨
            Λ.target (derive p K Hd).h_j = some (derive p K Hd).J.root) ∧
          Λ.timeout (derive p K Hd).h_j = false ∧
          (Λ.lock (derive p K Hd).h_j = none ∨
            Λ.lock (derive p K Hd).h_j = some (derive p K Hd).J.root) then
        some ⟨(derive p K Hd).h_j, (derive p K Hd).J.root⟩ else none) := by
  exact ⟨rfl, rfl⟩

end AvailableChain.FGSA.Window
end
