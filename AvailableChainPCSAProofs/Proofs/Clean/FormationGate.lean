module
public import AvailableChainPCSAProofs.Proofs.Shared.CleanGate
public import AvailableChainFGSA.Proofs.Head.Walk

public section

/-! Formation step 5 on resolved support counts (pcsa34-r4.3 §5.3).
OPEN: derive the path, denominator, rival, and disjoint child counts from
the early honest votes and at most a faulty votes in the PC-SA run.
Use all honest HEAD senders for h, including senders asleep at e_s; F2
counts only nodes awake at both v_s and e_s, so h can exceed h_s.
Pool equality is not a premise. -/

namespace AvailableChain.PCSA

/-- Honest support above a faulty bound makes the raw gate result exact. -/
theorem pcsa_formation_gate_exact (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (a P : Block) (h f : Nat) (hFault : f < h)
    (hAnchor : Block.Prec a P)
    (hVoters : GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) ≤ h + f)
    (hPath : ∀ C, Block.Prec a C → Block.Preceq C P →
      C ∈ v.blocks ∧ h ≤ SA.Root.prefixSupport p.toParams v s C)
    (hRivals : ∀ C, Block.Prec a C → Block.Preceq C P →
      ∀ D ∈ v.blocks, D.parent? = C.parent? → D ≠ C →
        SA.Root.prefixSupport p.toParams v s D ≤ f)
    (hChildren : ∀ D ∈ v.blocks, D.parent? = some P →
      SA.Root.prefixSupport p.toParams v s D ≤ f ∧
        h + SA.Root.prefixSupport p.toParams v s D ≤
          GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s)) :
    SA.Root.confirmationFrom p.toParams a v s = some P := by
  have ha : Block.Preceq a P := (Bool.and_eq_true_iff.mp hAnchor).2
  apply FGSA.fgsa_confirmationFrom_exact_of_dominated_suffix p v a P s ha
    ?_ ?_ (Or.inr hAnchor)
  · intro C hac hCP
    obtain ⟨hm, hs⟩ := hPath C hac hCP
    refine ⟨hm, decide_eq_true (by omega), ?_⟩
    intro D hD hpar _ hne
    have hd := hRivals C hac hCP D hD hpar hne
    omega
  · intro D hD hpar
    obtain ⟨hd, hcount⟩ := hChildren D hD hpar
    apply decide_eq_false
    omega

end AvailableChain.PCSA
end
