module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Accountable

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # `fg.causalCap.core.v1`: the causal cap for a bound M (part (b))

A crossing of a height needs a quorum of matching rows, and a quorum has a
row of a signer outside a set of weight below q. Thus a chain whose rows from
such signers all have height at most M cannot cross M+1. Faulty rows can be
new; they cannot cross a height alone. Part (a) (an honest row of height h has
`h ≤` the signer's archival maximum) is a run fact: `provenance_entry` with
`comp.cut.v1`. -/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- [pin fg.causalCap.core.v1] (b) A chain whose rows from signers outside
`faulty` all have height ≤ M has state height ≤ M+1 and justified height ≤ M,
when the faulty weight is below q. -/
theorem causalCap (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (M : Height) (B : FGBlock V)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty →
      ∀ h T t, a.height_pair = .vote h T t → h ≤ M) :
    (derive E cfg B).h ≤ M + 1 ∧ (derive E cfg B).h_j ≤ M := by
  have hh : (derive E cfg B).h ≤ M + 1 := by
    by_contra hlt
    have hlt' : M + 1 < (derive E cfg B).h := by
      unfold Height at *
      omega
    obtain ⟨X, -, -, Q, hQ, hw⟩ := height_crossing E cfg B (M + 1) (Nat.le_add_left 1 M) hlt'
    obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
    obtain ⟨carrier, a, hc, ha, hai, hm⟩ := hw i hiQ
    have haB : a ∈ chainRows B := mem_chainRows_of_carrier hc ha
    cases hp : a.height_pair with
    | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
    | vote k T t =>
        have hk : k = M + 1 := by
          simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
          exact hm.1
        have := hrows a haB (hai ▸ hif) k T t hp
        unfold Height at *
        omega
  refine ⟨hh, ?_⟩
  have := justified_below_height E cfg B
  unfold Height at *
  omega

/-- [pin comp.cut.v1] (item 4, partial: the arithmetic j ≤ M < H−1 under hrows)
At a frontier `H ≥ M+2`, such a justification is not the active root
(`H ≠ h_j + 1`). -/
theorem causalCap_notRoot (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (M : Height) (B : FGBlock V)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty →
      ∀ h T t, a.height_pair = .vote h T t → h ≤ M)
    (H : Height) (hH : M + 2 ≤ H) : (derive E cfg B).h_j + 1 ≠ H := by
  have := (causalCap E cfg faulty hcap M B hrows).2
  unfold Height at *
  omega

end AvailableChain.KitFG
end
