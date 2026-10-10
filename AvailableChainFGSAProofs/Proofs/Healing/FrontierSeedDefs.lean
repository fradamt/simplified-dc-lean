module
public import AvailableChainFGSAClaims.Statements.ChannelProps

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! The seed predicate has no dependency on object-service proof inputs. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:915–944 and H.6-S:988–1025.
DC: SAME the two-arm seed premise of the frozen TFrontier. -/
def FrontierSeedQualification (p : Params) {V : Type} (E : Generic.Env V)
    (u : Time) (q : Slot) : Prop :=
  (∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1333–1350; TF-SEED Q4.
DC: SAME an explicit equation adapter for the frozen two-arm seed premise. -/
theorem frontierSeedQualification_iff (p : Params) {V : Type} (E : Generic.Env V)
    (u : Time) (q : Slot) : FrontierSeedQualification p E u q ↔
  (∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q) := Iff.rfl

/-- A qualified seed has the earlier cutoff needed by its prior-slot readers. -/
theorem frontier_seed_prior_cut {p : Params} {V : Type} {E : Generic.Env V}
    {u : Time} {q : Slot} (hready : recoveryStart p E ≤ u)
    (hseed : FrontierSeedQualification p E u q) :
    E.t_GST ≤ slotStartZ p ((q : Int) - 1) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hk : (2 : Int) ≤ p.k := by exact_mod_cast p.kLarge
  have hd := p.deltaPos
  rcases hseed with ⟨β, hβ, _, hlate⟩ | ⟨b, hb, _, _, _, hlate⟩
  · have hq : β + 2 * p.k - 1 < q := by
      by_contra hn
      have hle : (q : Int) ≤ (β + 2 * p.k - 1 : Nat) := by exact_mod_cast Nat.le_of_not_gt hn
      change 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int) < 4 * p.Δ * (q : Int) at hlate
      nlinarith
    have hcast : ((β + 2 * p.k - 1 : Nat) : Int) = (β : Int) + 2 * p.k - 1 := by
      have hkNat := p.kLarge
      omega
    have hqI : ((β + 2 * p.k - 1 : Nat) : Int) < (q : Int) := by exact_mod_cast hq
    rw [hcast] at hqI
    change u < 4 * p.Δ * (β : Int) at hβ
    change E.t_GST ≤ 4 * p.Δ * ((q : Int) - 1)
    nlinarith
  · have hq : b + p.k < q := by
      by_contra hn
      have hle : (q : Int) ≤ (b + p.k : Nat) := by exact_mod_cast Nat.le_of_not_gt hn
      change 4 * p.Δ * ((b + p.k : Nat) : Int) < 4 * p.Δ * (q : Int) at hlate
      nlinarith
    have hqI : ((b + p.k : Nat) : Int) < (q : Int) := by exact_mod_cast hq
    push_cast at hqI
    change u ≤ 4 * p.Δ * (b : Int) + p.Δ at hb
    change E.t_GST ≤ 4 * p.Δ * ((q : Int) - 1)
    nlinarith

end AvailableChain.FGSA.Run
end
