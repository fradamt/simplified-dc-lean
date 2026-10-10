module
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDefs
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceRelease
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAClaims.Statements.OutageSleep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- P16: the joined honest set outside W is disjoint from A union W. -/
theorem outage_good_bad_disjoint [Fintype V] (fast : Bool) (b₀ : Time) (r s : Slot) :
    Disjoint (outageH p E rho s \ outageW p E rho fast b₀ r)
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hu
  obtain ⟨hh, hw⟩ := Finset.mem_sdiff.mp hx
  have hxH : x ∈ rho.honest := (Finset.mem_filter.mp hh).1
  rcases Finset.mem_union.mp hu with ha | hW
  · exact (Finset.mem_sdiff.mp ha).2 hxH
  · exact hw hW

/-- P16: E implies the strict release bound for the opponent set U=A union W. -/
theorem outage_opponents_lt_release [Fintype V]
    (hBase : Base₂ p c E rho) {fast : Bool} {b₀ : Time} {r s : Slot}
    (hCount : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      (outageH p E rho s \ outageW p E rho fast b₀ r).card) :
    (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      SA.releaseThreshold p.toParams := by
  classical
  obtain ⟨e, _⟩ := fgsa_linked_seats rho hBase.linked
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hSum := Finset.card_le_univ
    ((outageH p E rho s \ outageW p E rho fast b₀ r) ∪
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r))
  rw [Finset.card_union_of_disjoint (outage_good_bad_disjoint fast b₀ r s), hn] at hSum
  apply outage_fault_lt_release p hCount
  omega

/-- P16: E gives E1 without a good-vote or receipt premise. -/
theorem outage_e1_of_e (p : Params) : OutageE1DerivedClaim p := by
  intro In V _ _ c E rho fast b₀ b₁ hBase hE
  classical
  obtain ⟨r, hr, hCount⟩ := hE
  have hc := hCount r le_rfl ((Nat.le_add_right r p.k).trans (Nat.le_succ _))
  obtain ⟨e, _⟩ := fgsa_linked_seats rho hBase.linked
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hSum := Finset.card_le_univ
    ((outageH p E rho r \ outageW p E rho fast b₀ r) ∪
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r))
  rw [Finset.card_union_of_disjoint (outage_good_bad_disjoint fast b₀ r r), hn] at hSum
  exact ⟨r, hr, by omega⟩

/-- P12/P17: restart keeps coverage of B and its covering lock deadline. -/
theorem outage_restart_protection {B : Block} {j : Slot} {st : State p.n} (w : Time)
    (h : OutageProtection p B j st) : OutageProtection p B j (acRestart p st w) := by
  rw [OutageProtection_def] at h ⊢
  rwa [acRestart_stableRecord, acRestart_fg, acRestart_obligations]

/-- The kept-state restart case for a joint event induction. -/
theorem outage_restart_protection_at {B : Block} {j : Slot} {i : Nat} {x : V} {w : Time}
    (hi : rho.events[i]? = some (.restart x w))
    (h : OutageProtection p B j (storeAt p c E rho i x)) :
    OutageProtection p B j (storeAt p c E rho (i + 1) x) := by
  change OutageProtection p B j (V2.D.Run.stateBefore E rho (i + 1) x).st
  rw [V2.D.Run.stateBefore_succ E rho hi]
  simp only [V2.D.World.step, Function.update_self]
  exact outage_restart_protection w h

/-- P17: the covering-lock exception is limited to the live deadline. -/
theorem outage_restart_live_lock {B : Block} {g : Nat} {dl : Time} {st : State p.n}
    {w : Time} (hRow : (B, g, dl) ∈ st.base.obligations) (hLive : w < dl) :
    (B, g, dl) ∈ (acRestart p st w).base.obligations ∧
      (acRestart p st w).base.now < dl := by
  rw [acRestart_obligations, acRestart_now]
  exact ⟨hRow, hLive⟩

end AvailableChain.FGSA.Run
end
