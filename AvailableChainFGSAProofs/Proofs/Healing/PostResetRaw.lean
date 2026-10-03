module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant -- shake: keep (J5 required carrier input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat -- shake: keep (J5 required lane input)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep -- shake: keep (J5 required lane input)
public import AvailableChainFGSAProofs.Proofs.Healing.ResetTransfer -- shake: keep (J5 required lane input)

public section

/-! Blueprint 21 H.16:2924–2945, H5:3318–3325; post-reset plan J5 B;
B1/B13/B17/B18. DC: SAME removal of event-prefix guards from raw transfer.
The all-cut input is conditional; this file does not produce its successor. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem raw_result_tick {y : V} {j : Slot} {C : Block}
    (hC : gateResult p c E rho y j = some (some C)) :
    ∃ k, IsGateTick p c rho k y j := by
  rw [gateResult_def, gateIn_def, preTick_def] at hC
  cases hk : V2.D.Run.tickIdx? rho y (SA.gateTime p.toParams j) with
  | none => rw [hk] at hC; cases hC
  | some k => exact ⟨k, V2.D.Run.tickIdx?_spec hk⟩

/-- Blueprint 21 H.16:2924–2945, H5:3318–3325; plan J5 B;
B1/B13/B17/B18. DC: SAME all-cut projection of the four H5 clauses.
Each concrete reader uses a cut past the source tick and its own read.
The input covers every Nat cut, including cuts past rho.events.length.
Only raw_transfer is needed at all cuts; no J4 or J6 field is used. -/
theorem postReset_h5RawTransfer_body {w : HealingWitness}
    (_h0r : H0Reset p c E rho w)
    (raw : ∀ i, PostResetRawTransfer p c E rho w i) :
    H5RawTransfer p c E rho w := by
  change ∀ y j C, y ∈ rho.honest → w.sStar ≤ j →
    gateResult p c E rho y j = some (some C) → _
  intro y j C hy hj hC
  obtain ⟨k, hk⟩ := raw_result_tick p c E rho hC
  have atCut (i : Nat) (hi : k < i) := by
    have h := raw i
    rw [PostResetRawTransfer_def] at h
    exact h k hi y j C hy hj hk hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x nd hx hnd lease hlease hlive
    let i := max (k + 1) (timeIdx rho (SA.releaseTime p.toParams j))
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.1 x nd hx (le_max_right _ _) hnd lease hlease hlive
  · intro x s H hx hs hH
    let i := max (k + 1) (timeIdx rho (SA.voteTime p.toParams s))
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.2.1 x s H hx hs (le_max_right _ _) hH
  · intro v Q hv hQ
    let i := max (k + 1) (timeIdx rho (SA.proposalTime p.toParams v))
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.2.2.1 v Q hv (le_max_right _ _) hQ
  · intro a x hx hhor ha
    let i := max (k + 1) (a + 1)
    have h := atCut i (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _))
    exact h.2.2.2 a x (Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (le_max_right _ _))
      hx hhor ha

end AvailableChain.FGSA.Run
end
