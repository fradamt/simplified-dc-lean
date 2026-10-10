module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAClaims.Statements.Channels

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The selected honest seats whose HEAD duty is enabled at label s. -/
noncomputable abbrev healingJoinedSeats (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) : Finset (Fin p.n) := by
  classical
  exact Finset.univ.filter (fun q => rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
    joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s))

omit [DecidableEq V] in
/-- Membership carries the selected actor's actual join fact. -/
theorem healingJoinedSeats_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (q : Fin p.n) : q ∈ healingJoinedSeats E rho s ↔
    rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
    joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) := by
  classical
  delta healingJoinedSeats
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2); plan H-SUPPORT §4 step 7.
DC: SAME an honest node ticks at each awake vote time inside the horizon. -/
theorem healing_support_vote_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hDelta : E.Δ = p.Δ) {z : V}
    (hz : z ∈ rho.honest) (i : Slot) (hh : SA.voteTime p.toParams i ≤ rho.horizon)
    (hawake : E.awake z (SA.voteTime p.toParams i) = true) :
    ∃ j : Nat, rho.events[j]? = some (.tick z (SA.voteTime p.toParams i)) := by
  have htime : ((4 * i + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams i := by
    change ((4 * i + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (i : Int) + p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hS hDelta z hz (4 * i + 1)
    (htime ▸ hh) (htime ▸ hawake)
  rw [htime] at hj
  exact ⟨j, hj⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2); plan H-SUPPORT §4 step 7.
DC: SAME a joined honest holder emits its HEAD at its vote tick, and this HEAD is its
read at the label. -/
theorem healing_support_honest_emits (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Slot} {k : Fin p.n} {j : Nat}
    (hj : rho.events[j]? = some (.tick (rho.seatOf (.base (.head i)) k)
      (SA.voteTime p.toParams i)))
    (hawake : E.awake (rho.seatOf (.base (.head i)) k) (SA.voteTime p.toParams i) = true)
    (hjoined : joinedNow p (FGSA.clock p (V2.D.Run.stateBefore E rho j
      (rho.seatOf (.base (.head i)) k)).st (SA.voteTime p.toParams i)) = true) :
    let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho j
      (rho.seatOf (.base (.head i)) k)).st (SA.voteTime p.toParams i)) i
    V2.D.Run.emits E rho (rho.seatOf (.base (.head i)) k)
        (ofHead p ⟨.seat (.head i) k, K.root⟩) (SA.voteTime p.toParams i) ∧
      headAtLabel p c E rho (rho.seatOf (.base (.head i)) k) i = some K := by
  intro K
  refine ⟨⟨j, hj, ?_⟩, ?_⟩
  · rw [(V2.D.Run.step_tick_eq E rho hj).2]
    exact (fgsa_emits_head E rho _ _ _ i k K.root).mpr ⟨hawake, rfl, rfl, hjoined, rfl⟩
  · unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hj]
    rfl

end AvailableChain.FGSA.Run
end
