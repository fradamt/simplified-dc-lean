module
public import AvailableChainSAPC.Proofs.RecoveryPremise
public import AvailableChainSAPC.Proofs.Preservation

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Full honest participation puts every honest seat in the actual late
denominator. The duty itself may be the first synchronous HEAD; this
lemma makes no claim about the preceding proposal. -/
theorem full_batch_late_count {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (net : PartialSynchrony (sapc p) E rho)
    (relay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (sync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (full : ∀ v ∈ rho.honest, E.awake v (voteTime p r) = true)
    (v : V) (hv : v ∈ rho.honest) :
    rho.honest.card ≤ GridCO.voterCount (GridCO.lateVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) := by
  rw [← GridCO.lateSeats_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf r).symm
  · intro u hu
    have early := synchronous_head_in_earlyVotes p E rho hx hΔ net relay r sync horizon
      u v hu hv (full u hu)
    exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_filterMap.mpr
      ⟨_, GridCO.earlyVotes_subset_lateVotes p.engine _ r _ early, rfl⟩))
  · intro u _ w _ eq
    exact (rho.seatOf r).symm.injective eq

/-- Every synchronous genuine prefix under Recovery has support above f.
The support can include faulty seats. Its bound comes from the full late
denominator and the raw majority test, before either PC gate guard. -/
theorem recovery_genuine_support_above_floor {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C) :
    pcFaultCap p < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B := by
  have voteBound : voteTime p r ≤ rho.horizon := by
    apply le_trans _ horizon
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have denominator := full_batch_late_count p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync horizon (fun u hu => h.full rfl u hu _ sync voteBound) v hv
  have seats : Fintype.card V = p.n := by
    simpa using (Fintype.card_congr (rho.seatOf r)).symm
  have total : rho.honest.card + (faulty rho).card = p.n := by
    dsimp [faulty]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have := Finset.card_le_univ rho.honest
    omega
  apply recovery_support_above_floor p (faulty rho).card rho.honest.card _ _
    (recovery_faultBound p G E rho hG h) total denominator
  have majority := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r C raw
  have mono := GridCO.prefixSupport_mono p.engine
    (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B C below
  omega

/-- Recovery removes the PC-compatibility premise from genuine transfer.
Only the finite-root obligation remains for fast-source release and
slow-window expiry. This does not assert those obligations or recovery. -/
theorem recovery_genuine_head_covers {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C)
    (root : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) B) :
    Block.Preceq B (headData p rho (r + 1) w).target := by
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  exact synchronous_genuine_highSupport_head_covers p E rho h.execution hΔ h.acceptedRelay
    r (sync.trans early.1) horizon v w hv hw B C raw below
    (recovery_genuine_support_above_floor p E rho hΔ G hG h r sync (early.2.trans horizon)
      v hv B C raw below) root

end AvailableChain.SAPC
end
