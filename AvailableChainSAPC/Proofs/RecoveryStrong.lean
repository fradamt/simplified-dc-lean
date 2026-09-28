module
public import AvailableChainSAPC.Proofs.Contract
public import AvailableChainSAPC.Proofs.StrongPersistence

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Supported leases put every finite root below a synchronous timely N.
Thus N transfers even at the last HEAD, without a following-gate horizon. -/
theorem recovery_timely_head_covers {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (sync : E.t_GST ≤ earlyTime p r)
    (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (saved : savedTimely (Run.stateBefore (sapc p) rho i v) r = some (some B)) :
    RecoveryHeadCovers p rho r B := by
  have cap := recovery_faultBound p G E rho hG h
  intro w hw
  have root : Block.Preceq (GridCO.liveRoot (headState p rho (r + 1) w).base) B := by
    apply GridCO.liveRoot_below_of_rows
    intro K g d row
    exact timely_prefix_of_head_coverage p E rho h.execution
      (capped_quorum_above_faults p rho cap) i v r K B saved
      (recovery_rows_supported_at_head p E rho h.execution boundary sources r start
        horizon w hw K g d row)
  have active : capBroken p (headState p rho (r + 1) w) = false := by
    rw [headState, capBroken_clock]
    exact capBroken_false_beforeTime p E rho h.execution cap w _
  exact synchronous_timely_active_head_covers p E rho h.execution hΔ h.acceptedRelay r sync
    v w hv hw horizon B (savedTimely_candidate_at_early p E rho h.execution.toScheduleWellFormed
      i v r B saved) active (Bool.or_eq_true_iff.mpr (Or.inl root))

/-- Timely preparation targets after the source boundary continue through
all later complete HEADs. The first transfer uses q support; later transfers
reuse the proved recovery raw-history induction. -/
theorem recovery_timely_later_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r s : Slot) (start : boundary ≤ r) (sync : E.t_GST ≤ voteTime p r) (before : r < s)
    (horizon : voteTime p (s + 1) ≤ rho.horizon)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (saved : savedTimely (Run.stateBefore (sapc p) rho i v) r = some (some B)) :
    ∀ w ∈ rho.honest, Block.Preceq B (headData p rho s w).target := by
  have early : E.t_GST ≤ earlyTime p r := by
    apply sync.trans
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have timeMono (a b : Slot) (le : a ≤ b) : voteTime p a ≤ voteTime p b := by
    have cast : (a : Time) ≤ b := by exact_mod_cast le
    change 4 * p.Δ * (a : Time) + p.Δ ≤ 4 * p.Δ * (b : Time) + p.Δ
    nlinarith [p.deltaPos]
  have first := recovery_timely_head_covers p E rho hΔ G hG h boundary sources r start early
    ((timeMono (r + 1) (s + 1) (Nat.add_le_add_right before.le 1)).trans horizon) i v hv B saved
  by_cases eq : s = r + 1
  · subst s; exact first
  have later : r + 1 < s := lt_of_le_of_ne before (Ne.symm eq)
  have bound : gateTime p (s - 1) ≤ rho.horizon := by
    apply le_trans _ horizon
    have cast : ((s - 1 : Nat) : Time) + 1 = s := by
      exact_mod_cast Nat.sub_add_cancel (Nat.zero_le r |>.trans_lt before)
    change 4 * p.Δ * ((s - 1 : Nat) : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast; nlinarith [p.deltaPos]
  have firstGate := ((GridCO.gateTime_le_iff p.engine (r + 1) (s - 1)).mpr
    (Nat.le_sub_one_of_lt later)).trans bound
  have syncNext := sync.trans (timeMono r (r + 1) (Nat.le_succ r))
  have times : voteTime p (r + 1) ≤ earlyTime p (r + 1) ∧
      earlyTime p (r + 1) ≤ gateTime p (r + 1) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ ∧
      4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ ≤
        4 * p.Δ * ((r + 1 : Nat) : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  obtain ⟨C, raw, below⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay (r + 1) syncNext (times.2.trans firstGate)
    (recovery_awake_majority p E rho G h _ syncNext (times.1.trans (times.2.trans firstGate)))
    B first v hv
  have support := (recovery_boundary_genuine_supported p E rho hΔ G hG h boundary sources
    (r + 1) (start.trans (Nat.le_succ r)) syncNext firstGate v hv B C raw below
    (s - 1) (Nat.le_sub_one_of_lt later) bound).2.1
  have eq : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.zero_le r |>.trans_lt before)
  simpa only [RecoveryHeadCovers, eq] using support

/-- Later PC targets extend earlier post-boundary PC targets, including
certificates first assembled from old evidence at a later read. -/
theorem recovery_pc_target_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (sync : E.t_GST ≤ proposalTime p boundary)
    (t t' : Time) (horizon : t' ≤ rho.horizon) (u v : V) (c d : PC p.n)
    (left : (Run.readAt (sapc p) rho t u).bestPC = some c)
    (right : (Run.readAt (sapc p) rho t' v).bestPC = some d)
    (start : boundary ≤ c.slot) (slots : c.slot < d.slot) : Block.Preceq c.target d.target := by
  have cap := recovery_faultBound p G E rho hG h
  have ha := capped_quorum_above_faults p rho cap
  have ack := installedPC_time_le_read p E rho h.execution.toUnforgeableSignatures ha v t' d right
  have validC := installedPC_valid_at_read p rho u t c left
  have validD := installedPC_valid_at_read p rho v t' d right
  rw [readAt_eq_stateBefore h.execution.toScheduleWellFormed] at validC validD
  obtain ⟨w, hw, i, _, _, saved⟩ := validPC_prior_timely p E rho h.execution ha _ u c validC
  apply pc_prefix_of_head_coverage p E rho h.execution ha _ v c.target d validD
  have syncVote : E.t_GST ≤ voteTime p c.slot := by
    have time := (GridCO.proposalTime_le_iff p.engine boundary c.slot).mpr start
    apply sync.trans
    change 4 * p.Δ * (boundary : Time) ≤ 4 * p.Δ * (c.slot : Time) + p.Δ
    change 4 * p.Δ * (boundary : Time) ≤ 4 * p.Δ * (c.slot : Time) at time
    linarith [p.deltaPos]
  exact recovery_timely_later_heads p E rho hΔ G hG h boundary sources c.slot d.slot
    start syncVote slots (ack.trans horizon) (i + 1) w hw c.target saved

/-- The common fresh repair supplies a permanent rank lower bound.
Target order then gives agreement and monotonicity for all recovered reads. -/
theorem strong_recovered_safe_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    SafeFrom (sapc p) rho (sapcInterface p).strong
      (E.t_GST + (sapcConstants p G).recoveryBound) := by
  obtain ⟨boundary, repair, B, pos, sync, sources, later, deadline, proposal, records, _⟩ :=
    recovery_common_repair p E rho hΔ G hG h
  have cap := recovery_faultBound p G E rho hG h
  have slotB := (honest_proposal_slot p E rho h.execution.toScheduleWellFormed
    repair B proposal).2.2
  have nonzero : B ≠ .genesis := by
    intro eq
    have zero : repair = 0 := by simpa only [eq, Block.slot] using slotB.symm
    exact (Nat.ne_of_gt (pos.trans later)) zero
  have initial (v : V) (hv : v ∈ rho.honest) :
      ∃ c, (Run.readAt (sapc p) rho (gateTime p repair) v).bestPC = some c ∧ c.slot = repair := by
    have value := (records v hv).2
    cases selected : (Run.readAt (sapc p) rho (gateTime p repair) v).bestPC with
    | none =>
      have eq : Block.genesis = B := by
        simpa only [strong, selected, Option.map_none, Option.getD_none] using value
      exact (nonzero eq.symm).elim
    | some c =>
      have target : c.target = B := by
        simpa only [strong, selected, Option.map_some, Option.getD_some] using value
      have valid := installedPC_valid_at_read p rho v _ c selected
      simp only [pcValid, pcWellFormed, Bool.and_eq_true, beq_iff_eq] at valid
      have slot : c.target.slot = c.slot := valid.1.1.1.1.1.2
      exact ⟨c, rfl, slot.symm.trans ((congrArg Block.slot target).trans slotB)⟩
  have installed (v : V) (hv : v ∈ rho.honest) (t : Time)
      (lo : E.t_GST + (sapcConstants p G).recoveryBound ≤ t) :
      ∃ c, (Run.readAt (sapc p) rho t v).bestPC = some c ∧ boundary ≤ c.slot := by
    obtain ⟨c, selected, slot⟩ := initial v hv
    obtain ⟨d, next, rank⟩ := read_rank p E rho h.execution.toScheduleWellFormed v
      (gateTime p repair) t (deadline.trans lo) c selected
    refine ⟨d, next, ?_⟩
    rcases rank with rfl | lt
    · rw [slot]; exact later.le
    · rw [slot] at lt; exact later.le.trans lt.le
  constructor
  · intro u hu v hv t t' lo hi lo' hi'
    obtain ⟨c, selectedC, startC⟩ := installed u hu t lo
    obtain ⟨d, selectedD, startD⟩ := installed v hv t' lo'
    change Block.Compatible (strong (Run.readAt (sapc p) rho t u))
      (strong (Run.readAt (sapc p) rho t' v))
    simp only [strong, selectedC, selectedD, Option.map_some, Option.getD_some]
    rcases lt_trichotomy c.slot d.slot with lt | eq | lt
    · exact Bool.or_eq_true_iff.mpr (Or.inl (recovery_pc_target_prefix p E rho hΔ G hG h
        boundary sources sync.le t t' hi' u v c d selectedC selectedD startC lt))
    · have targets := pc_same_slot_unique p E rho h.execution.toScheduleWellFormed cap _ _
        (archive_authenticated_at_read p E rho h.execution.toUnforgeableSignatures t u)
        (archive_authenticated_at_read p E rho h.execution.toUnforgeableSignatures t' v)
        c d (installedPC_valid_at_read p rho u t c selectedC)
        (installedPC_valid_at_read p rho v t' d selectedD) eq
      rw [targets]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.block_preceq_self _))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (recovery_pc_target_prefix p E rho hΔ G hG h
        boundary sources sync.le t' t hi v u d c selectedD selectedC startD lt))
  · intro v hv t t' lo le hi
    obtain ⟨c, selected, start⟩ := installed v hv t lo
    obtain ⟨d, next, rank⟩ := read_rank p E rho h.execution.toScheduleWellFormed
      v t t' le c selected
    change Block.Preceq (strong (Run.readAt (sapc p) rho t v))
      (strong (Run.readAt (sapc p) rho t' v))
    simp only [strong, selected, next, Option.map_some, Option.getD_some]
    rcases rank with rfl | lt
    · exact GridCO.block_preceq_self _
    · exact recovery_pc_target_prefix p E rho hΔ G hG h boundary sources sync.le t t' hi
        v v c d selected next start lt

/-- The companion's exact recovered inclusion field. Recovery already
derives its cap from the unchanged base constants. -/
theorem strong_recovered_included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).strong
      (E.t_GST + (sapcConstants p G).recoveryBound) (sapcStrongConstants p).strongDelay :=
  (recovery_included_from_engine p E rho hΔ G hG h).2.2

end AvailableChain.SAPC
end
