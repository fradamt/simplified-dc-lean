module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Outage.Arming
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingBatch
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPrefix
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingOutput
public import Mathlib.Tactic.IntervalCases

public section

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.OutageArming

open AvailableChain.SimplexFG
open Gen.Pure

/-! Plan O-ARM §10 boundary examples. -/

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan O-ARM §2, §10. Class (iii). DC: INTENTIONAL.
A cut at a gate time, b₀ = d(l): the cut label is `l` itself, the batch
receipt deadline e(l + 1) equals the cut, and the pending gate is strictly
later. -/
theorem cut_at_gate (p : Params) (l : Slot) :
    let b₀ := SA.gateTime p.toParams l
    ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat = l ∧
      SA.earlyTime p.toParams (l + 1) = b₀ ∧ b₀ < SA.gateTime p.toParams (l + 1) := by
  intro b₀
  have h6 : 6 * p.Δ ≤ b₀ := by
    change 6 * p.Δ ≤ 4 * p.Δ * (l : Time) + 6 * p.Δ
    have := p.deltaPos
    have : (0 : Time) ≤ 4 * p.Δ * (l : Time) := by positivity
    linarith
  have hle := (arming_le_label p b₀ h6 l).mp le_rfl
  have hlt : ¬ l + 1 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat := fun h =>
    absurd ((arming_le_label p b₀ h6 (l + 1)).mpr h)
      (not_le.mpr ((arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)))
  refine ⟨le_antisymm (Nat.le_of_lt_succ (not_le.mp hlt)) hle, arming_early_next p l,
    (arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l)⟩

/-- Plan O-ARM §10. Class (iii). DC: INTENTIONAL.
Δ = 1 and b₀ = d(2) = 14: the cut label is 2. -/
example : (((14 : Int) - 6 * 1) / (4 * 1)).toNat = 2 := by decide

/-- Plan O-ARM §2, §10. Class (iii). DC: INTENTIONAL.
The first possible origin s = 1. The fast lag puts the pending label at
least at 3; the slow window labels are between 2 and `l`. -/
example (p : Params) (T b₀ : Time) (hs : SA.gateTime p.toParams 1 ≤ T)
    (hlag : T + 4 * p.Δ ≤ b₀) : 3 ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 :=
  arming_fast_gap p 1 T b₀ hs hlag

example (p : Params) (l a : Nat) (hgap : 1 + p.k ≤ l + 1) (ha : a < p.k - 1) :
    2 ≤ l + 1 - (a + 1) ∧ l + 1 - (a + 1) ≤ l :=
  let h := arming_slow_window_label p 1 l a le_rfl hgap ha
  ⟨h.2.2, h.2.1⟩

/-- Plan O-ARM §10. Class (iii). DC: INTENTIONAL.
A pending gate after the horizon: no actual gate tick exists, so field 9 is
vacuous, and the pre-pending fields alone cover every read up to the horizon. -/
theorem pending_after_horizon {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {T b₀ b₁ : Time} {B : Block}
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hhor : rho.horizon < SA.gateTime p.toParams (l + 1)) :
    (∀ i y, ¬ IsGateTick p c rho i y (l + 1)) ∧
    ∀ y t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t → t ≤ rho.horizon →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y) := by
  refine ⟨fun i y hi => ?_, fun y t hy hlt ht => ?_⟩
  · have h := (hs.in_horizon _ (List.mem_of_getElem? hi)).2
    exact absurd (lt_of_le_of_lt h hhor) (lt_irrefl _)
  · have htd := lt_of_le_of_lt ht hhor
    have h0 : 0 ≤ t := le_trans (by
      rw [arming_gate_eq]
      have := p.deltaPos
      positivity) hlt
    exact ⟨hc.pending_cover y t hy hlt htd ht, hc.pending_compat y t hy h0 htd ht⟩

/-- Plan O-ARM §6.4, §10. Class (iii). DC: INTENTIONAL.
Slow mode below τ: the slow test alone admits the release level. -/
example (p : Params) {n : Nat} (v : GridCO.State n .root) (r : Slot) (B : Block)
    (_hbelow : SA.Root.prefixSupport p.toParams v r B < SA.releaseThreshold p.toParams)
    (hslow : GridCO.slowEligible p.toParams.engine v r B = true) :
    SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine n .root v r B :=
  by
    simp only [GridCO.admissionLevels]
    change SA.releaseThreshold p.toParams ∈
      (if decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v r B) ||
        GridCO.slowEligible p.toParams.engine v r B then [SA.releaseThreshold p.toParams] else [])
    simp [hslow]

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.cut_at_gate
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.pending_after_horizon
#print axioms AvailableChain.FGSA.Run.ArmingData_def
/-- Restart clears saved rows. A prior epoch cannot supply the slow window. -/
theorem saved_rows_erased_at_restart (p : Params) (st : State p.n) (w : Time) (s : Slot) :
    GridCO.savedGenuine (acRestart p st w).base s = none := by
  unfold GridCO.savedGenuine
  rw [acRestart_genuine]
  rfl

/-- Same-time wake precedes the gate's read. The strict-before read is insufficient. -/
theorem gate_reads_after_wake {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : IsGateTick p c rho i x s) :
    storeAt p c E rho i x = (V2.D.Run.stateAfterRestartsAt E rho
      (SA.gateTime p.toParams s) x).st := by
  exact congrArg Node.st (V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt hs hi)

/-- Full sleep excludes the old all-honest tick conclusion. -/
theorem asleep_has_no_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) {x : V} {t : Time} (ha : E.awake x t = false) :
    V2.Event.tick x t ∉ rho.events := by
  intro ht
  have hw := hE.tick_awake x t ht
  rw [ha] at hw
  cases hw

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.saved_rows_erased_at_restart
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.gate_reads_after_wake
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.asleep_has_no_tick
#print axioms AvailableChain.FGSA.Run.arming_tick_exists
#print axioms AvailableChain.FGSA.Run.arming_block_early
#print axioms AvailableChain.FGSA.Run.arming_head_ge
#print axioms AvailableChain.FGSA.Run.arming_head_ge_on
#print axioms AvailableChain.FGSA.Run.arming_healthy_batch
#print axioms AvailableChain.FGSA.Run.arming_enabled_of_pass
#print axioms AvailableChain.FGSA.Run.arming_clean_mem
#print axioms AvailableChain.FGSA.Run.arming_clean_of_tick
#print axioms AvailableChain.FGSA.Run.arming_max_label
#print axioms AvailableChain.FGSA.Run.arming_origin_of_clean
#print axioms AvailableChain.FGSA.Run.arming_origin
#print axioms AvailableChain.FGSA.Run.arming_store_succ_on
#print axioms AvailableChain.FGSA.Run.arming_store_succ
#print axioms AvailableChain.FGSA.Run.arming_clock_offGate_fields
#print axioms AvailableChain.FGSA.Run.arming_saved_interval_on
#print axioms AvailableChain.FGSA.Run.arming_saved_interval
#print axioms AvailableChain.FGSA.Run.arming_slow_saved_on
#print axioms AvailableChain.FGSA.Run.arming_slow_eligible_on
#print axioms AvailableChain.FGSA.Run.arming_slow_saved
#print axioms AvailableChain.FGSA.Run.arming_fast_awake
#print axioms AvailableChain.FGSA.Run.arming_fast_restart_free
#print axioms AvailableChain.FGSA.Run.arming_receiver_window
#print axioms AvailableChain.FGSA.Run.arming_receiver_times
#print axioms AvailableChain.FGSA.Run.arming_receiver_start_epoch
#print axioms AvailableChain.FGSA.Run.arming_receiver_epoch
#print axioms AvailableChain.FGSA.Run.arming_receiver_enabled
#print axioms AvailableChain.FGSA.Run.arming_receiver_gate_epoch
#print axioms AvailableChain.FGSA.Run.arming_tick_store_on
#print axioms AvailableChain.FGSA.Run.arming_emitted_head_fields
#print axioms AvailableChain.FGSA.Run.arming_proposal_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_head_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_batch_receipt_on
#print axioms AvailableChain.FGSA.Run.arming_prefix_batch_receipt_on

#print axioms AvailableChain.FGSA.Run.arming_enabled_of_result
#print axioms AvailableChain.FGSA.Run.arming_source_below
#print axioms AvailableChain.FGSA.Run.arming_entry_below
#print axioms AvailableChain.FGSA.Run.arming_frame_below
#print axioms AvailableChain.FGSA.Run.arming_leases_cut
#print axioms AvailableChain.FGSA.Run.arming_leases_interval
#print axioms AvailableChain.FGSA.Run.arming_leases_interval_on
#print axioms AvailableChain.FGSA.Run.arming_prefix_state
#print axioms AvailableChain.FGSA.Run.arming_S_cut
#print axioms AvailableChain.FGSA.Run.arming_S_interval
#print axioms AvailableChain.FGSA.Run.arming_S_interval_on
#print axioms AvailableChain.FGSA.Run.arming_cover
#print axioms AvailableChain.FGSA.Run.arming_compat
#print axioms AvailableChain.FGSA.Run.arming_nonrow_delivery
#print axioms AvailableChain.FGSA.Run.arming_head_ready
#print axioms AvailableChain.FGSA.Run.arming_fresh_head_service
#print axioms AvailableChain.FGSA.Run.arming_proposal_service
#print axioms AvailableChain.FGSA.Run.arming_pending_rows_on

end AvailableChain.FGSA.Run.Tests.OutageArming

namespace AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut

open AvailableChain.SimplexFG
/-! STOP: the public receipt claim includes a batch after an early healthy cut. -/

abbrev p : Params :=
  { Δ := 2, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
abbrev P := fgsa p unitCodec
def env : Generic.Env (Fin 1) := ⟨2, by decide, 0, by decide, fun _ _ => true⟩
def head0 : Obj p := ⟨.seat (.base (.head 0)) ⟨0, by decide⟩, .head genesisRoot⟩
def wire0 : HeadWire p.n := ⟨.seat (.head 0) ⟨0, by decide⟩, genesisRoot⟩
def body : NamedProposal p.n := namedProposal p .genesis 1 0 [wire0] [wire0] []
def proposal : Obj p := ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal body⟩
def run : V2.D.Run (Fin 1) P where
  honest := {0}
  horizon := 8
  events := [.tick 0 0, .tick 0 2, .deliver 0 head0 2, .tick 0 4, .tick 0 6, .tick 0 8]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

theorem emitted_cases {v : Fin 1} {o : Obj p} {t : Time}
    (h : V2.D.Run.emits env run v o t) :
    (o = head0 ∧ t = 2) ∨ (o = proposal ∧ t = 8) := by
  obtain ⟨i, hi, ho⟩ := h
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  change i < 6 at hb
  interval_cases i <;> simp [run] at hi
  all_goals obtain ⟨rfl, rfl⟩ := hi
  all_goals first
    | (change o ∈ [] at ho; exact (List.not_mem_nil ho).elim)
    | (change o ∈ [head0] at ho; exact Or.inl ⟨List.mem_singleton.mp ho, rfl⟩)
    | (change o ∈ [proposal] at ho; exact Or.inr ⟨List.mem_singleton.mp ho, rfl⟩)

theorem valid : V2.D.ExecutionValid env run := by
  refine {
    toScheduleWellFormed := ?_
    toSleepWellFormed := ?_
    toDeliveryWellFormed := ?_
    toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp [run] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e he
      simp [run] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro v t he
      simp [run] at he
      refine ⟨(t / 2).toNat, ?_⟩
      simp [env]; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t = (k : Time) * 2 at hk
      change t ≤ 8 at hh
      have hkbound : k ≤ 4 := by dsimp [Time] at *; omega
      interval_cases k <;> simp [run] <;> dsimp [Time] at * <;> omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [run] at he
    all_goals obtain ⟨rfl, rfl, rfl⟩ := he
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals change i < 6 at hib
    all_goals interval_cases i <;> first
      | decide +kernel
      | exact False.elim ((by decide +kernel : ¬ (type_of% hi)) hi)
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [run] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hu0 : u = 0 := Subsingleton.elim _ _
      subst u
      exact ⟨2, le_rfl, 1, rfl, by change head0 ∈ [head0]; exact List.mem_singleton_self _⟩
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [run] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hn : ¬ P.carries head0 o' := by intro h; cases h
      exact (hn hc).elim
  · refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
    intro v hv t ht hh hw
    have hf := hw.2
    change true = false at hf
    cases hf

theorem roots : NamedReceiptRootCollisionFree p unitCodec env run := by
  have old {A : NamedProposal p.n} (hA : NamedProposalInRun p unitCodec env run A) :
      A = .genesis := by
    rcases namedProposalInRun_genesis_or_delivered env run (by
      intro x o t N hd ho
      simp [run] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases ho) hA with hg | ⟨x, o, t, hd, ho⟩
    · exact hg
    · simp [run] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      cases ho
  have scope {A : NamedProposal p.n} (hA : NamedProposalReceiptScope p unitCodec env run A) :
      A = .genesis ∨ A = body := by
    rcases hA with hA | ⟨v, hv, o, t, N, he, ho, hAN⟩
    · exact Or.inl (old hA)
    · rcases emitted_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases ho
      · change Msg.proposal body = Msg.proposal N at ho
        cases Msg.proposal.inj ho
        change (decide (A = body) || NamedProposal.preceq A .genesis) = true at hAN
        have hh : A = body ∨ A = .genesis := by
          simpa only [Bool.or_eq_true, decide_eq_true_eq, NamedProposal.preceq] using hAN
        exact hh.symm
  intro A B hA hB he
  rcases scope hA with rfl | rfl
  all_goals rcases scope hB with rfl | rfl
  all_goals first
    | rfl
    | exact False.elim ((by decide +kernel : ¬ (type_of% he)) he)

theorem healthy : Gen.V2.Duty.HealthyPrefixDeliveryBy env run (fgsaDelay env.Δ 2) 8 := by
  have demand : V2.D.DeliveryDemand env run 0 0 head0 2 (fun a => a + 2) 8 := by
    intro a ha hn hl hc hh hr hx
    change a + 2 ≤ 8 at hc
    have hb : a ≤ 6 := by dsimp [Time] at *; omega
    interval_cases a
    all_goals first
      | (right; exact ⟨2, le_rfl, by decide, 2, head0, rfl, Or.inl rfl⟩)
      | (left; exact ⟨3, by decide, by decide +kernel⟩)
  constructor
  · intro v hv o t he w hw
    have hv0 : v = 0 := Subsingleton.elim _ _
    have hw0 : w = 0 := Subsingleton.elim _ _
    subst v; subst w
    rcases emitted_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact demand
    · intro a ha hn hl hc
      change a + 2 ≤ 8 at hc
      dsimp [Time] at *
      omega
  · intro v hv i o t ha w hw
    obtain ⟨parent, hi, hc⟩ := ha.1
    have hm := List.mem_of_getElem? hi
    simp [run] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    rcases (fgsaHooks p unitCodec).handles_carries _ _ _ hc with h | h
    · subst o
      have hw0 : w = 0 := Subsingleton.elim _ _
      subst w
      exact demand
    · have hn : ¬ P.carries head0 o := by intro h; cases h
      exact (hn h).elim


theorem joined_all (v : Fin 1) (s : Slot) (t : Time) : joinedAt p env run v s t := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w hw ht he
    have hf := he.2
    change true = false at hf
    cases hf
  · intro w hw ht he
    simp [run] at he

theorem base : Base₂ p unitCodec env run := by
  have hseats (l : RunLabel) : P.seats l = 1 := by
    cases l with
    | base l => cases l <;> rfl
    | prop s => rfl
  refine ⟨valid, ?_, ?_, ?_, rfl, roots⟩
  · refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    exact ⟨hseats l, fun i => Subsingleton.elim _ _⟩
  · intro l hl
    have hinj : Function.Injective (run.seatOf l) := by
      intro a b he
      have ha : a.val < 1 := (hseats l) ▸ a.isLt
      have hb : b.val < 1 := (hseats l) ▸ b.isLt
      apply Fin.ext
      omega
    exact ⟨hinj, fun v => ⟨⟨0, by rw [hseats l]; decide⟩, Subsingleton.elim _ _⟩⟩
  · intro v t he
    simp [run] at he

theorem regime : OutageSleep₂ p unitCodec true env run 0 8 8 2 := by
  classical
  have hj (t : Time) : joinedHonest p env run t = run.honest := by
    ext v
    simp [joinedHonest, joined_all]
  have ha (t : Time) : Gen.V2.Duty.awakeHonest env run t = run.honest := by
    ext v
    simp [Gen.V2.Duty.awakeHonest_def, env]
  have hpart (t : Time) :
      (Gen.V2.Duty.faulty run).card < (Gen.V2.Duty.awakeHonest env run t).card := by
    rw [ha]
    decide
  have hpre : HealthyPrefix₂ p unitCodec env run 8 2 :=
    ⟨base, by decide, healthy, le_rfl, fun t _ _ => hpart t⟩
  have hsleep : ∀ t : Time,
      (awakeHonestIn env run (t - p.η) t ∪ Gen.V2.Duty.faulty run).card <
        2 * (Gen.V2.Duty.awakeHonest env run t).card := by
    intro t
    rw [ha]
    have hex : ∃ u : Time, t ≤ u ∧ u ≤ t := ⟨t, le_rfl, le_rfl⟩
    simp [awakeHonestIn, env, run, Gen.V2.Duty.faulty, hex]
  refine {
    pre := hpre
    sleepy := fun t _ _ => hsleep t
    order := by decide
    lag := by decide
    budget := by decide
    fastPart := ?_
    sleepPre := ⟨hpre, ?_⟩
    joinedSleepy := ?_
    joinedFastPart := ?_
    protection := ?_ }
  · intro _ t _ _
    rw [ha]
    decide
  · intro t _ _
    rw [hj]
    decide
  · intro t _ _
    rw [hj, ← ha]
    exact hsleep t
  · intro _ t _ _
    rw [hj]
    decide
  · refine ⟨1, ?_, ?_⟩
    · intro s
      change 8 ≤ 8 * (s : Time) + 2 ↔ 1 ≤ s
      cases s with
      | zero => decide
      | succ s =>
        constructor
        · intro _; exact Nat.succ_le_succ (Nat.zero_le s)
        · intro _
          have hn : (0 : Time) ≤ (s : Time) := Int.natCast_nonneg s
          push_cast
          linarith
    · have hc : coveredNodes p env run true 8 = run.honest := by
        ext v
        simp [coveredNodes, fastCoveredSchedule, joined_all]
      have hw : outageW p env run true 8 1 = ∅ := by
        ext v
        simp only [outageW, Finset.mem_filter, hc, Finset.notMem_empty]
        exact ⟨fun h => (h.2.1 h.1).elim, False.elim⟩
      rw [hw]
      decide

/-- The corrected prefix receipt claim excludes the batch beyond this early cut. -/
theorem prefix_receipt : OutagePrefixReceipt p unitCodec env run true 0 8 := by
  intro x hx q hq hT hCut
  have hq1 : q = 1 := by simpa [coverLabel, p] using hq
  rw [hq1] at hCut
  exact False.elim ((by decide : ¬ SA.earlyTime p.toParams 1 ≤ 8) hCut)

end AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.emitted_cases
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.valid
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.roots
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.healthy
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.joined_all
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.base
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.regime
#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.EarlyCut.prefix_receipt
