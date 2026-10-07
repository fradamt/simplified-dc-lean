module
public import AvailableChainPCSAProofs.Proofs.Outage.SlowRun

public section

/-! The Clean-lane ARM item (b) of ARM-healthy (pcsa34-r4.3 §5.4.2) from the
Clean facts at the pending labels. CI and `CleanDisseminationClaim` reach only
the labels with `d_j ≤ b₀`; ARM (b) reads the honest acks of every label with
`v_j < b₀`. `CutChain` records the four facts it needs at the cut: honest
results are not empty (5.2.2 (c)), the results chain and the HEADs above the
previous results at the labels whose votes are in the prefix (CI (i), (ii)),
and dissemination at the pending label (5.2.3). The Outage assembly derives
them from the pending-label Clean claims. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}

variable (p c) in
omit [Fintype V] in
/-- [pcsa34-r4.3 §5.2.2 (i), (ii), (c), §5.2.3, §5.5 step 1] The Clean facts
of one run at the pending labels of the cut `b₀`. -/
structure CutChain (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ : Time) :
    Prop where
  nonempty : ∀ i : Slot, SA.earlyTime p.toParams i ≤ b₀ → ∀ x ∈ rho.honest,
    gateResultAt p c E rho x i ≠ some none
  chain : ∀ (i i' : Slot) (x y : V) (X Y : Block), i < i' → SA.earlyTime p.toParams i' ≤ b₀ →
    x ∈ rho.honest → y ∈ rho.honest →
    gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
    Block.Preceq X Y
  heads : ∀ (i : Slot) (x y : V) (H X : Block), 0 < i → SA.voteTime p.toParams i ≤ b₀ →
    HonestHeadAt p c E rho x i H → y ∈ rho.honest →
    gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H
  dis : ∀ (s : Slot) (y : V) (B : Block), HonestAckAt p c E rho y s B →
    (SA.voteTime p.toParams (s + 1) ≤ b₀ →
      ∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
    (SA.earlyTime p.toParams (s + 1) ≤ b₀ → ∀ x ∈ rho.honest, ∀ X,
      gateResultAt p c E rho x (s + 1) = some (some X) → Block.Preceq B X)

/-- [pcsa34-r4.3 §5.2.2, §5.2.3] The Clean facts at the pending labels of every
clean stage-1 run with `a < ⌈n/2⌉`. -/
def CleanCutChainItems (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
    Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      CutChain p c E rho b₀

theorem CleanCutChainItems_def (p : Params) : CleanCutChainItems p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (m : FGMode) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (b₀ ΔF : Time),
      Clean₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
        CutChain p c E rho b₀) := by
  delta CleanCutChainItems
  rfl

/-! ### Slot times -/

omit [DecidableEq V] [Fintype V] in
/-- The gate of the previous label is the early time. -/
theorem pcsa_gate_pred_early (s : Slot) (hs : 0 < s) :
    SA.gateTime p.toParams (s - 1) = SA.earlyTime p.toParams s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.sub_add_cancel hs).symm⟩
  rw [Nat.add_sub_cancel]
  change 4 * p.Δ * (s' : Int) + 6 * p.Δ = 4 * p.Δ * ((s' + 1 : Nat) : Int) + 2 * p.Δ
  push_cast
  ring

omit [DecidableEq V] [Fintype V] in
/-- Early times increase with the slot. -/
theorem pcsa_early_mono {a b : Slot} (h : a ≤ b) :
    SA.earlyTime p.toParams a ≤ SA.earlyTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 2 * p.Δ ≤ 4 * p.Δ * (b : Int) + 2 * p.Δ
  have : (a : Int) ≤ b := by exact_mod_cast h
  nlinarith

omit [DecidableEq V] [Fintype V] in
/-- The early time of a slot is before the vote time of every later slot. -/
theorem pcsa_early_lt_vote_of_lt {a b : Slot} (h : a < b) :
    SA.earlyTime p.toParams a < SA.voteTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 2 * p.Δ < 4 * p.Δ * (b : Int) + p.Δ
  have : (a : Int) + 1 ≤ b := by exact_mod_cast h
  nlinarith

/-! ### ARM item (b) -/

omit [Fintype V] in
/-- An honest ack of slot `s` has a gate result of label `s − 1` at its node. -/
theorem pcsa_ack_gateResult (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {y : V} {s : Slot} {X : Block} (h0 : 0 < s)
    (hX : HonestAckAt p c E rho y s X) :
    (∃ r, gateResultAt p c E rho y (s - 1) = some r) ∧
      SA.earlyTime p.toParams s ≤ rho.horizon := by
  obtain ⟨-, -, hread⟩ := hX
  rw [pcsa_ackAt_def] at hread
  obtain ⟨nd, hnd, -⟩ := Option.map_eq_some_iff.mp hread
  obtain ⟨k, hk, -⟩ := pcsa_postClock_some E rho hnd
  refine ⟨?_, pcsa_tick_le_horizon E rho hs hk⟩
  rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def, pcsa_gate_pred_early s h0,
    pcsa_tickIdx_of_event E rho hs hk]
  exact ⟨_, rfl⟩

/-- [pcsa34-r4.3 §5.4.2 ARM-healthy (b)] In a clean prefix, every honest ack
of a later label with `v_{s'} < b₀` extends the target of a PC held by an
honest node, given the Clean facts at the pending labels. -/
theorem pcsa_cleanArmAcks_of (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {b₀ ΔF : Time} (hC : Clean₂ p c E rho b₀ ΔF) (hf : FaultsBelowQA p c rho)
    (hfr : StageOneFrame p c E rho) (hK : CutChain p c E rho b₀) :
    CleanArmAcks p c E rho b₀ := by
  have h := hC.base
  have hs := h.valid.toScheduleWellFormed
  have hne := hK.nonempty
  have hres := hK.chain
  have hheads := hK.heads
  rw [CleanArmAcks_def]
  intro v hv T d _ _ hd y s' X hs' hvs hX
  rw [pcsa_storeAt_index E rho hs] at hd
  obtain ⟨-, x₀, hx₀⟩ := pcsa_held_pc_ack E rho h hf v hv _ d hd
  obtain ⟨hdH, hdR⟩ := hK.dis d.slot x₀ d.target hx₀
  obtain ⟨z, hz⟩ := pcsa_honest_ack_head E rho h hf hfr y s' X hX
  rcases Nat.lt_or_eq_of_le hs' with hlt | heq
  · have h0 : 0 < s' := lt_of_le_of_lt (Nat.zero_le _) hlt
    have hy : y ∈ rho.honest := hX.1
    obtain ⟨⟨r, hr⟩, hhor⟩ := pcsa_ack_gateResult E rho hs h0 hX
    have hlt' : d.slot + 1 ≤ s' - 1 := Nat.le_sub_one_of_lt hlt
    have he1 : SA.earlyTime p.toParams (s' - 1) ≤ b₀ :=
      le_of_lt (lt_trans
        (pcsa_early_lt_vote_of_lt (a := s' - 1) (b := s') (Nat.sub_lt h0 Nat.one_pos)) hvs)
    obtain ⟨R, rfl⟩ : ∃ R, r = some R := by
      cases r with
      | none => exact absurd hr (hne _ he1 y hy)
      | some R => exact ⟨R, rfl⟩
    have hRX := hheads s' z y X R h0 (le_of_lt hvs) hz hy hr
    refine Gen.Pure.block_preceq_trans ?_ hRX
    have he2 : SA.earlyTime p.toParams (d.slot + 1) ≤ b₀ :=
      le_trans (pcsa_early_mono hlt') he1
    rcases Nat.lt_or_eq_of_le hlt' with hlt2 | heq2
    · -- a result of label `s + 1` at `y`
      have hg : SA.gateTime p.toParams (d.slot + 1) ≤ rho.horizon := by
        refine le_trans (pcsa_gate_mono (Nat.le_of_lt hlt2)) ?_
        rw [pcsa_gate_pred_early s' h0]
        exact hhor
      have hg0 : 0 ≤ SA.gateTime p.toParams (d.slot + 1) := by
        have hΔ : (0 : Int) < p.Δ := p.deltaPos
        change 0 ≤ 4 * p.Δ * ((d.slot + 1 : Nat) : Int) + 6 * p.Δ
        positivity
      obtain ⟨k, hk⟩ := pcsa_tick_exists E rho hs y hy _ (pcsa_gate_public E h.delta _) hg0 hg
      have hr1 : ∃ r1, gateResultAt p c E rho y (d.slot + 1) = some r1 := by
        rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def,
          pcsa_tickIdx_of_event E rho hs hk]
        exact ⟨_, rfl⟩
      obtain ⟨r1, hr1⟩ := hr1
      obtain ⟨R1, rfl⟩ : ∃ R1, r1 = some R1 := by
        cases r1 with
        | none => exact absurd hr1 (hne _ he2 y hy)
        | some R1 => exact ⟨R1, rfl⟩
      exact Gen.Pure.block_preceq_trans (hdR he2 y hy R1 hr1)
        (hres _ _ y y R1 R hlt2 he1 hy hy hr1 hr)
    · rw [← heq2] at hr
      exact hdR he2 y hy R hr
  · rw [← heq] at hz hvs
    exact hdH (le_of_lt hvs) z X hz

/-- [pcsa34-r4.3 §5.4.2] The two ARM items from the relay item and the Clean
facts at the pending labels. -/
theorem pcsa_cleanArmItems_of (p : Params) (hrel : CleanRelayItems p)
    (hK : CleanCutChainItems p) : CleanArmItems p := by
  rw [CleanArmItems_def]
  rw [CleanRelayItems_def] at hrel
  rw [CleanCutChainItems_def] at hK
  intro V _ _ In c m E rho b₀ ΔF hC hf hfr
  exact ⟨hrel c m E rho b₀ ΔF hC hf hfr,
    pcsa_cleanArmAcks_of E rho hC hf hfr (hK c m E rho b₀ ΔF hC hf hfr)⟩

end AvailableChain.PCSA.Run
end
