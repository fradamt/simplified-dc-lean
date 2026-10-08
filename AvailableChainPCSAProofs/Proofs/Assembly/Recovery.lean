module
public import AvailableChainPCSAProofs.Proofs.Recovery.Export
public import AvailableChainPCSAProofs.Proofs.Clean.Export
public import AvailableChainPCSAProofs.Proofs.Outage.Export

public section

/-! Clean CI consumers for the recovery archive, and the persistence input of
the recovery suffix from C8. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Existing CI result order closes cleanSaved when the anchor gate result is supplied. -/
theorem recovery_cleanSaved_of_ci (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA : Slot) (P : Block) (hci : CleanInvariantAt p c E rho cA)
    (y : V) (hy : y ∈ rho.honest)
    (hP : gateResultAt p c E rho y cA = some (some P)) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P := by
  apply recovery_cleanSaved_of_gate_prefix E rho hs cA P
  intro x hx r C hr hc
  exact (hci.resultsChain x hx y hy r cA C P hr.le (le_refl _) hc hP).1 hr

/-- CI's PC/result field and the anchor stamp supply cleanSaved without an anchor gate. -/
theorem recovery_cleanSaved_of_ci_pc (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (hf : StageOneFrame p c E rho)
    (cA : Slot) (P : Block) (hP : P.slot = cA) (hci : CleanInvariantAt p c E rho cA)
    (y : V) (hy : y ∈ rho.honest)
    (hst : PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA P) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P := by
  obtain ⟨pc, hpc, _, ht⟩ := recovery_stampRead E rho hs hnr hf y hy _ cA P hst
  have htime : SA.freezeTime p.toParams cA < SA.voteTime p.toParams (cA + 1) := by
    have hd := p.deltaPos
    change 4 * p.Δ * (cA : Int) + 3 * p.Δ < 4 * p.Δ * ((cA + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  intro x hx i r C hr hc
  have hcompat := hci.pcResults y hy x hx _ pc r C htime hpc hr.le
    (recovery_saved_gate_result E rho hs x i r C hc)
  rw [ht] at hcompat
  have hsym : Block.Compatible C P := by
    rcases Bool.or_eq_true_iff.mp hcompat with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inr h)
    · exact Bool.or_eq_true_iff.mpr (Or.inl h)
  exact recovery_saved_below_of_compatible E rho x i r cA C P hr hP hc hsym

/-- [§5.6.1; C8] The persistence input of the recovery suffix: ARM at `s₁`
with `j₀ = s₁ + 1` gives its conclusion by C8 (`pcsa_armPersistence`).
RECOVERY's `a ≤ ⌊n/4⌋` gives `a < ⌈n/2⌉`. -/
theorem recovery_persistence_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} (h : Recovery₂ p c E rho G ΔF)
    (hfr : StageOneFrame p c E rho) (s₁ : Slot) :
    ∀ B, Arm p c E rho s₁ B (s₁ + 1) → ArmConcl p c E rho s₁ B (s₁ + 1) := by
  have hf : FaultsBelowQA p c rho := by
    rw [FaultsBelowQA_def]
    have hq := (QuarterCap_def p c rho).mp h.quarterCap
    have hn := p.nPos
    change (Gen.V2.Duty.faulty rho).card < (p.n + 1) / 2
    omega
  have hP : ArmPersistenceClaim p := pcsa_armPersistence p
  rw [ArmPersistenceClaim_def] at hP
  intro B harm
  exact hP c m E rho s₁ B (s₁ + 1) h.base hf hfr (Nat.lt_succ_self s₁) harm

/-- Clean results before the anchor are below its honest proposal, including saved results. -/
theorem pcsa_recovery_cleanSaved_from_anchor [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {ΔF : Time} (cA : Slot) (N : NamedProposal p.n)
    (hPos : 0 < cA)
    (hClean : Clean₂ p c E rho (SA.freezeTime p.toParams cA) ΔF)
    (hFault : FaultsBelowQA p c rho) (hFrame : StageOneFrame p c E rho)
    (hN : HonestNamedProposal p c E rho cA N) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C N.erase := by
  have hgate : SA.gateTime p.toParams (cA - 1) ≤ SA.freezeTime p.toParams cA := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hPos)
    simp only [Nat.succ_sub_one]
    have hd := p.deltaPos
    change 4 * p.Δ * (a : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((a + 1 : Nat) : Int) + 3 * p.Δ
    push_cast
    linarith
  have hparent : Block.Preceq N.erase.parent N.erase := by
    cases N.erase with
    | genesis => exact Gen.Pure.block_preceq_refl _
    | node P s r app =>
      change (decide (P = .node P s r app) || Block.preceq P P) = true
      exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl P))
  apply recovery_cleanSaved_of_gate_prefix E rho hClean.base.valid.toScheduleWellFormed cA N.erase
  intro x hx r C hr hc
  exact Gen.Pure.block_preceq_trans
    (pcsa_clean_result_below_proposal_parent p c m E rho _ ΔF hClean hFault hFrame
      cA N hPos hN hgate x hx r C (Nat.le_sub_one_of_lt hr) hc) hparent

/-- The short-break anchor has an honest proposal, common stamp, and persistent ARM. -/
theorem pcsa_recovery_anchor_from_shortBreak [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁) :
    ∃ N : NamedProposal p.n,
      HonestNamedProposal p c E rho cA N ∧
      (∀ y ∈ rho.honest,
        PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA N.erase) ∧
      Arm p c E rho cA N.erase (cA + 1) ∧
      ArmConcl p c E rho cA N.erase (cA + 1) := by
  have htime : SA.proposalTime p.toParams cA ≤ SA.freezeTime p.toParams cA := by
    have hd := p.deltaPos
    change 4 * p.Δ * (cA : Int) ≤ 4 * p.Δ * (cA : Int) + 3 * p.Δ
    linarith
  obtain ⟨N, hN⟩ := recovery_named_proposal_exists E rho h.recovery.base h.frame cA
    h.anchorPos h.anchorProposer (htime.trans h.anchorClean.cut.2)
  have hStamp := pcsa_clean_honestProposal_stamped p c m E rho _ ΔF h.anchorClean
    h.recovery.quarterCap h.frame cA N h.anchorPos hN h.anchorPart (le_refl _)
  have hArm := arm_next_of_common_stamp E rho cA N.erase hStamp
  exact ⟨N, hN, hStamp, hArm,
    recovery_persistence_of_run E rho h.recovery h.frame cA N.erase hArm⟩

/-- Short-break premises supply the first formation slot and its separate root clauses. -/
theorem pcsa_recovery_firstSlot_short [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁) :
    ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁ := by
  obtain ⟨N, hN, hStamp, _, hArm⟩ := pcsa_recovery_anchor_from_shortBreak E rho h
  have hSaved := pcsa_recovery_cleanSaved_from_anchor E rho cA N h.anchorPos h.anchorClean
    (pcsa_c9_faultsBelowQA_of_quarterCap rho h.recovery.quarterCap) h.frame hN
  exact recovery_firstSlot_of_anchor E rho h.recovery h.frame cA s₁ N.erase
    h.order h.window h.firstAfterGST h.firstProposer h.horizon
    hStamp hArm hSaved

/-- OPEN lane suppliers for the long-break receipt boundary. Existing clean
exports require a healthy prefix and do not supply these recovery statements.
In particular, OPEN_sameLabel must include `t_g < GST ≤ v_g`. -/
theorem pcsa_recovery_lock_transport (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (g : Slot)
    (OPEN_sameLabel : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ X Y,
      gateResultAt p c E rho x r = some (some X) →
      gateResultAt p c E rho y r = some (some Y) → Block.Compatible X Y)
    (OPEN_earlyForward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ GridCO.earlyVotes p.toParams.engine (actView src.st) r,
      ∀ i, GridCO.headSeat? o = some i → ∀ H,
        GridCO.resolvedHead? (actView src.st) o = some H →
        ((o ∈ headSupport p dst.st (r + 1) ∧
          GridCO.resolvedHead? dst.st.base o = some H ∧
          GridCO.stampVote dst.st.base o < SA.freezeTime p.toParams r) ∨
          GridCO.equivocates (headVotes p dst.st (r + 1)) i = true) ∧
        H ∈ dst.st.base.blocks ∧
        GridCO.stampBlock dst.st.base H < SA.freezeTime p.toParams r ∧
        (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))))
    (OPEN_voterBackward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ headVotes p dst.st (r + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ GridCO.lateVotes p.toParams.engine (actView src.st) r ∨
        GridCO.equivocates (GridCO.lateVotes p.toParams.engine (actView src.st) r) i = true)
    (OPEN_pcReceipt : ∀ t, E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target ∧
      pc.target ∈ (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st.base.blocks)
    (OPEN_honestVoterInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ headSupport p dst.st (r + 1) ∧
      o ∈ headVotes p dst.st (r + 1) ∧
      GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
        (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))))
    (OPEN_honestProposerInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ proposerSupport dst.st (r + 1) ∧
      o ∈ proposerVotes dst.st (r + 1) ∧
      GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st (fullTree p dst.st)))
    (OPEN_rootResolution : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ a b : Nat, ∀ X Y,
    X ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks →
    Y ∈ (V2.D.Run.stateBefore E rho b y).st.base.blocks →
    X.root = Y.root → X = Y)
    : RecoveryLockTransport p c E rho g := by
  exact {
    sameLabel := OPEN_sameLabel
    earlyForward := OPEN_earlyForward
    voterBackward := OPEN_voterBackward
    pcReceipt := OPEN_pcReceipt
    honestVoterInputs := OPEN_honestVoterInputs
    honestProposerInputs := OPEN_honestProposerInputs
    rootResolution := OPEN_rootResolution
  }

/-- The seven OPEN lane suppliers give long-break formation and root reachability. -/
theorem pcsa_recovery_firstSlot_long [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s₁ : Slot)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s₁)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s₁)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s₁)
    (horizon : SA.gateTime p.toParams s₁ ≤ rho.horizon)
    (OPEN_sameLabel : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ X Y,
      gateResultAt p c E rho x r = some (some X) →
      gateResultAt p c E rho y r = some (some Y) → Block.Compatible X Y)
    (OPEN_earlyForward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ GridCO.earlyVotes p.toParams.engine (actView src.st) r,
      ∀ i, GridCO.headSeat? o = some i → ∀ H,
        GridCO.resolvedHead? (actView src.st) o = some H →
        ((o ∈ headSupport p dst.st (r + 1) ∧
          GridCO.resolvedHead? dst.st.base o = some H ∧
          GridCO.stampVote dst.st.base o < SA.freezeTime p.toParams r) ∨
          GridCO.equivocates (headVotes p dst.st (r + 1)) i = true) ∧
        H ∈ dst.st.base.blocks ∧
        GridCO.stampBlock dst.st.base H < SA.freezeTime p.toParams r ∧
        (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))))
    (OPEN_voterBackward : ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ headVotes p dst.st (r + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ GridCO.lateVotes p.toParams.engine (actView src.st) r ∨
        GridCO.equivocates (GridCO.lateVotes p.toParams.engine (actView src.st) r) i = true)
    (OPEN_pcReceipt : ∀ t, E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target ∧
      pc.target ∈ (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st.base.blocks)
    (OPEN_honestVoterInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ headSupport p dst.st (r + 1) ∧
      o ∈ headVotes p dst.st (r + 1) ∧
      GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
        (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))))
    (OPEN_honestProposerInputs : ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ proposerSupport dst.st (r + 1) ∧
      o ∈ proposerVotes dst.st (r + 1) ∧
      GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st (fullTree p dst.st)))
    (OPEN_rootResolution : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ a b : Nat, ∀ X Y,
    X ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks →
    Y ∈ (V2.D.Run.stateBefore E rho b y).st.base.blocks →
    X.root = Y.root → X = Y)
    : ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁ := by
  exact recovery_firstSlot_long E rho h hF g s₁
    (pcsa_recovery_lock_transport E rho g OPEN_sameLabel OPEN_earlyForward
      OPEN_voterBackward OPEN_pcReceipt OPEN_honestVoterInputs
      OPEN_honestProposerInputs OPEN_rootResolution)
    hgst hmix hafter hprop horizon

end AvailableChain.PCSA.Run
end
