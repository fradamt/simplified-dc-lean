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

/-- Explicit supplier interface for the long-break receipt boundary.
`pcsa_recovery_lock_transport_of_run` below supplies each field from lane exports.
The same-label field includes `t_g < GST ≤ v_g`. -/
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
    (OPEN_pcReceipt : ∀ t, (∃ s, t = SA.earlyTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target)
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
    (OPEN_pcReceipt : ∀ t, (∃ s, t = SA.earlyTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target)
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

omit [DecidableEq V] in
private theorem recovery_supplier_vote_floor (E : Generic.Env V) (g r : Slot) (hgr : g ≤ r)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    E.t_GST ≤ SA.voteTime p.toParams r := by
  apply hgst.trans
  have hd := p.deltaPos
  have hr : (g : Int) ≤ (r : Int) := by exact_mod_cast hgr
  change 4 * p.Δ * (g : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
  nlinarith

/-- Run premises supply the sameLabel transport field. -/
theorem pcsa_recovery_sameLabel_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ X Y,
      gateResultAt p c E rho x r = some (some X) →
      gateResultAt p c E rho y r = some (some Y) → Block.Compatible X Y := by
  intro r hgr hc x hx y hy X Y hX hY
  obtain ⟨a, ha, hX⟩ := pcsa_gateResultAt_source E rho x r X hX
  obtain ⟨b, hb, hY⟩ := pcsa_gateResultAt_source E rho y r Y hY
  have hv := recovery_supplier_vote_floor E g r hgr hgst
  have hz : E.t_GST ≤ SA.freezeTime p.toParams r := by
    have hd := p.deltaPos
    apply hv.trans
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + 3 * p.Δ
    linarith
  exact pcsa_same_label_gate_results_win E rho h.base hF
    (pcsa_strictFrom_of_sync E rho h.sync) a b x y hx hy r X Y hz hc ha hb hX hY

/-- Run premises supply the voterBackward transport field. -/
theorem pcsa_recovery_voterBackward_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ src dst,
      pcsa_postClock E rho x (SA.gateTime p.toParams r) = some src →
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      ∀ o ∈ headVotes p dst.st (r + 1), ∀ i, GridCO.headSeat? o = some i →
        o ∈ GridCO.lateVotes p.toParams.engine (actView src.st) r ∨
        GridCO.equivocates (GridCO.lateVotes p.toParams.engine (actView src.st) r) i = true := by
  intro r hgr hc x hx y hy src dst hsrc hdst o ho i hi
  obtain ⟨a, ha, hsa⟩ := pcsa_postClock_source E rho x _ src hsrc
  obtain ⟨b, hb, hsb⟩ := pcsa_postClock_source E rho y _ dst hdst
  rw [hsb] at ho
  rw [hsa]
  have hl := pcsa_headVotes_label p _ (r + 1) o ho
  rw [Nat.add_sub_cancel] at hl
  obtain ⟨root, rfl⟩ := pcsa_count_head_shape o r i hl hi
  have hv := recovery_supplier_vote_floor E g r hgr hgst
  have hz : E.t_GST ≤ SA.freezeTime p.toParams r := by
    have hd := p.deltaPos
    apply hv.trans
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + 3 * p.Δ
    linarith
  exact pcsa_voter_tick_input_relay_late_win E rho h.base
    (pcsa_strictFrom_of_sync E rho h.sync) b a y x hy hx r i root hz hc hb ha ho

/-- Run premises supply the rootResolution transport field. -/
theorem pcsa_recovery_rootResolution_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) :
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ a b : Nat, ∀ X Y,
    X ∈ (V2.D.Run.stateBefore E rho a x).st.base.blocks →
    Y ∈ (V2.D.Run.stateBefore E rho b y).st.base.blocks →
    X.root = Y.root → X = Y := by
  intro x hx y hy a b X Y hX hY he
  exact pcsa_scoped_root_eq E rho h.base.idealization X Y
    (pcsa_body_scope E rho a x hx X hX) (pcsa_body_scope E rho b y hy Y hY) he

/-- Run premises supply the pcReceipt transport field. -/
theorem pcsa_recovery_pcReceipt_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho) :
    ∀ t, (∃ s, t = SA.earlyTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    E.t_GST ≤ t → t + p.Δ ≤ rho.horizon →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ pc,
      pc ∈ (V2.D.Run.stateBeforeTime E rho t x).st.pcs →
      KeyHeld (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st pc.slot pc.target := by
  intro t hcut ht hc x hx y hy pc hpc
  have hpub : V2.PublicTime E t := by
    obtain ⟨s, rfl | rfl⟩ := hcut
    · refine ⟨4 * s + 2, ?_⟩
      rw [h.base.delta]
      change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
      push_cast
      ring
    · refine ⟨4 * s + 1, ?_⟩
      rw [h.base.delta]
      change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
      push_cast
      ring
  have hz : 0 ≤ t := by
    obtain ⟨s, rfl | rfl⟩ := hcut
    all_goals change 0 ≤ 4 * p.Δ * (s : Int) + _
    all_goals have hd := p.deltaPos; positivity
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ h.base.valid.toScheduleWellFormed] at hpc ⊢
  rw [KeyHeld_def]
  apply pcsa_pc_before_public_cut_relay_win E rho h.base hF
    (pcsa_c9_faultsBelowQA_of_quarterCap rho h.quarterCap)
    (pcsa_strictFrom_of_sync E rho h.sync) _ _ x y hx hy t hpub hz (le_refl _)
    (by rw [h.base.delta]) ht (by rwa [h.base.delta]) pc hpc

private theorem recovery_supplier_index (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (t bound : Time)
    (hk : rho.events[k]? = some (.tick x t)) (hb : bound ≤ t) :
    V2.D.Run.idxBefore rho bound ≤ k := by
  apply Nat.le_of_not_gt
  intro hi
  exact not_lt_of_ge hb
    ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk bound).mp hi)

private theorem recovery_supplier_resolution (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hF : StageOneFrame p c E rho)
    (k : Nat) (x : V) (hx : x ∈ rho.honest) (t : Time)
    (o : GridCO.Wire p.n .root) :
    GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k x).st t)) o =
      GridCO.resolvedHead? (clock p (V2.D.Run.stateBefore E rho k x).st t).base o := by
  have hf : (clock p (V2.D.Run.stateBefore E rho k x).st t).fg.F = .genesis := by
    rw [pcsa_body_clock_fg]
    exact (hF x hx k).1
  unfold GridCO.resolvedHead? GridCO.resolutionTree
  simp only [pcsa_actView_blocks_of_genesis _ hf]
  rfl

/-- Early wire and body relay retain every prefix in the next voter tree. -/
theorem pcsa_recovery_earlyForward_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    ∀ r, g ≤ r → SA.gateTime p.toParams r ≤ rho.horizon →
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
          (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))) := by
  intro r hgr hc x hx y hy src dst hsrc hdst o ho i hi H hr
  obtain ⟨a, ha, hsa⟩ := pcsa_postClock_source E rho x _ src hsrc
  obtain ⟨k, hk, hsk⟩ := pcsa_postClock_source E rho y _ dst hdst
  rw [hsa] at ho hr
  rw [hsk]
  have hl : GridCO.headLabel? o = some r :=
    beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp ho).1).2
  obtain ⟨root, rfl⟩ := pcsa_count_head_shape o r i hl hi
  have hroot := FGSA.Run.resolvedHead_root _ _ hr
  change some root = some H.root at hroot
  have heq := Option.some.inj hroot
  subst root
  have hd := p.deltaPos
  have hv := recovery_supplier_vote_floor E g r hgr hgst
  have he : E.t_GST ≤ SA.earlyTime p.toParams r := by
    apply hv.trans
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + 2 * p.Δ
    linarith
  have hz : SA.freezeTime p.toParams r ≤ rho.horizon := by
    apply le_trans _ hc
    change 4 * p.Δ * (r : Int) + 3 * p.Δ ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams r) ≤ k := by
    apply recovery_supplier_index E rho h.base k y _ _ hk
    change 4 * p.Δ * (r : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hD := pcsa_strictFrom_of_sync E rho h.sync
  have hbody := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
  have htime := (List.mem_filter.mp ho).2
  change GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho a x).st
    (SA.gateTime p.toParams r))) ⟨.seat r i, .head H.root⟩
    (SA.earlyTime p.toParams r) = true at htime
  delta GridCO.resolvedBefore at htime
  rw [hr] at htime
  obtain ⟨⟨_, hvs⟩, hbs⟩ := Bool.and_eq_true_iff.mp htime |>.imp_left Bool.and_eq_true_iff.mp
  have hb := pcsa_early_body_relay_frozen_win E rho h.base hF hD a k x y hx hy r H _
    (SA.voteTime p.toParams (r + 1))
    he hz hidx hbody (of_decide_eq_true hbs)
  have hbcut := (pcsa_early_body_relay_frozen_win E rho h.base hF hD a
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams r)) x y hx hy r H _ 0
    he hz (le_refl _) hbody (of_decide_eq_true hbs)).1
  rw [pcsa_clock_blocks] at hbcut
  refine ⟨?_, hb.1, hb.2, ?_⟩
  · have hpool := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
    change _ ∈ (clock p (V2.D.Run.stateBefore E rho a x).st _).base.votes at hpool
    rw [pcsa_clock_heads] at hpool
    have hvs' : GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
        ⟨.seat r i, .head H.root⟩ < SA.earlyTime p.toParams r := by
      have hh := of_decide_eq_true hvs
      change GridCO.stampVote (clock p _ _).base _ < _ at hh
      obtain ⟨row, hlookup⟩ := pcsa_head_stamp_lookup E rho a x ⟨.seat r i, .head H.root⟩ hpool
      unfold GridCO.stampVote at hh ⊢
      rw [pcsa_clock_headStamps, hlookup] at hh
      rw [hlookup]
      exact hh
    rcases pcsa_early_head_relay_frozen_win E rho h.base hD a k x y hx hy r i H.root
      (SA.voteTime p.toParams (r + 1))
      he hz hidx hpool hvs' with hh | hcap
    · rcases pcsa_early_input_relay_support_win E rho h.base hF hD a k x y hx hy
        r i H _ (SA.voteTime p.toParams (r + 1)) he hz hidx ho hr with hs | hcap
      · exact Or.inl ⟨hs.1,
          (recovery_supplier_resolution E rho hF k y hy _ _).symm.trans hs.2.2, hh.2⟩
      · exact Or.inr hcap.1
    · exact Or.inr hcap.1
  · intro B hBH
    exact pcsa_frozen_read_prefix_mem E rho h.base hF _ k y hy r _ H B
      (le_refl _) hidx hbcut hBH

/-- Honest HEAD receipt and authentication supply the actual voter inputs. -/
theorem pcsa_recovery_honestVoterInputs_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.voteTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ headSupport p dst.st (r + 1) ∧
      o ∈ headVotes p dst.st (r + 1) ∧
      GridCO.equivocates (headVotes p dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st
        (KitFG.storeFrameView (FGSA.heightView p) dst.st.fg (voterBlocks p dst.st (r + 1)))) := by
  intro r hgr x H hH i hi y hy dst hdst
  obtain ⟨k, hk, hsk⟩ := pcsa_postClock_source E rho y _ dst hdst
  rw [hsk]
  dsimp only
  have hd := p.deltaPos
  have hv := recovery_supplier_vote_floor E g r hgr hgst
  have hef : SA.earlyTime p.toParams r < SA.freezeTime p.toParams r := by
    change 4 * p.Δ * (r : Int) + 2 * p.Δ < 4 * p.Δ * (r : Int) + 3 * p.Δ
    linarith
  have hft : SA.freezeTime p.toParams r ≤ SA.voteTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hec := (hef.le.trans hft).trans
    (h.base.valid.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hk)).2
  have hidx := recovery_supplier_index E rho h.base k y _ _ hk hft
  have hei := pcsa_c9_idxBefore_mono rho hef.le
  have hD := pcsa_strictFrom_of_sync E rho h.sync
  obtain ⟨hm, hr⟩ := pcsa_honest_head_clean_support_win E rho h.base hF hD
    x y hy r i H hi hH hv hec k (hei.trans hidx) (SA.voteTime p.toParams (r + 1))
  have hearly := List.mem_filter.mp (List.mem_filter.mp hm).1
  have hseat : rho.seatOf (.base (.head r)) i ∈ rho.honest := hi ▸ hH.1
  have hsup : (⟨.seat r i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st
        (SA.voteTime p.toParams (r + 1))) (r + 1) := by
    delta headSupport
    apply List.mem_eraseDups.mpr
    apply List.mem_append_left
    apply List.mem_filter.mpr
    rw [Nat.add_sub_cancel]
    refine ⟨hearly.1, ?_⟩
    have ht := hearly.2
    change GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.voteTime p.toParams (r + 1)))) ⟨.seat r i, .head H.root⟩
      (SA.earlyTime p.toParams r) = true at ht
    delta GridCO.resolvedBefore at ht ⊢
    rw [hr] at ht ⊢
    obtain ⟨⟨hs, ht⟩, hb⟩ := Bool.and_eq_true_iff.mp ht |>.imp_left Bool.and_eq_true_iff.mp
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨hs, decide_eq_true ((of_decide_eq_true ht).trans hef)⟩,
      decide_eq_true ((of_decide_eq_true hb).trans hef)⟩
  refine ⟨hsup, pcsa_headSupport_subset_at_read E rho h.base.valid.toDeliveryWellFormed
    k y _ (r + 1) hsup,
    pcsa_voter_honest_not_capped_unconditional E rho h.base.valid k y _ r i hseat,
    (recovery_supplier_resolution E rho hF k y hy _ _).symm.trans hr, ?_⟩
  intro B hBH
  have hb := (pcsa_honest_head_body_before_early_win E rho h.base hF hD x y hy
    r H hH hv hec _ hei).1
  exact pcsa_frozen_read_prefix_mem E rho h.base hF _ k y hy r _ H B
    (le_refl _) hidx hb hBH

/-- Honest HEAD receipt and authentication supply the actual proposer inputs. -/
theorem pcsa_recovery_honestProposerInputs_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    ∀ r, g ≤ r → ∀ x H, HonestHeadAt p c E rho x r H →
    ∀ i : Fin p.n, rho.seatOf (.base (.head r)) i = x →
    ∀ y ∈ rho.honest, ∀ dst,
      pcsa_postClock E rho y (SA.proposalTime p.toParams (r + 1)) = some dst →
      let o : GridCO.Wire p.n .root := ⟨.seat r i, .head H.root⟩
      o ∈ proposerSupport dst.st (r + 1) ∧
      o ∈ proposerVotes dst.st (r + 1) ∧
      GridCO.equivocates (proposerVotes dst.st (r + 1)) i = false ∧
      GridCO.resolvedHead? dst.st.base o = some H ∧
      (∀ B, Block.Preceq B H → B ∈ erasedList dst.st (fullTree p dst.st)) := by
  intro r hgr x H hH i hi y hy dst hdst
  obtain ⟨k, hk, hsk⟩ := pcsa_postClock_source E rho y _ dst hdst
  rw [hsk]
  dsimp only
  have hd := p.deltaPos
  have hv := recovery_supplier_vote_floor E g r hgr hgst
  have hef : SA.earlyTime p.toParams r < SA.freezeTime p.toParams r := by
    change 4 * p.Δ * (r : Int) + 2 * p.Δ < 4 * p.Δ * (r : Int) + 3 * p.Δ
    linarith
  have hft : SA.freezeTime p.toParams r ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hec := (hef.le.trans hft).trans
    (h.base.valid.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hk)).2
  have hidx := recovery_supplier_index E rho h.base k y _ _ hk hft
  have hei := pcsa_c9_idxBefore_mono rho hef.le
  have hD := pcsa_strictFrom_of_sync E rho h.sync
  obtain ⟨hm, hr⟩ := pcsa_honest_head_clean_support_win E rho h.base hF hD
    x y hy r i H hi hH hv hec k (hei.trans hidx) (SA.proposalTime p.toParams (r + 1))
  have hearly := List.mem_filter.mp (List.mem_filter.mp hm).1
  have hseat : rho.seatOf (.base (.head r)) i ∈ rho.honest := hi ▸ hH.1
  have hraw : (⟨.seat r i, .head H.root⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
        (SA.proposalTime p.toParams (r + 1))) (r + 1) := by
    change _ ∈ GridCO.votesAt _ (r + 1 - 1)
    rw [Nat.add_sub_cancel]
    exact hearly.1
  refine ⟨?_, hraw,
    pcsa_proposer_honest_not_capped E rho h.base.valid k y _ r i hseat,
    (recovery_supplier_resolution E rho hF k y hy _ _).symm.trans hr, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨hraw, ?_⟩
    rw [hr]
    simpa only [Nat.add_sub_cancel] using
      decide_eq_true (pcsa_honest_head_slot_le E rho h.base hF x r H hH)
  · intro B hBH
    exact pcsa_full_read_prefix_mem E rho hF k y hy _ H B
      (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1 hBH

/-- All seven receipt fields follow from the recovery run and stage-one frame. -/
theorem pcsa_recovery_lock_transport_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g : Slot) (hgst : E.t_GST ≤ SA.voteTime p.toParams g) :
    RecoveryLockTransport p c E rho g := by
  exact pcsa_recovery_lock_transport E rho g
    (pcsa_recovery_sameLabel_of_run E rho h hF g hgst)
    (pcsa_recovery_earlyForward_of_run E rho h hF g hgst)
    (pcsa_recovery_voterBackward_of_run E rho h g hgst)
    (pcsa_recovery_pcReceipt_of_run E rho h hF)
    (pcsa_recovery_honestVoterInputs_of_run E rho h hF g hgst)
    (pcsa_recovery_honestProposerInputs_of_run E rho h hF g hgst)
    (pcsa_recovery_rootResolution_of_run E rho h)

/-- The long claim's premises give a bounded first formation slot and its root path. -/
theorem pcsa_recovery_firstSlot_long_of_run [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (horizon : E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ≤ rho.horizon) :
    ∃ (s₁ : Slot) (N : NamedProposal p.n),
      SA.gateTime p.toParams s₁ ≤ E.t_GST + 2 * pcsaL p + G + 8 * p.Δ ∧
      FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁ := by
  obtain ⟨g, s₁, hg, _, hmix, hafter, hprop, hbound⟩ := long_recovery_slot E rho h horizon
  obtain ⟨N, hN, hroot⟩ := recovery_firstSlot_long E rho h hF g s₁
    (pcsa_recovery_lock_transport_of_run E rho h hF g hg)
    hg hmix.le hafter hprop (hbound.trans horizon)
  exact ⟨s₁, N, hbound, hN, hroot⟩

end AvailableChain.PCSA.Run
end
