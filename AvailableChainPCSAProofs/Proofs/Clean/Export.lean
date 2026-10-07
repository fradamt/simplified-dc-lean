module
public import AvailableChainPCSAClaims.Claims.Clean
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit
public import AvailableChainPCSAProofs.Proofs.Clean.CommonResolution
public import AvailableChainPCSAProofs.Proofs.Clean.HeadPersistence
public import AvailableChainPCSAProofs.Proofs.Clean.HeadStamps
public import AvailableChainPCSAProofs.Proofs.Clean.HeadReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.HeadTransport
public import AvailableChainPCSAProofs.Proofs.Clean.HeadRelay
public import AvailableChainPCSAProofs.Proofs.Clean.BodyStamps
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport
public import AvailableChainPCSAProofs.Proofs.Clean.ResolutionDomain
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBody
public import AvailableChainPCSAProofs.Proofs.Clean.BodyReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.BodyPersistence
public import AvailableChainPCSAProofs.Proofs.Clean.TreeReceipt
public import AvailableChainPCSAProofs.Proofs.Clean.BodyAdmission
public import AvailableChainPCSAProofs.Proofs.Clean.TargetCollect
public import AvailableChainPCSAProofs.Proofs.Clean.StepVote
public import AvailableChainPCSAProofs.Proofs.Clean.StepAck
public import AvailableChainPCSAProofs.Proofs.Clean.AckRun
public import AvailableChainPCSAProofs.Proofs.Clean.StepGate
public import AvailableChainPCSAProofs.Proofs.Clean.StepPC
public import AvailableChainPCSAProofs.Proofs.Shared.Dissemination
public import AvailableChainPCSAProofs.Proofs.Shared.CleanPC

public import AvailableChainPCSAProofs.Proofs.Clean.BackwardInputs

public import AvailableChainPCSAProofs.Proofs.Clean.ForwardReceipt

public import AvailableChainPCSAProofs.Proofs.Clean.CountTransport

public import AvailableChainPCSAProofs.Proofs.Clean.GateCounts

public import AvailableChainPCSAProofs.Proofs.Clean.GateReads

public import AvailableChainPCSAProofs.Proofs.Clean.BodyPaths

public import AvailableChainPCSAProofs.Proofs.Clean.ResultPaths

public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport

public import AvailableChainPCSAProofs.Proofs.Clean.HeadEvidence

public import AvailableChainPCSAProofs.Proofs.Clean.HeadBody

public import AvailableChainPCSAProofs.Proofs.Clean.HonestReceipt

public import AvailableChainPCSAProofs.Proofs.Clean.HonestSupport

public import AvailableChainPCSAProofs.Proofs.Clean.HonestBatch

public import AvailableChainPCSAProofs.Proofs.Clean.GateBatch

public import AvailableChainPCSAProofs.Proofs.Clean.ZeroResult

public import AvailableChainPCSAProofs.Proofs.Clean.PCPool

public import AvailableChainPCSAProofs.Proofs.Clean.PCScope

public import AvailableChainPCSAProofs.Proofs.Clean.AckOrigins

public import AvailableChainPCSAProofs.Proofs.Clean.AckDecisions

public import AvailableChainPCSAProofs.Proofs.Clean.StoreOrigins

public import AvailableChainPCSAProofs.Proofs.Clean.LockOrigins

public import AvailableChainPCSAProofs.Proofs.Clean.ZeroStores

public import AvailableChainPCSAProofs.Proofs.Clean.SnapshotContents

public import AvailableChainPCSAProofs.Proofs.Clean.CarriedPCs

public import AvailableChainPCSAProofs.Proofs.Clean.ZeroViews

public import AvailableChainPCSAProofs.Proofs.Clean.RecordEvents

public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents

public import AvailableChainPCSAProofs.Proofs.Clean.RecordBounds

public import AvailableChainPCSAProofs.Proofs.Clean.RecordOrder

public import AvailableChainPCSAProofs.Proofs.Clean.ProposerInputs

public import AvailableChainPCSAProofs.Proofs.Clean.CommonInputs

public import AvailableChainPCSAProofs.Proofs.Clean.ProposalEvidence

public import AvailableChainPCSAProofs.Proofs.Clean.ProposalStore

public import AvailableChainPCSAProofs.Proofs.Clean.ProposalDelivery

public import AvailableChainPCSAProofs.Proofs.Clean.CommonRaw

public import AvailableChainPCSAProofs.Proofs.Clean.CommonBodies

public import AvailableChainPCSAProofs.Proofs.Clean.CommonSupport

public import AvailableChainPCSAProofs.Proofs.Clean.CommonScores

public import AvailableChainPCSAProofs.Proofs.Clean.CommonTree

public import AvailableChainPCSAProofs.Proofs.Clean.NCounts

public import AvailableChainPCSAProofs.Proofs.Clean.NWalkCounts

public import AvailableChainPCSAProofs.Proofs.Clean.NReadTransport

public import AvailableChainPCSAProofs.Proofs.Clean.NNextHead

public import AvailableChainPCSAProofs.Proofs.Clean.NHeads

public import AvailableChainPCSAProofs.Proofs.Clean.ViewOrigins

public section

/-! Clean store support and snapshot claim exports (pcsa34-r4.3; proof plan §5). -/

namespace AvailableChain.PCSA.Run

/-- The snapshot contains exactly the PCs held after the freeze ticks. -/
theorem pcsa_snapshotStamp (p : Params) : PCSnapshotStampClaim p := by
  intro V _ _ In c m E rho h y hy s hs
  exact snapshot_afterTicks E rho h.valid.toScheduleWellFormed h.delta y hy s hs

end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- CI at the predecessor supplies the root premise for the next honest HEADs. -/
theorem pcsa_clean_next_head_above [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (s : Slot) (hCI : CleanInvariantAt p c E rho s)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (x y : V) (hx : x ∈ rho.honest) (X H : Block)
    (hX : gateResultAt p c E rho x s = some (some X))
    (hH : HonestHeadAt p c E rho y (s + 1) H) : Block.Preceq X H := by
  exact pcsa_next_head_above_result_of_root E rho h.base hF h.healthy x y hx s X H hc hX hH
    (fun R hR => hCI.roots y hH.1 R hR x hx X hX)
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- The successor HEAD-extension field uses only the predecessor record. -/
theorem pcsa_clean_headsAbove_step (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (s : Slot) (hCI : CleanInvariantAt p c E rho s)
    (hc : SA.gateTime p.toParams (s + 1) ≤ cut) :
    ∀ (i : Slot) (x y : V) (H X : Block), 0 < i → i ≤ s + 1 →
      HonestHeadAt p c E rho x i H → y ∈ rho.honest →
      gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H := by
  have hprev : SA.gateTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  intro i x y H X hip hi hH hy hX
  by_cases hold : i ≤ s
  · exact hCI.headsAbove i x y H X hip hold hH hy hX
  · have he : i = s + 1 := Nat.le_antisymm hi (Nat.succ_le_of_lt (Nat.lt_of_not_ge hold))
    subst i
    rw [Nat.add_sub_cancel] at hX
    exact pcsa_clean_next_head_above E rho h hF s hCI hprev y x hy X H hX hH
/-- The successor result-chain field combines the predecessor record and the honest batch. -/
theorem pcsa_clean_resultsChain_step (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hF : StageOneFrame p c E rho)
    (s : Slot) (hCI : CleanInvariantAt p c E rho s)
    (hc : SA.gateTime p.toParams (s + 1) ≤ cut) :
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (i i' : Slot) (X Y : Block),
      i ≤ i' → i' ≤ s + 1 → gateResultAt p c E rho x i = some (some X) →
      gateResultAt p c E rho y i' = some (some Y) →
      (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y) := by
  have hprev : SA.gateTime p.toParams s ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  intro x hx y hy i i' X Y hii' hi' hX hY
  by_cases hold : i' ≤ s
  · exact hCI.resultsChain x hx y hy i i' X Y hii' hold hX hY
  · have he : i' = s + 1 := Nat.le_antisymm hi' (Nat.succ_le_of_lt (Nat.lt_of_not_ge hold))
    subst i'
    rcases Nat.lt_or_eq_of_le hii' with hi | he
    · have his : i ≤ s := Nat.le_of_lt_succ hi
      obtain ⟨D, hD⟩ := pcsa_clean_result_exists E rho h hF x hx s hprev
      have hXD : Block.Preceq X D := by
        rcases his.lt_or_eq with his' | his'
        · exact (hCI.resultsChain x hx x hx i s X D his (le_refl _) hX hD).1 his'
        · subst i
          have hEq : X = D := Option.some.inj (Option.some.inj (hX.symm.trans hD))
          rw [hEq]
          exact Gen.Pure.block_preceq_refl _
      have hXY : Block.Preceq X Y := pcsa_clean_result_covers_heads E rho h hF y hy (s + 1) X Y hc
        (fun z H hH => Gen.Pure.block_preceq_trans hXD
          (pcsa_clean_next_head_above E rho h hF s hCI hprev x z hx D H hD hH)) hY
      exact ⟨fun _ => hXY, fun heq => (Nat.ne_of_lt hi heq).elim⟩
    · subst i
      exact ⟨fun hi => (Nat.lt_irrefl _ hi).elim,
        fun _ => pcsa_clean_same_label_results E rho h.base hF h.healthy x y hx hy
          (s + 1) X Y hc hX hY⟩
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
/-- The label-zero Clean record follows from the empty pre-gate stores and genesis result. -/
theorem pcsa_clean_invariant_zero (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (h : Clean₂ p c E rho cut ΔF) (hFault : FaultsBelowQA p c rho)
    (hF : StageOneFrame p c E rho) (hc : SA.gateTime p.toParams 0 ≤ cut) :
    CleanInvariantAt p c E rho 0 := by
  have htime : SA.voteTime p.toParams 1 < SA.gateTime p.toParams 0 := by
    have hp := p.deltaPos
    change 4 * p.Δ * (1 : Int) + p.Δ < 4 * p.Δ * (0 : Int) + 6 * p.Δ
    nlinarith
  have stores (x : V) (hx : x ∈ rho.honest) (t : Time)
      (ht : t < SA.voteTime p.toParams 1) :=
    pcsa_zero_storeAt_before_gate E rho h.base hF hFault x hx t (ht.trans htime)
  have results (x : V) (hx : x ∈ rho.honest) (X : Block)
      (hX : gateResultAt p c E rho x 0 = some (some X)) : X = .genesis :=
    Option.some.inj (Option.some.inj (hX.symm.trans (pcsa_clean_zero_result E rho h hF x hx hc)))
  have compatible : Block.Compatible Block.genesis Block.genesis :=
    Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) (Gen.Pure.block_preceq_refl
      _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy i i' X Y hii' hi' hX hY
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero (hii'.trans hi')
    have hi'0 : i' = 0 := Nat.eq_zero_of_le_zero hi'
    subst i
    subst i'
    rw [results x hx X hX, results y hy Y hY]
    exact ⟨fun hn => (Nat.lt_irrefl 0 hn).elim, fun _ => compatible⟩
  · intro i x y H X hi hi0
    exact (Nat.not_lt.mpr hi0 hi).elim
  · intro i P x H hi hp _
    have hi0 := Nat.eq_zero_of_le_zero hi
    subst i
    exact (pcsa_no_honest_proposal_zero E rho P hp).elim
  · intro x hx t C ht hC
    rw [(stores x hx t ht).2.2] at hC
    exact (List.not_mem_nil hC).elim
  · intro x hx y hy t t' C D ht _ hC _
    rw [(stores x hx t ht).2.2] at hC
    exact (List.not_mem_nil hC).elim
  · intro x hx y hy t C i X ht hC _ _
    rw [(stores x hx t ht).2.2] at hC
    exact (List.not_mem_nil hC).elim
  · intro x hx t row ht hr
    rw [(stores x hx t ht).2.1] at hr
    exact (List.not_mem_nil hr).elim
  · intro x hx t B C ht hl _
    obtain ⟨row, hr, _⟩ := hl
    rw [(stores x hx t ht).2.1] at hr
    exact (List.not_mem_nil hr).elim
  · intro x hx i st X B hi hst _ _
    have hi0 := Nat.eq_zero_of_le_zero hi
    subst i
    rw [pcsa_zero_gate_pcs E rho h.base hFault x st hst]
    rfl
  · intro x hx i e he ht row hr _
    have hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams 0) :=
      Nat.le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff h.base.valid.toScheduleWellFormed he _).mpr
        (ht.trans htime))
    have hs := (pcsa_zero_store_before_gate E rho h.base hF i x hx hi).2
    change row ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations at hr
    rw [hs] at hr
    exact (List.not_mem_nil hr).elim
  · intro x hx t ht
    left
    have hf : (storeAt p c E rho x t).fg.F = .genesis := by
      rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.base.valid.toScheduleWellFormed]
      exact (hF x hx _).1
    rw [(stores x hx t ht).1, hf]
    rfl
  · intro x hx t t' htt ht'
    rw [(stores x hx t (lt_of_le_of_lt htt ht')).1, (stores x hx t' ht').1]
    exact Gen.Pure.block_preceq_refl _
  · intro x hx y hy t t' ht ht'
    rw [(stores x hx t ht).1, (stores y hy t' ht').1]
    exact compatible
  · intro x hx R hr y hy X hX
    rw [pcsa_zero_next_root E rho h.base hF hFault x hx R hr, results y hy X hX]
    exact compatible
end AvailableChain.PCSA.Run

end
