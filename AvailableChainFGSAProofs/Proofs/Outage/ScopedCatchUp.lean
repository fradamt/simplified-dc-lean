module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedContinuation

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The public W-reader branch names its actual post-E gate and awake suffix.
The regime produces the batch again at that gate, and the enabled guard supplies
the receipt epoch. No batch is inferred at the gate actor's earlier HEAD tick. -/
theorem outage_caught_up_gate_scope [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    {x : V} {t : Time}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (hOutside : x ∉ coveredNodes p E rho fast b₀) (hhor : t ≤ rho.horizon) :
    ∃ s j, restoredLabel p b₁ + p.k ≤ s ∧ j < timeIdx rho t ∧
      enabledGateAt p c E rho j x s ∧
      BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) ∧
      AwakeClosed E x (SA.gateTime p.toParams s) t ∧
      RestartFreeTime rho x (SA.gateTime p.toParams s) t ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
        (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) := by
  obtain ⟨hConfirmed, hCovered | ⟨s, j, hEnd, hst, hj, hG, _, hAw, hRF⟩⟩ := hReader
  · exact (hOutside hCovered).elim
  have hLabel : restoredLabel p b₁ + p.k ≤ s := by
    change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤
      4 * p.Δ * (s : Int) + 6 * p.Δ at hEnd
    have hlt : ((restoredLabel p b₁ + p.k : Nat) : Int) < (s : Int) + 1 := by
      nlinarith [p.deltaPos]
    dsimp only [Slot] at *
    omega
  have hrs : restoredLabel p b₁ ≤ s := (Nat.le_add_right _ _).trans hLabel
  have hJ := outage_enabled_gate_joined h.pre.base.valid hConfirmed.1 hG
  have hEG : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hBatch := (outage_continuation_receipt h).2.1 x s hrs
    (hEG.le.trans (hst.trans hhor)) ⟨hConfirmed.1, hJ⟩
  have hEpoch := outage_restored_reader_epoch h.pre.base.valid.toScheduleWellFormed hJ
    (a := SA.voteTime p.toParams s)
    (by change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
        linarith [p.deltaPos]) (fgsa_vote_lt_gate p s)
  exact ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF,
    hEpoch.mono le_rfl (fgsa_idxBefore_mono rho hEG.le)⟩

/-- The finalized branch supplies inclusion at the actual inclusive read.
This branch needs no covering target demand on later HEADs. -/
theorem outage_finalized_continuation_read {x : V} {t : Time} {B : Block}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hBF : Block.Preceq B (F_at p c E rho (timeIdx rho t) x)) :
    Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  have hFS := fgsaAC_anchor_le_output E rho (timeIdx rho t) x
  have hBS := Gen.Pure.block_preceq_trans hBF hFS
  exact ⟨hBS, outage_continuation_inclusive_read hs hBS
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) hBF)⟩

end AvailableChain.FGSA.Run
end
