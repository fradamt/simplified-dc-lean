module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingReceipt
public import AvailableChainGeneric.Proofs.V2.Duty.Sleep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- P15 local service. The anchor is max(send,wake). Finality compatibility
is checked at the receiver's deadline; survival uses event indices. -/
theorem outage_restored_service {o : Obj p} {send wake C : Time} {x : V}
    (hDelta : E.Δ = p.Δ) {ΔF : Time}
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hSend : 0 ≤ send)
    (hReady : Gen.V2.Duty.ReadyTrigger E rho o send x (max send wake)
      (max (max send wake) E.t_GST + p.Δ))
    (hHor : max (max send wake) E.t_GST + p.Δ ≤ rho.horizon)
    (hRead : max (max send wake) E.t_GST + p.Δ ≤ C)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho x o (max send wake))
    (hEpoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho (max send wake))
      (V2.D.Run.idxBefore rho C))
    (hHandlers : ∀ j t, max send wake ≤ t →
      t < max (max send wake) E.t_GST + p.Δ → V2.D.Run.handlesAt E rho j x o t →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o)
    (hFinality : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho
      (max (max send wake) E.t_GST + p.Δ) x) o = false) :
    Nonempty (ReceiverService E rho o send C x) := by
  refine ⟨⟨fun t => max t E.t_GST + p.Δ, rho.horizon, max send wake, ?_, hReady,
    le_max_left _ _, hSend.trans (le_max_left _ _), ?_, hHor, hHor, hRead,
    hHistory, hEpoch, hHandlers, hFinality⟩⟩
  · simpa only [hDelta] using
      Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hSync
        (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  · exact (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos)

/-- P15 local proposal receipt. Each ancestor has a strict stamp at the read.
The service retains the visible finality and dependency inputs. -/
theorem outage_restored_proposal_receipt {x : V} {s : Slot} {N : NamedProposal p.n}
    {send C : Time} (hS : V2.D.ScheduleWellFormed E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho) (hx : x ∈ rho.honest)
    (hC : 0 < C)
    (h : ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send C x) :
    ReceiptObjectAt p c E rho x (ofWire p ⟨.proposer s, .proposal N⟩) C :=
  arming_proposal_receipt_on hS hRoots hx hC h

/-- P15 local batch receipt. It applies to every honest receiver, including W.
The service supplies the finality alternative for each authentic HEAD target. -/
theorem outage_restored_batch_receipt_on {x : V} {q : Slot} {C : Time}
    (hE : V2.D.ExecutionValid E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho) (hx : x ∈ rho.honest)
    (hC : 0 < C) (h : ArmingBatchReceiptService E rho x q C) :
    BatchReceiptAt p c E rho x q C :=
  arming_batch_receipt_on hE hRoots hx hC h

omit [DecidableEq V] in
/-- A joined gate reader was awake throughout the label's receipt window. -/
theorem outage_restored_reader_awake {x : V} {q : Slot} {C : Time}
    (hJ : joinedAt p E rho x (q + 1) C)
    {t : Time} (ht : 0 ≤ t) (hStart : slotStartZ p (q : Int) ≤ t) (hEnd : t ≤ C) :
    E.awake x t = true := by
  classical
  by_contra hn
  obtain ⟨w, htw, hwC, hw⟩ := V2.D.Engine.wake_between hEnd
    (Bool.eq_false_iff.mpr hn) hJ.1
  have hBound := hJ.2.1 w (ht.trans_lt htw) hwC hw
  have he : slotStartZ p (((q + 1 : Nat) : Int) - 1) = slotStartZ p (q : Int) := by
    congr 1
    omega
  rw [he] at hBound
  exact (not_lt.mpr hBound) (hStart.trans_lt htw)

omit [DecidableEq V] in
/-- The joined reader supplies its exact current epoch after the label's start.
A restart at the start is before actionCut and is allowed. -/
theorem outage_restored_reader_epoch (hS : V2.D.ScheduleWellFormed E rho)
    {x : V} {q : Slot} {C a : Time} (hJ : joinedAt p E rho x (q + 1) C)
    (hStart : slotStartZ p (q : Int) ≤ a) (haC : a < C) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho C) := by
  classical
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hS haC
  intro k w he haw hwC
  have hw0 := (hS.in_horizon _ (List.mem_of_getElem? he)).1
  have hBound := hJ.2.2 w hw0 hwC.le (List.mem_of_getElem? he)
  have hEq : slotStartZ p (((q + 1 : Nat) : Int) - 1) = slotStartZ p (q : Int) := by
    congr 1
    omega
  rw [hEq] at hBound
  exact (not_lt.mpr hBound) (hStart.trans_lt haw)

/-- Compose the three approved restored read cuts. The public regime theorem
must derive these services and the P-Ar prefix; they are local proof inputs. -/
theorem outage_restored_receipt_with_service {fast : Bool} {T b₀ b₁ : Time}
    (hE : V2.D.ExecutionValid E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (hPrefix : OutagePrefixReceipt p c E rho fast T b₀)
    (hEarly : ∀ x q, restoredLabel p b₁ ≤ q →
      SA.earlyTime p.toParams q ≤ rho.horizon →
      headReader p E rho x (q + 1) (SA.gateTime p.toParams q) →
      ArmingBatchReceiptService E rho x q (SA.earlyTime p.toParams q))
    (hFreeze : ∀ x s, 0 < s → restoredLabel p b₁ ≤ s - 1 →
      SA.voteTime p.toParams s ≤ rho.horizon →
      headReader p E rho x s (SA.voteTime p.toParams s) →
      ArmingBatchReceiptService E rho x (s - 1) (SA.freezeTime p.toParams (s - 1)))
    (hProposal : ∀ m, 0 < m → restoredLabel p b₁ ≤ m - 1 →
      V2.D.proposalTime (fgsaInterface p c) m ≤ rho.horizon →
      let x := V2.D.proposerOf rho (fgsaInterface p c) m
      headReader p E rho x m (V2.D.proposalTime (fgsaInterface p c) m) →
      ArmingBatchReceiptService E rho x (m - 1)
        (V2.D.proposalTime (fgsaInterface p c) m)) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ := by
  refine ⟨hPrefix, ?_, ?_, ?_⟩
  · intro x q hr hHor hx
    apply outage_restored_batch_receipt_on hE hRoots hx.1
    · change 0 < 4 * p.Δ * (q : Int) + 2 * p.Δ
      have hd := p.deltaPos
      positivity
    · exact hEarly x q hr hHor hx
  · intro x s hs hr hHor hx
    apply outage_restored_batch_receipt_on hE hRoots hx.1
    · change 0 < 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
      have hd := p.deltaPos
      positivity
    · exact hFreeze x s hs hr hHor hx
  · intro m hm hr hHor x hx
    apply outage_restored_batch_receipt_on hE hRoots hx.1
    · change 0 < 4 * p.Δ * (m : Int)
      have hd := p.deltaPos
      have hm' : (0 : Int) < (m : Int) := by exact_mod_cast hm
      positivity
    · exact hProposal m hm hr hHor hx

end AvailableChain.FGSA.Run
end
