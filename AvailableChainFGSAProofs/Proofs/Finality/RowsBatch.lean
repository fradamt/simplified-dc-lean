module
public import AvailableChainFGSAProofs.Proofs.Finality.ActionTime
public import AvailableChainFGSAProofs.Proofs.Finality.RowsFrame
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1234,1251–1254: the action uses the full label-(z+1) HEAD pool.
DC: INTENTIONAL: this read identity supplies no vote admission or batch premise. -/
theorem rowsPrem_action_pools (q : Nat) (x : V) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime q) = some nd) :
    nd.st.slot p = q * p.R + 1 ∧
    (let raw := GridCO.votesAt nd.st.base (q * p.R + 1)
     let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
       | some H => decide (H.slot ≤ q * p.R + 1)
       | none => false)
     FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support) := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
  | none => rw [hi] at hnd; cases hnd
  | some i =>
    rw [hi] at hnd
    have he := Option.some.inj hnd
    have hs : nd.st.slot p = q * p.R + 1 := by
      rw [← he]
      exact (fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho i x) q).1
    refine ⟨hs, ?_⟩
    dsimp only [FGSA.fgHead]
    rw [hs]
    rfl

variable [Fintype V] {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

include hK in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1234,1251–1253,1719–1722: P3 gives the actual HEAD walk batch of the
raw and support pools at action pt.r + 2, with D below every honest label HEAD.
DC: INTENTIONAL: H2′ at label (pt.r+2)R+1, honest admission at the action tick, P5's F ⪯ D. -/
theorem rowsPrem_action_walk_batch
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      let s := (pt.r + 2) * p.R + 1
      let raw := GridCO.votesAt nd.st.base s
      let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
        | some H => decide (H.slot ≤ s)
        | none => false)
      let seats : Finset (Fin p.n) := by
        classical
        exact Finset.univ.filter (fun k : Fin p.n => rho.seatOf (.base (.head s)) k ∈ rho.honest)
      Gen.Pure.Batch seats.card (Gen.V2.Duty.faulty rho).card ∧
      WalkBatch p c rho nd.st s raw support (eraseFG m.X_D) seats
        (Gen.V2.Duty.faulty rho).card ∧
      FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support := by
  intro x nd hx hnd
  obtain ⟨_, _, _, _, hs2, hGST, _⟩ := kmid_kernel_bounds hK
  have hf := rowsPrem_action_frame p c E rho hK m hQC hXing hNames x nd hx hnd
  have hrD : pt.r * p.R ≤ m.cD := by
    have := m.earlySlot.1
    have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
    omega
  obtain ⟨hvGST, hvte, heh, hvthor⟩ := finality_action_time_bounds p pt.r (pt.r + 2)
    (by omega) E.t_GST E.Δ rho.horizon hGST hK.set.base.delta m.actionsInRun
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hK.set.sync (fgsaDelay_nonrow E.Δ _) hvGST hvte heh
  have hcut := kmid_window_join_cut hK (s := (pt.r + 2) * p.R + 1)
    (by rw [Nat.add_mul]; omega)
  have hJoin : ∀ y ∈ rho.honest, joinedAt p E rho y
      ((pt.r + 2) * p.R + 1) (SA.voteTime p.toParams ((pt.r + 2) * p.R + 1)) :=
    fun y hy => finality_recovery_joined p c E rho hK.set hy hcut hvGST hvthor
  have hbatch := hK.set.batch hvGST hvthor
  have hawake : Gen.V2.Duty.awakeHonest E rho
      (SA.voteTime p.toParams ((pt.r + 2) * p.R + 1)) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun y hy => hK.set.awake y hy _ hvGST hvthor)
  rw [hawake] at hbatch
  have hjh := finality_recovery_joinedHonest p c E rho hK.set hcut hvthor
  rw [← hjh] at hbatch
  have hact : E.t_GST < p.actionTime (pt.r + 2) := by
    have hlt : SA.voteTime p.toParams ((pt.r + 2) * p.R + 1) <
        p.actionTime (pt.r + 2) := by
      rw [kmid_actionTime_eq]
      change 4 * p.Δ * _ + p.Δ < 4 * p.Δ * _ + 6 * p.Δ
      push_cast
      linarith [p.deltaPos]
    exact hvGST.trans_lt hlt
  refine fgsa_action_walk_batch E rho hK.set.base (pt.r + 2) hsync
    hJoin hbatch
    (eraseFG m.X_D) x nd hnd ?_ (eraseFG_preceq hf.2.2.2.2.2.2.2.2.1)
    (fun j _ => finality_recovery_readEpoch p c E rho hK.set hx hact j)
    (fun a K ha hhead => hServices.service (pt.r + 2) x hx hact hcut
      m.actionsInRun nd hnd a K ha hhead
      (Gen.Pure.block_preceq_trans (eraseFG_preceq hf.2.2.2.2.2.2.2.2.1)
        (hK.input.ac.h2' m.cD
        (eraseFG m.X_D) m.honestD (hs2.trans hrD) _ _ K
        ⟨ha, hJoin _ ha⟩ (Nat.succ_le_succ m.earlySlot.2) hhead)))
  · intro y H hy hH
    exact hK.input.ac.h2' m.cD (eraseFG m.X_D) m.honestD (hs2.trans hrD) y _ H ⟨hy, hJoin y hy⟩
      (Nat.succ_le_succ m.earlySlot.2) hH

end AvailableChain.FGSA.Run
end
