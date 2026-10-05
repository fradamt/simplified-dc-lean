module
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

public section

/-! H-SUPPORT gate cover (plan §4 steps 7–8; G7). At a label where every honest HEAD
covers B, the raw confirmation of each honest gate in the synchronous window covers B. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2 S1); plan H-SUPPORT §4 step 7.
DC: SAME a HEAD that an honest seat emits is its HEAD read at that label. -/
theorem healing_support_emitted_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (w : Slot) (q : Fin p.n) (K : Block) (t : Time)
    (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head w)) q)
      (ofHead p ⟨.seat (.head w) q, K.root⟩) t K) :
    headAtLabel p c E rho (rho.seatOf (.base (.head w)) q) w = some K := by
  have hObserver := he
  obtain ⟨j, _, _, hj, hem, _, _⟩ := he
  have hK := headTargetAtEmission_at_tick E rho hs hObserver hj rfl
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨_, ht, _, _⟩ := (fgsa_emits_head E rho _ _ _ w q K.root).mp hem
  subst t
  change (postClock E rho _ (SA.voteTime p.toParams w)).map
    (fun nd => headVote p nd.st w) = some K
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hj]
  exact congrArg some hK.symm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–733 (H.2 S1–S3), 02 §5.4:541; plan H-SUPPORT §4 steps 7–8.
DC: INTENTIONAL the covering-batch gate read. If every honest HEAD of label w covers B
and the gate floor is at or below B, the raw confirmation of an honest gate at w covers
B. The per-seat HEADs may differ (`fgsa_gate_batch_premises`); no exact HEAD is needed. -/
theorem healing_support_gate_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {w : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams w)
    (hhor : SA.gateTime p.toParams w ≤ rho.horizon)
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {j : Nat} {y : V} (ht : IsGateTick p c rho j y w)
    (hFB : Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j y)
      (SA.gateTime p.toParams w)).fg.F) B) :
    ∃ C, SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)).fg.F)
        (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w = some C ∧
      Block.Preceq B C := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hC := hrec.base.cstar
  have hvg : SA.voteTime p.toParams w ≤ SA.gateTime p.toParams w := by
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvd : SA.voteTime p.toParams w + E.Δ ≤ SA.gateTime p.toParams w := by
    rw [hDelta]
    change 4 * p.Δ * (w : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hhorv : SA.voteTime p.toParams w ≤ rho.horizon := hvg.trans hhor
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
  have hcovK (q : Fin p.n) (hq : rho.seatOf (.base (.head w)) q ∈ rho.honest) (K : Block)
      (t : Time) (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head w)) q)
        (ofHead p ⟨.seat (.head w) q, K.root⟩) t K) : Block.Preceq B K :=
    hcov _ hq K (healing_support_emitted_head (c := c) E rho hS w q K t he)
  have hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)) w B :=
    ⟨fun q hq _ K he => Gen.Pure.block_preceq_trans hFB (hcovK q hq K _ he),
      fun q hq _ K he => hcovK q hq K _ he⟩
  let H : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head w)) k ∈ rho.honest)
  have hHmem (k : Fin p.n) : k ∈ H ↔ rho.seatOf (.base (.head w)) k ∈ rho.honest := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head w)) k) :=
    hC (.base (.head w)) trivial
  have hHcard : H.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective H hbij.1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hHmem k).mp hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, (hHmem k).mpr hz, rfl⟩
  have hawk : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams w) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun z hz => hrec.awake z hz _ hgst hhorv)
  have hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
    have h := (hrec.batch hgst hhorv).lt
    rw [hawk] at h
    exact ⟨hHcard ▸ h⟩
  have hcover := fgsa_gate_batch_premises E rho hE hC j y w B H hbatch
    (fun k hk _ => (hHmem k).mpr hk) (by
      intro k hk
      have hq := (hHmem k).mp hk
      obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, hF, hBK⟩ :=
        fgsa_gateReceipt (hroots := hrec.base.idealization)
          E rho hE hN hDelta hC w hSync ht B hgeom k hq
          (hrec.awake _ hq _ hgst hhorv)
      exact ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, hF, hBK⟩)
  exact fgsa_confirmationFrom_covers_majority p _ _ B w B.root
    (Bool.or_eq_true_iff.mpr (Or.inl hFB)) hcover.1 hcover.2.1 hcover.2.2

end AvailableChain.FGSA.Run
end
