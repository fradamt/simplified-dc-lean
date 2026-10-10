module
import all AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch
public import AvailableChainFGSAProofs.Proofs.Outage.GoodVotes
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Prefix transport gives the exact early HEAD service at a joined reader.
The cut can precede the consuming gate, as required by the pending batch. -/
theorem outage_prefix_head_service {cut : Time}
    (hBase : Base₂ p c E rho)
    (hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) cut)
    {x y : V} {s : Slot} {C R : Time} {q : Fin p.n} {b : BlockId}
    (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hC : SA.earlyTime p.toParams s ≤ C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hCut : C ≤ cut)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    Nonempty (FreshHeadService E rho s q b C x) := by
  have hd := p.deltaPos
  have hv0 : 0 ≤ SA.voteTime p.toParams s := by rw [arming_vote_eq]; positivity
  have hstart : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith
  have hve := (arming_vote_lt_early p s).1
  have hRF := outage_restored_reader_epoch hBase.valid.toScheduleWellFormed hJ
    hstart (hve.trans_le (hC.trans hCR))
  have hdl : SA.voteTime p.toParams s + p.Δ =
      SA.earlyTime p.toParams s := arming_vote_add p s
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := cut
    within := ?_
    ready := ?_
    later := by simpa only [hdl] using hve
    cut_le := by simpa only [hdl] using hC.trans hCut
    horizon := by simpa only [hdl] using hC.trans hhor
    freeze_le := by simpa only [hdl] using hC
    epoch := hRF.mono le_rfl (fgsa_idxBefore_mono rho hCR)
    handlers := by simpa only [hdl] using arming_head_handlers hBase.valid hBase.delta s q b x
    not_excluded := by simpa only [hdl] using outage_fresh_head_not_excluded hBase.valid hy he }⟩
  · exact hDelivery
  · rw [hdl]
    refine ⟨y, hy, Or.inl he, ?_⟩
    intro u hvu hue
    exact outage_restored_reader_awake hJ (hv0.trans hvu) (hstart.trans hvu)
      (hue.le.trans (hC.trans hCR))

private theorem outage_proposal_direct (st : State p.n) (parent o : Obj p)
    {s : Slot} {N : NamedProposal p.n} (hd : (toWire p o).decode = some (.block s N))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r M =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofHead] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofRow] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd

/-- Original proposal emission or acceptance drives service at a public anchor.
Durable proposal history supplies HistorySafeAt after an earlier restart.
The transport cut is explicit. -/
theorem outage_prefix_proposal_service {cut : Time}
    (hBase : Base₂ p c E rho)
    (hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) cut)
    {x y : V} {s q : Slot} {N : NamedProposal p.n} {send a C R : Time}
    (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hStart : slotStartZ p (s : Int) ≤ a) (hPub : V2.PublicTime E a)
    (hDeadline : a + p.Δ = C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hCut : C ≤ cut) (ht : send ≤ a)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E C x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩) send C x) := by
  have hV := hBase.valid
  have ha0 : 0 ≤ a := le_trans (by
    change 0 ≤ 4 * p.Δ * (s : Int); have := p.deltaPos; positivity) hStart
  have haC : a < C := hDeadline ▸ lt_add_of_pos_right a p.deltaPos
  have hdl : a + p.Δ = C := hDeadline
  have hAct : fgsaAdmissionTime p (ofWire p ⟨.proposer q, .proposal N⟩) ≤ send := by
    rcases he with ⟨k, hk, hem⟩ | ⟨k, hacc⟩
    · rw [(V2.D.Run.step_tick_eq E rho hk).2] at hem
      exact ((fgsa_emits_proposal E rho _ y send q (.proposal N)).mp hem).2.1.le
    · have hbound := timely_of_relay_retained E rho (fgsaTimelyClock p c)
        (fgsaAdmitSound p c) hV.toScheduleWellFormed
        (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
        (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
          fgsa_admissionTime_public p E hBase.delta obj) y k _ send hacc
      rw [fgsaTimelyClock_actTime] at hbound
      exact hbound.trans (Gen.V2.Duty.pubFloor_le E send)
  have hRF := outage_restored_reader_epoch hV.toScheduleWellFormed hJ hStart
    (haC.trans_le hCR)
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := cut
    anchor := a
    within := ?_
    ready := ?_
    send_le := ht
    nonneg := ha0
    later := by simpa only [hdl] using haC
    cut_le := by simpa only [hdl] using hCut
    horizon := by simpa only [hdl] using hhor
    freeze_le := by rw [hdl]
    history := fgsa_historySafeAt_of_proposal x _ a rfl
    epoch := hRF.mono le_rfl (fgsa_idxBefore_mono rho hCR)
    handlers := ?_
    not_excluded := by simpa only [hdl] using hNX }⟩
  · exact hDelivery
  · rw [hdl]
    refine ⟨y, hy, he, ?_⟩
    intro u hau huC
    exact outage_restored_reader_awake hJ (ha0.trans hau) (hStart.trans hau)
      (huC.le.trans hCR)
  · intro j u hau hud hh
    obtain ⟨parent, hj, hp⟩ := hh
    have hEq := outage_proposal_direct _ parent _ rfl hp
    subst parent
    refine ⟨hV.wire j x _ u hj, hV.deps j x _ u hj, ?_⟩
    have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hV hj hPub ha0 hau
    change fgsaAdmissionTime p _ ≤ (rho.stateBefore E j x).st.base.now
    rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
    exact (hAct.trans ht).trans hn

private theorem outage_target_decode {o : Obj p} {K : Block}
    (h : blockOf? p o = some K) :
    ∃ q N, o = ofWire p ⟨.proposer q, .proposal N⟩ ∧ N.erase = K := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i q N
    refine ⟨q, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- A joined honest reader gets a full batch at the exact public deadline.
Incompatible targets keep the public finality alternative. Compatible targets
use their original acceptance and durable proposal history. -/
theorem outage_prefix_batch_service {cut : Time}
    (hBase : Base₂ p c E rho)
    (hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) cut)
    {x : V} {s : Slot} {a C R : Time} (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hC : SA.earlyTime p.toParams s ≤ C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hCut : C ≤ cut)
    (hva : SA.voteTime p.toParams s ≤ a) (hPub : V2.PublicTime E a)
    (hDeadline : a + p.Δ = C) : ArmingBatchReceiptService E rho x s C := by
  classical
  have hV := hBase.valid
  have hS := hV.toScheduleWellFormed
  have hStart : slotStartZ p (s : Int) ≤ a := le_trans (by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]) hva
  constructor
  · intro y o q b hy he hd
    have ho : o = ofHead p ⟨.seat (.head s) q, b⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    subst o
    obtain ⟨k, hk, hem⟩ := he
    have he' := hem
    rw [(V2.D.Run.step_tick_eq E rho hk).2] at he'
    have hf := (fgsa_emits_head E rho _ y _ s q b).mp he'
    let K := headVote p (FGSA.clock p (rho.stateBefore E k y).st
      (SA.voteTime p.toParams s)) s
    have hroot : K.root = b := hf.2.2.2.2.symm
    have hTarget : HeadTargetAtEmission p c E rho y
        (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s) K := by
      refine ⟨k, s, q, hk, hem, ?_, rfl⟩
      rw [hroot]
    refine ⟨K, hTarget, ?_⟩
    by_cases hbad : ¬ Block.Compatible K (eraseFG (rho.stateBeforeTime E C x).st.fg.F)
    · exact Or.inl hbad
    right
    refine ⟨outage_prefix_head_service hBase hDelivery hx hy hJ hC hCR hhor hCut
      ⟨k, hk, hem⟩, ?_⟩
    by_cases hgen : K = .genesis
    · exact Or.inl hgen
    have hK : K ∈ (storeAt p c E rho k y).base.blocks := by
      have hm := headVote_stored p _
        (storeBundle_postClock E rho k y (SA.voteTime p.toParams s)).cstore s
      change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
      rwa [clock_base_blocks] at hm
    obtain ⟨j, hjk, send, obj, hobj, hacc⟩ := fgsa_block_accepted_origin E rho k y K hgen hK
    obtain ⟨q', N, rfl, hNK⟩ := outage_target_decode hobj
    have hsend : send ≤ SA.voteTime p.toParams s := by
      obtain ⟨parent, hj, _⟩ := hacc.1
      by_contra hn
      have hkj := V2.D.Engine.tick_index_lt_delivery E rho hS hk hj (le_of_not_ge hn)
      omega
    have hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer q', .proposal N⟩) send :=
      Or.inr ⟨y, hy, j, hacc⟩
    have hNX : (fgsa p c).excludes (rho.stateBeforeTime E C x)
        (ofWire p ⟨.proposer q', .proposal N⟩) = false := by
      change (blockExcluded _ N.erase || invalidForParent p _ N) = false
      rw [fgsa_trigger_invalid_false E rho _ send q' N hT rfl]
      change (!activeCompatible _ N.erase || false) = false
      have hc : activeCompatible (rho.stateBeforeTime E C x).st N.erase = true := by
        change Block.compatible N.erase (eraseFG (rho.stateBeforeTime E C x).st.fg.F) = true
        rw [hNK]
        exact not_not.mp hbad
      rw [hc]
      rfl
    exact Or.inr ⟨q', N, send, hNK,
      outage_prefix_proposal_service hBase hDelivery hx hy hJ hStart hPub hDeadline
        hCR hhor hCut (hsend.trans hva) (Or.inr ⟨j, hacc⟩) hNX⟩
  · intro y o m q N hy he htime hNX hd
    have ho : o = ofWire p ⟨.proposer q, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    subst o
    exact outage_prefix_proposal_service hBase hDelivery hx hy hJ hStart hPub hDeadline
      hCR hhor hCut (htime.trans hva) (Or.inl he) hNX

/-- The healthy prefix supplies service at every enabled pending receiver,
including W. Only the early deadline must be inside the prefix. -/
theorem outage_pending_receipt_scope [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1)) : GateReceiptScope E rho i x (l + 1) := by
  have hs := h.base.valid.toScheduleWellFormed
  have hJ := outage_enabled_gate_joined h.base.valid hx hG
  have heg : SA.earlyTime p.toParams (l + 1) ≤ SA.gateTime p.toParams (l + 1) := by
    rw [arming_early_eq, arming_gate_eq]
    linarith [p.deltaPos]
  have hecut : SA.earlyTime p.toParams (l + 1) ≤ b₀ :=
    (arming_early_next p l).trans_le hc.gate_le_cut
  have hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) b₀ := by
    simpa only [h.base.delta] using Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy
      E rho b₀ h.healthy (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  have hPub : V2.PublicTime E (SA.voteTime p.toParams (l + 1)) := by
    refine ⟨4 * (l + 1) + 1, ?_⟩
    rw [h.base.delta, arming_vote_nat]
  have hBatch := outage_prefix_batch_service h.base hDelivery hx hJ le_rfl heg
    (hecut.trans h.cut.2) hecut le_rfl hPub (arming_vote_add p (l + 1))
  refine ⟨hG, hJ, outage_enabled_gate_read_epoch hs hG ?_, ?_⟩
  · change 4 * p.Δ * ((l + 1 : Nat) : Int) <
      4 * p.Δ * ((l + 1 : Nat) : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · intro q K hy hTarget
    obtain ⟨k, hk, hem⟩ : V2.D.Run.emits E rho
        (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
        (SA.voteTime p.toParams (l + 1)) := by
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
      exact ⟨k, hk, hem⟩
    obtain ⟨K', hTarget', hbad | hService⟩ := hBatch.heads _ _ q K.root hy
      ⟨k, hk, hem⟩ (by rw [toWire_ofHead]; rfl)
    all_goals have heq : K = K' := headTargetAtEmission_unique E rho hs hTarget hTarget'
    · have hDK := arming_head_ge_on hs htransfer hc.max_mem hy
        (fgsa_joinedAt_of_emitted_head E rho h.base.valid hk hem) hk
      change Block.Preceq D (headVote p (clock p (rho.stateBefore E k
        (rho.seatOf (.base (.head (l + 1))) q)).st (SA.voteTime p.toParams (l + 1)))
          (l + 1)) at hDK
      rw [← headTargetAtEmission_at_tick E rho hs hTarget hk rfl] at hDK
      have hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
          (SA.earlyTime p.toParams (l + 1)) x).st.fg.F) D := by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
        exact hc.f_below _ x (fgsa_idxBefore_mono rho heg) hx
      exact (hbad (heq ▸ block_compatible_of_common (block_preceq_refl K)
        (block_preceq_trans hFloor hDK))).elim
    · simpa only [← heq] using hService

/-- The complete joined Clean batch makes every enabled pending result compatible.
The receiver can be in W; the prefix service has no covered-node premise. -/
theorem outage_pending_result_compatible [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {i : Nat} {x : V} {C : Block} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1))
    (hC : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  have hv0 : 0 ≤ SA.voteTime p.toParams (l + 1) := by
    rw [arming_vote_eq]
    have := p.deltaPos
    positivity
  have hvcut : SA.voteTime p.toParams (l + 1) < b₀ :=
    (arming_vote_lt_early p _).1.trans_le
      ((arming_early_next p l).trans_le hc.gate_le_cut)
  obtain ⟨H, hH, hbatch⟩ := inclusion_joined_head_seats E rho h.base.cstar (l + 1)
    ⟨h.joinedPartBefore _ hv0 hvcut⟩
  have hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (l + 1))))
        (l + 1))).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
    apply inclusion_joined_rest_bound E rho h.base.cstar h.base.valid (l + 1) H
      (fun k hh hj => (hH k).mpr ⟨hh, hj⟩)
    intro o ho k hk
    obtain ⟨hm, hl⟩ := List.mem_filter.mp (List.mem_filter.mp ho).1
    change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
    rw [(Internal.clockPre_vn _ _).1] at hm
    exact ⟨i, x, o, hm, beq_iff_eq.mp hl, hk⟩
  have hraw := inclusion_gate_raw_at_tick E rho h.base.valid.toScheduleWellFormed hG
  have hresult := Option.some.inj (hraw.symm.trans hC)
  exact outageV_gate_of_good_service E rho h.base i x (l + 1) B C hx
    (outage_pending_receipt_scope h hc htransfer hx hG) H
    (Gen.V2.Duty.faulty rho).card hbatch.lt hrest
    (fun q hq => (hH q).mp hq)
    (fun q hq K hK => outage_pending_head_targets E rho h.base.valid hc htransfer hx hG
      q K ((hH q).mp hq).1 hK) hresult

/-- Actual pending actions have compatible sources at every honest node, including W.
The source discipline supplies a passed gate; prefix service supplies its result bound. -/
theorem outage_pending_sources_compatible [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (htsrc : TSrc p c E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H) :
    ∀ y r C, y ∈ rho.honest → p.actionTime r = SA.gateTime p.toParams (l + 1) →
      actionSource p c E rho y r = some (some C) → Block.Compatible C B := by
  intro y r C hy ht hC
  obtain ⟨X, G, _, hCX, hG, hXG, _, i, hi, hpass⟩ := htsrc y r C hy hC
  have hrj : r * p.R = l + 1 := Nat.le_antisymm
    ((arming_gate_le_iff p _ _).mp ht.le) ((arming_gate_le_iff p _ _).mp ht.symm.le)
  rw [hrj] at hG hi
  have hEnabled := arming_enabled_of_pass hi hpass
  have hRes := (gateResultAt_eq_gateResult p c E rho h.base.valid.toScheduleWellFormed hi).trans hG
  exact block_compatible_of_preceq_compatible (hXG C hCX)
    (outage_pending_result_compatible h hc htransfer hy hEnabled hRes)

/-- The sleep Clean producers close the full all-ticks source seed. -/
theorem outage_arming_sources_from_prefix [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (htsrc : TSrc p c E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) :=
  outage_arming_sources_on h.base.valid.toScheduleWellFormed hc
    (outage_pending_sources_compatible h htsrc hc htransfer)

end AvailableChain.FGSA.Run
end
