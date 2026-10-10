module
public import AvailableChainFGSAProofs.Proofs.Finality.Rows
public import AvailableChainFGSAProofs.Proofs.Finality.RowsBatch
public import AvailableChainFGSAProofs.Proofs.Finality.RowsRecords

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

include hK in
/-- Paper 22:1228–1254: K-ROWS T1 at the actual action read. P1, P2 and P3 feed the
full action walk; K-MID's held caps through the action bound its head fields.
DC: INTENTIONAL: height plateau and finality lag from K-MID; no exact head body. -/
theorem rowsPrem_pending_head
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ∃ H : FGBlock (Fin p.n),
        FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧ FGBlock.Preceq m.X_D H ∧
        (heightView p H).h = m.d + 2 ∧ (heightView p H).J = m.U ∧
        (heightView p H).h_j = m.d + 1 ∧ (finalityView p H).h_F < m.d + 1 ∧
        (heightView p H).T_h = (heightView p m.X_D).T_h := by
  intro x nd hx hnd
  have hread := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
    x _ nd hnd
  have hi : afterTicksIdx rho (p.actionTime (pt.r + 2)) ≤ rho.events.length :=
    List.length_filter_le _ _
  have hwb := rowsPrem_action_walk_batch p c E rho hK m hServices hQC hXing hNames x nd hx hnd
  exact pending_action_head_capped p c E rho _ x (pt.r + 2) (m.d + 1) m.X_D m.U nd _ _ _ _
    hx hnd hread hK.services.walk hwb.2.2 hwb.1
    (rowsPrem_full_domain p c E rho hK m hQC hXing hNames x nd hx hnd)
    (rowsPrem_liveRoot_compatible p c E rho hK m hQC hXing hNames x nd hx hnd)
    hwb.2.1 m.heightD m.justifiedD m.justifiedHeightD
    (fun B hB => m.capThroughFinalAction _ x B hi le_rfl ⟨hx, by rw [hread]; exact hB⟩)
    (fun B hB => m.finalityThroughFinalAction _ x B hi le_rfl ⟨hx, by rw [hread]; exact hB⟩)

include hK in
/-- Paper 22:1256–1257,1667–1700: K-ROWS source step at the actual action read.
P4 gives the gate guard and P5 the source filter guards for the H3/H6 split.
DC: INTENTIONAL: deepest fresh FG-SA selector; height plateau fixes the same entry. -/
theorem rowsPrem_action_source
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x ∈ rho.honest, ∃ nd C,
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd ∧
      FGSA.fgSource p nd.st = some C ∧ FGBlock.Preceq m.X_D C ∧
      (heightView p C).h = m.d + 2 ∧ (heightView p C).T_h = (heightView p m.X_D).T_h := by
  intro x hx
  obtain ⟨_, hκ2, _, _, hs2, hGST, _⟩ := kmid_kernel_bounds hK
  have hs := hK.set.base.valid.toScheduleWellFormed
  have hrD : pt.r * p.R ≤ m.cD := by
    have := m.earlySlot.1
    have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
    omega
  have hne : eraseFG m.X_D ≠ .genesis := by
    intro h
    have hslot := m.slotD
    rw [eraseFG_eq_genesis.mp h] at hslot
    have h0 : (0 : Nat) = m.cD := hslot
    have := m.earlySlot.1
    omega
  have hGSTq : E.t_GST ≤ SA.voteTime p.toParams ((pt.r + 2) * p.R) := by
    refine hGST.trans ?_
    have hle := kmid_slot_scale_le p (Nat.mul_le_mul_right p.R
      (show pt.r ≤ pt.r + 2 by omega))
    have hd := p.deltaPos
    change 4 * p.Δ * ((pt.r * p.R : Nat) : Time) ≤
      4 * p.Δ * (((pt.r + 2) * p.R : Nat) : Time) + p.Δ
    linarith
  have hheads : ∀ y ∈ rho.honest, ∃ H,
      headAtLabel p c E rho y ((pt.r + 2) * p.R) = some H := by
    intro y hy
    have hvt : ((4 * ((pt.r + 2) * p.R) + 1 : Nat) : Time) * p.Δ =
        SA.voteTime p.toParams ((pt.r + 2) * p.R) := by
      change ((4 * ((pt.r + 2) * p.R) + 1 : Nat) : Int) * p.Δ =
        4 * p.Δ * (((pt.r + 2) * p.R : Nat) : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hK.set.base.delta y hy _
      (hvt ▸ (kmid_slot_horizon hK le_rfl).2.1)
      (hvt ▸ hK.set.awake y hy _ hGSTq (kmid_slot_horizon hK le_rfl).2.1)
    rw [hvt] at hk
    have hH : headAtLabel p c E rho y ((pt.r + 2) * p.R) =
        some (FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
          (SA.voteTime p.toParams ((pt.r + 2) * p.R))).st ((pt.r + 2) * p.R)) := by
      change (postClock E rho y (SA.voteTime p.toParams ((pt.r + 2) * p.R))).map
        (fun nd => FGSA.headVote p nd.st ((pt.r + 2) * p.R)) = _
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
      rfl
    exact ⟨_, hH⟩
  have hi : afterTicksIdx rho (p.actionTime (pt.r + 2)) ≤ rho.events.length :=
    List.length_filter_le _ _
  exact finality_action_source p c E rho pt.w (pt.r + 2) (m.d + 1) m.cD m.X_D x hx
    m.earlySlot.2 (hs2.trans hrD) m.honestD hK.input.ac.h2' hK.input.ac.h3 hK.input.ac.h6
    (by
      apply finality_recoveryStart_le_vote p E ((pt.r + 2) * p.R) (by
        have hR2 := (kmid_kernel_bounds hK).2.2.2.1
        have hle : p.R ≤ (pt.r + 2) * p.R := by rw [Nat.add_mul]; omega
        exact hR2.trans hle)
      have hsync := hK.input.wit.synchronous
      have hstart := hK.start
      rw [kmid_period_eq] at hstart
      have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
        exact_mod_cast hK.input.wit.proposal_lower
      have hR : 2 ≤ p.R := (kmid_kernel_bounds hK).2.2.2.1
      have hle := kmid_slot_scale_le p (show pt.r * p.R + 2 ≤ (pt.r + 2) * p.R by
        rw [Nat.add_mul]; omega)
      change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
      change 4 * p.Δ * (pt.w.u : Int) + 6 * p.Δ ≤ _ at hstart
      change E.t_GST ≤ 4 * p.Δ * (_ - 2)
      push_cast at hle hstart ⊢
      nlinarith [p.deltaPos]) m.actionsInRun hne hheads
    (fun y hy => kmid_window_joined hK
      (Nat.mul_le_mul_right p.R (by omega)) le_rfl hy)
    (kmid_window_confirmed hK (by omega) (by
      have hle := kmid_slot_scale_le p m.earlySlot.2
      have hh := m.actionsInRun
      rw [kmid_actionTime_eq] at hh
      change 4 * p.Δ * (m.cD : Int) + 6 * p.Δ ≤ rho.horizon
      linarith) hx) (rowsPrem_F_below_D_at_gate p c E rho hK m hXing)
    (fun nd hnd => by
      have hf := rowsPrem_action_frame p c E rho hK m hQC hXing hNames x nd hx hnd
      exact ⟨hf.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2⟩)
    m.heightD
    (fun nd hnd B hB => by
      have hread := rowsPrem_postClock_store p c E rho hs x _ nd hnd
      exact m.capThroughFinalAction _ x B hi le_rfl ⟨hx, by rw [hread]; exact hB⟩)

include hK in
/-- Paper 22:1256–1263: K-ROWS fresh rows at the actual action. The source step, the
pending head fields and P6's record guards give one complete fresh row per honest seat.
DC: INTENTIONAL: durable record and both send-once checks; source ancestry fixes the entry. -/
theorem rowsPrem_fresh_rows
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (S : Finset (Fin p.n)) (hS : S ⊆ honestSeats p c rho) (hQ : p.E.IsQuorum S) :
    ∃ rows : Fin p.n → RowWire p.n,
      FreshFinalityRows_W p c E rho (pt.r + 2) (m.d + 1) m.U S rows ∧
      (∀ i ∈ S, namedEntry (rows i).payload.height_pair =
        some (m.d + 2, (heightView p m.X_D).T_h.root)) ∧
      (∀ i ∈ S, (rows i).payload.height_pair =
        NamedHeightPair.vote (m.d + 2) (heightView p m.X_D).T_h.root false) := by
  obtain ⟨_, _, _, _, _, hGST, _⟩ := kmid_kernel_bounds hK
  have hhonest : ∀ i ∈ S, rho.seatOf (.base .fg) i ∈ rho.honest := by
    intro i hi
    classical
    have hm := hS hi
    unfold honestSeats at hm
    exact (Finset.mem_filter.mp hm).2
  have hGSTa : E.t_GST ≤ p.actionTime (pt.r + 2) := by
    refine hGST.trans ?_
    have hle := kmid_slot_scale_le p (Nat.mul_le_mul_right p.R
      (show pt.r ≤ pt.r + 2 by omega))
    have hd := p.deltaPos
    change 4 * p.Δ * ((pt.r * p.R : Nat) : Time) ≤
      4 * p.Δ * (((pt.r + 2) * p.R : Nat) : Time) + 6 * p.Δ
    linarith
  exact fresh_unanimous_rows p c E rho (pt.r + 2) (m.d + 1) m.X_D m.U S hS hQ m.heightD
    (fun i hi => by
      obtain ⟨nd, C, hnd, hsrc, hDC, hCh, _⟩ := rowsPrem_action_source p c E rho hK m hQC
        hXing hNames _ (hhonest i hi)
      exact ⟨nd, C, hnd, hK.set.awake _ (hhonest i hi) _ hGSTa m.actionsInRun, hsrc, hDC,
        hCh⟩)
    (fun i hi nd hnd => by
      obtain ⟨H, hH, _, _, hHJ, hHj, hHF, _⟩ := rowsPrem_pending_head p c E rho hK m hServices hQC
        hXing hNames _ nd (hhonest i hi) hnd
      rw [fgInputs_headFields p nd.st H hH]
      exact ⟨hHj, congrArg FGBlock.root hHJ, hHF⟩)
    (fun i hi nd hnd => rowsPrem_action_record p c E rho m hK hQC hNames _ nd
      (hhonest i hi) hnd)
    (fun i _ j r a h hr ha hh => rowsPrem_earlier_height p c E rho (pt.r + 2) (m.d + 2)
      m.noSecondHeight j _ r a h hr ha hh)

include hK in
/-- Paper 22:1265–1289: held blocks through the next action cut have height at most d+3.
Emitted names put each earlier honest row at its action source; K-MID caps that source.
DC: INTENTIONAL: held/read causal cap; Assembly supplies the causal-origin bound. -/
theorem rowsPrem_anchor_cap
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hcapBefore : ∀ (cut : Time) (b i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      i ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho i x W →
      (∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
        RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) →
      (heightView p W).h < b + 2) :
    ∀ i x W, i ≤ V2.D.Run.idxBefore rho (p.actionTime (pt.r + 3)) →
      HeldAt p c E rho i x W → (heightView p W).h ≤ m.d + 3 := by
  refine actual_anchor_cap p c E rho (pt.r + 2) (m.d + 1) hcapBefore ?_
  intro j x r a u h T timeout ha hu hv hr
  have hpair : a.payload.height_pair = u.height_pair := by
    rw [kmid_wire_decode p hu]
    rfl
  obtain ⟨C, hsrc, he⟩ := hNames j x r a (h, T) ha (by rw [hpair, hv]; rfl)
  have hx : x ∈ rho.honest := ((HonestRowAt_def p c E rho _ _ _ _).mp ha).1
  obtain ⟨i, _, hilt, hheld⟩ := kmid_source_held_at_tick p c E rho
    hK.set.base.valid.toScheduleWellFormed hx hsrc
  have hrq : r ≤ pt.r + 2 := by
    by_contra hn
    exact absurd hr (not_lt.mpr ((kmid_action_strictMono p).monotone (by omega)))
  have hcut := afterTicksIdx_mono rho ((kmid_action_strictMono p).monotone hrq)
  have hC := m.capThroughFinalAction i x C (hilt.le.trans (List.length_filter_le _ _))
    (hilt.le.trans hcut) hheld
  have hh : h = (heightView p C).h := congrArg Prod.fst he
  rw [hh]
  exact hC

/-- Paper 22:1265–1289: the anchor carrier keeps the actual pending key or is covered.
DC: INTENTIONAL: W retention with K_W ≥ 2 at K-MID's retained D; no acceptance claim. -/
theorem rowsPrem_anchor_retained_or_covered (P : FGBlock (Fin p.n))
    (hDP : FGBlock.Preceq m.X_D P) (hcap : (heightView p P).h ≤ m.d + 3) :
    Window.RetainedW p P (m.d + 1) m.U ∨ Window.CoveredW p P (m.d + 1) m.U :=
  actual_anchor_retained_or_covered p (m.d + 1) m.X_D m.U P hDP m.retainedD hcap

end AvailableChain.FGSA.Run
end
