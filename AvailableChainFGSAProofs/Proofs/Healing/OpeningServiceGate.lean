module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningGateRead

public section

/-! H-GATE gate service at a later honest gate (plan fgsa-s5-hgate-hcommon §2.3, §3 B–C;
brief S5 H-GATE O2–O4). Fix an honest proposal Q of slot q with exact service, inside a
post-GST phase. At an honest gate of a label s > q in the phase, every live lease is
compatible with the ACTUAL raw result C of that gate (`opening_gate_guard`). A block that
every honest HEAD of label s covers then gets fresh gate service (`opening_gateService_of_cover`).
The standing hypotheses are Recovery₂, RMono, RXing and the inline last-write premise
`writes` (ruling B27, the binder of `healing_tPerm`). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.2 S1, 02 §5.4:531–541; plan H-GATE §3C (support count).
DC: INTENTIONAL if every honest HEAD of label w covers B and the gate F is at or below B,
the honest HEAD seats are clean early supporters of B at an honest gate of w. Their number
reaches the release threshold under the Recovery₂ fault bound. No exact HEAD is needed. -/
theorem opening_gate_support [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {w : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams w)
    (hhor : SA.gateTime p.toParams w ≤ rho.horizon)
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {j : Nat} {y : V} (ht : IsGateTick p c rho j y w)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho j y).fg.F) B) :
    SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w B := by
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
      (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)) w B := by
    refine ⟨fun q hq _ K he => ?_, fun q hq _ K he => hcovK q hq K _ he⟩
    rw [clockPre_fg]
    exact block_preceq_trans hFB (hcovK q hq K _ he)
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
  let vw := actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))
  have hsupp (k : Fin p.n) (hk : k ∈ H) :
      Gen.AC.Root.poolSupports vw.blocks (GridCO.cleanSupport p.toParams.engine vw w) k B = true
          := by
    have hq := (hHmem k).mp hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _, hBK⟩ :=
      fgsa_gateReceipt (hroots := hrec.base.idealization)
        E rho hE hN hDelta hC w hSync ht B hgeom k hq
        (hrec.awake _ hq _ hgst hhorv)
    exact fgsa_active_support_of_receipt E rho hE j y w k K B t hh he hv hK hslot hvs hbs hBK
  have hc := Gen.AC.Root.batch_counts vw.blocks (GridCO.lateVotes p.toParams.engine vw w)
    (GridCO.cleanSupport p.toParams.engine vw w) (GridCO.cleanSupport p.toParams.engine vw w)
    H H.card (Gen.V2.Duty.faulty rho).card B
    (fun _ ho => fgsa_early_subset_late p vw w (List.mem_filter.mp ho).1)
    (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p vw w k)
    hsupp (fgsa_late_rest_bound E rho hC hE j y w H (fun k hk _ => (hHmem k).mpr hk)) hbatch
  have hcount : H.card ≤ SA.Root.prefixSupport p.toParams vw w B := by
    have heq : SA.Root.prefixSupport p.toParams vw w B =
        GridCO.goldfishScore vw.blocks (GridCO.cleanSupport p.toParams.engine vw w)
          (GridCO.cleanSupport p.toParams.engine vw w) B :=
      actView_score p (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))
        (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j y) _)
        (by rw [clockPre_headDomain];
            exact base_headDomain_none p (reachable_stateBefore E rho j y)) _ _ B
    rw [heq]
    exact (hc.2.2.1 B (block_preceq_refl B)).1
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base (.head w)) hC trivial).symm
  have hcard : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hc' := Finset.card_le_univ rho.honest
    rw [hn] at hc'
    omega
  have hf := hrec.fault
  have hp := p.nPos
  have hτ : SA.releaseThreshold p.toParams ≤ H.card := by
    rw [hHcard]
    change (p.n + 1) / 2 ≤ rho.honest.card
    omega
  exact hτ.trans hcount

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2 S1 (permanence at later HEADs); plan H-GATE §3B (q < rR), gap 3.
DC: INTENTIONAL the exact service of Q at its gate is a fast PhaseBody, so TPerm S1 makes
Q a prefix of every honest HEAD of each label s > q whose vote time is in the phase. This
includes s = q + 1, whose HEAD v_(q+1) is before d_q: the phase reaches d_q. -/
theorem opening_heads_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqv : SA.gateTime p.toParams q ≤ v)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} (hqs : q < s)
    (hvs : SA.voteTime p.toParams s ≤ v) :
    ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq Q K := by
  have hd := p.deltaPos
  have huq : u ≤ SA.voteTime p.toParams q := by
    refine hu.trans ?_
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  obtain ⟨_, _, ⟨nd, hnd, hQnd⟩, _, _⟩ := hexact.2 (hqv.trans hphase.2.1) x hx
  have hbody : PhaseBody p c E rho q Q := ⟨x, hx, Or.inl ⟨nd, hnd, hQnd⟩⟩
  have htr := healing_tPerm E rho hrec mono crossing writes u v m J contested q Q hgst hphase
    huq hqv hbody
  intro z hz K hK
  exact htr.1 z s K hz hqs hvs hK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.1 (release), H.2 S1, H.22 H3; plan H-GATE §3C (the
intervening-gate
induction, gaps 1 and 3). DC: INTENTIONAL every live lease at an honest gate of a label
s > q in the phase is compatible with the ACTUAL raw result C of that gate. The last write
of the lease is at a gate w < s. If w < q, the q_(q+1) release removes a target that
conflicts with Q, and the slot bound of the write gate puts the target below Q. If w = q,
the target is below the exact result Q. If w > q, a fast key, or a slow key with its
synchronous window, is a PhaseBody, so TPerm makes every honest HEAD of label s cover the
target; a slow key without the window reads the saved result Q of label q. Below Q ⪯ C
the target is compatible; above Q, the gate cover gives target ⪯ C. Compatibility with
Q alone is not used: two incomparable descendants of Q are not compatible. -/
theorem opening_gate_guard [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    {s : Slot} (hqs : q < s) (hsv : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q) :
    ∀ C, (fgsaAC E rho).raw i s x = some C →
      ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvh : v ≤ rho.horizon := hphase.2.1
  have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
  have hgq : SA.gateTime p.toParams q ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith
  have hvq : u ≤ SA.voteTime p.toParams q := by
    refine hu.trans ?_
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := hgst.trans hvq
  have hvqs : SA.voteTime p.toParams q ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := hgstq.trans hvqs
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hsh : SA.gateTime p.toParams s ≤ rho.horizon := hsv.trans hvh
  have hcovQ := opening_heads_cover E rho hrec mono crossing writes hgst hphase hexact hu hgq hx
    hqs hvs
  obtain ⟨hgr, ⟨jq, hjqt, _⟩, _, _, _⟩ := hexact.2 (hgq.trans hvh) x hx
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  have hrawEq : (fgsaAC E rho).raw i s x = SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F)
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s := by
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F) u s) hv
    exact he.symm
  intro C hC
  -- A block that every honest HEAD of label s covers, above F, is below C.
  have hcoverC (b : Block)
      (hcb : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq b K)
      (hFb : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) b) : Block.Preceq b C := by
    obtain ⟨C', hC', hbC'⟩ := healing_support_gate_cover E rho hrec hgsts hsh hcb ht
      (by rw [clockPre_fg]; exact hFb)
    rw [clockPre_fg] at hC'
    have he := Option.some.inj ((hC.symm.trans hrawEq).trans hC')
    subst he
    exact hbC'
  have hQC : Block.Preceq Q C := hcoverC Q hcovQ hFQ
  have hbelowQ {b : Block} (hb : Block.Preceq b Q) : Block.Compatible b C :=
    Bool.or_eq_true_iff.mpr (Or.inl (block_preceq_trans hb hQC))
  intro lease hl
  rw [← hv] at hl
  have hl' : lease ∈ (storeAt p c E rho i x).base.obligations :=
    (clockPre_obligations_sublist p _ _).subset hl
  obtain ⟨j, hji, w, Bw, htj, hpass, hres, hbB, hkey, hdl, _, _⟩ := writes i x lease hl'
  change Block.Compatible lease.1 C
  have hwt : SA.gateTime p.toParams w < SA.gateTime p.toParams s :=
    fgsa_tick_time_strict E rho hS htj ht hji
  have hwsI : (w : Int) < (s : Int) := by
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hwt
    nlinarith
  rcases lt_trichotomy w q with hwq | hwq | hwq
  · -- An old write: the q_(q+1) release (G5), then the slot bound of the write gate.
    have hwqI : (w : Int) + 1 ≤ (q : Int) := by exact_mod_cast hwq
    have hq1v : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
      change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
      push_cast
      linarith
    have hawake := hrec.awake x hx (SA.voteTime p.toParams (q + 1)) (by
      apply hgst.trans (hu.trans _)
      change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos]) ((hq1v.trans hgq).trans hvh)
    obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hx (q + 1)
      ((hq1v.trans hgq).trans hvh) hawake
    have hjq : j < iq := by
      apply repair_idx_lt E rho hS htj hiq
      change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith
    have hqi : iq < i := by
      apply repair_idx_lt E rho hS hiq ht
      change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      nlinarith
    have hkeep := healing_lease_persist E rho hS htj (Nat.lt_succ_of_lt hjq)
      (Nat.succ_le_of_lt hqi) lease hdl hl'
    have hpost : storeAt p c E rho (iq + 1) x =
        FGSA.clock p (storeAt p c E rho iq x) (SA.voteTime p.toParams (q + 1)) := by
      change (V2.D.Run.stateBefore E rho (iq + 1) x).st = _
      rw [V2.D.Run.stateBefore_succ E rho hiq]
      simp only [V2.D.World.step, Function.update_self]
      exact tick_st (c := c) E rho _ x _
    rw [hpost] at hkeep
    have hjqi : jq ≤ i := by
      apply le_of_lt
      apply repair_idx_lt E rho hS hjqt ht
      change 4 * p.Δ * (q : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      nlinarith
    have hFjq : Block.Preceq (eraseFG (storeAt p c E rho jq x).fg.F) Q :=
      block_preceq_trans (eraseFG_preceq (mono hN jq i x hx hjqi).1) hFQ
    have hFiq : Block.Preceq (eraseFG (storeAt p c E rho iq x).fg.F) Q :=
      block_preceq_trans (eraseFG_preceq (mono hN iq i x hx hqi.le).1) hFQ
    have hcovq : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z q = some K →
        Block.Preceq Q K := by
      intro z hz K hK
      have hvqh : SA.voteTime p.toParams q ≤ rho.horizon :=
        (hvqs.trans hvs).trans hvh
      have he := Option.some.inj ((hexact.1 hvqh z hz).symm.trans hK)
      rw [← he]
      exact block_preceq_refl Q
    have hτ := opening_gate_support E rho hrec hgstq (hgq.trans hvh) hcovq hjqt hFjq
    have hvdq : SA.voteTime p.toParams q + E.Δ ≤ SA.gateTime p.toParams q := by
      rw [hDelta]
      change 4 * p.Δ * (q : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
      linarith
    have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
      hrec.sync (fgsaDelay_nonrow E.Δ _) hgstq hvdq (hgq.trans hvh)
    have hcq := healing_support_release_compat (hroots := hrec.base.idealization)
      E rho hE hN hDelta q hSync hx hx hjqt hiq hτ
      hFiq lease hkeep
    obtain ⟨hBm, hBs⟩ := opening_result_slot E rho hS htj hres
    have hQs := repair_proposal_slot E rho hQ
    rcases Bool.or_eq_true_iff.mp hcq with hlQ | hQl
    · exact hbelowQ hlQ
    · by_cases heq : Q = Bw
      · subst heq
        exact hbelowQ hbB
      · exfalso
        have hlt := repair_stored_slot_lt E rho hE j x hBm (block_preceq_trans hQl hbB) heq
        rw [hQs] at hlt
        have key : ∀ a b d : Nat, b < a → a < d → d ≤ b + 1 → False := by
          intro a b d h1 h2 h3
          omega
        exact key q w Bw.slot hwq hlt hBs
  · -- The write gate of label q: its exact result is Q.
    subst hwq
    have hres' : gateResult p c E rho x w = some (some Bw) :=
      (gateResultAt_eq_gateResult p c E rho hS htj).symm.trans hres
    have hBQ : Bw = Q := Option.some.inj (Option.some.inj (hres'.symm.trans hgr))
    subst hBQ
    exact hbelowQ hbB
  · -- A later write gate w with q < w < s.
    obtain ⟨_, _, _, _, hcase⟩ := healing_support_key_cases p hkey
    have hwqI : (q : Int) + 1 ≤ (w : Int) := by exact_mod_cast hwq
    have hwv : SA.gateTime p.toParams w ≤ v := hwt.le.trans hsv
    have huw : u ≤ SA.voteTime p.toParams w := by
      refine hvq.trans ?_
      change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      nlinarith
    have hbody : PhaseBody p c E rho w lease.1 ∨ Block.Preceq lease.1 Q := by
      by_cases hwin : q + p.k ≤ w + 1
      · left
        refine healing_support_phaseBody_of_write p c E rho hS hx htj hpass hres hkey ?_
        refine hgstq.trans ?_
        change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * ((w + 1 - p.k : Nat) : Int) + p.Δ
        have h1 : (q : Int) ≤ ((w + 1 - p.k : Nat) : Int) := by
          exact_mod_cast Nat.le_sub_of_add_le hwin
        nlinarith
      · rcases hcase with hfast | hslow
        · exact Or.inl (opening_phaseBody_of_fast_key E rho hS hx htj hpass hres hkey hfast)
        · -- A slow key without its window: the slow test reads the saved result of q.
          right
          unfold GridCO.slowEligible at hslow
          have hall := (Bool.and_eq_true_iff.mp hslow).2
          have hidx : w - q - 1 ∈ List.range (p.toParams.engine.m - 1) := by
            apply List.mem_range.mpr
            change w - q - 1 < p.k - 1
            have key : ∀ a b k : Nat, b < a → ¬ (b + k ≤ a + 1) → a - b - 1 < k - 1 := by
              intro a b k h1 h2
              omega
            exact key w q p.k hwq hwin
          have hj := List.all_eq_true.mp hall _ hidx
          have hwq' : w - (w - q - 1 + 1) = q := by
            have key : ∀ a b : Nat, b < a → a - (a - b - 1 + 1) = b := by
              intro a b h
              omega
            exact key w q hwq
          rw [hwq'] at hj
          have hsg : GridCO.savedGenuine (actView (clockPre p (storeAt p c E rho j x)
              (SA.gateTime p.toParams w))) q =
              GridCO.savedGenuine (storeAt p c E rho j x).base q := by
            unfold GridCO.savedGenuine
            change ((clockPre p (storeAt p c E rho j x)
              (SA.gateTime p.toParams w)).base.genuine.find? _).map _ = _
            rw [clockPre_genuine]
          rw [hsg] at hj
          cases hsv' : GridCO.savedGenuine (storeAt p c E rho j x).base q with
          | none =>
            rw [hsv'] at hj
            exact absurd hj Bool.false_ne_true
          | some o =>
            cases o with
            | none =>
              rw [hsv'] at hj
              exact absurd hj Bool.false_ne_true
            | some C' =>
              rw [hsv'] at hj
              obtain ⟨_, _, _, hgC⟩ := healing_saved_origin E rho hS hN hsv'
              have hCQ : C' = Q := Option.some.inj (Option.some.inj (hgC.symm.trans hgr))
              subst hCQ
              exact hj
    rcases hbody with hbody | hlQ
    · have hcovb := (healing_tPerm E rho hrec mono crossing writes u v m J contested w lease.1
        hgst hphase huw hwv hbody).1
      have hcb : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
          Block.Preceq lease.1 K :=
        fun z hz K hK => hcovb z s K hz (by exact_mod_cast (show (w : Int) + 1 ≤ (s : Int) by
          omega)) hvs hK
      have hawake := hrec.awake x hx (SA.voteTime p.toParams s) hgsts (hvs.trans hvh)
      obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hx s
        (hvs.trans hvh) hawake
      have hhl : headAtLabel p c E rho x s = some (headVote p (FGSA.clock p
          (V2.D.Run.stateBefore E rho jz x).st (SA.voteTime p.toParams s)) s) := by
        unfold headAtLabel
        rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
        rfl
      rcases block_preceq_total_of_common (hcb x hx _ hhl) (hcovQ x hx _ hhl) with hlQ | hQl
      · exact hbelowQ hlQ
      · exact Bool.or_eq_true_iff.mpr
          (Or.inl (hcoverC lease.1 hcb (block_preceq_trans hFQ hQl)))
    · exact hbelowQ hlQ

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2 S1, H.22:3207–3216 (G1), spec 899–921; plan H-GATE §3C.
DC: INTENTIONAL fresh gate service at an honest gate of a label s > q in the phase, for a
stored non-genesis block B above the gate F that every honest HEAD of label s covers. The
raw result covers B (`healing_support_gate_cover`), B has release-threshold support
(`opening_gate_support`), and the guard holds for the actual raw result
(`opening_gate_guard`). GateService at s is a conclusion, never a premise. -/
theorem opening_gateService_of_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    {s : Slot} (hqs : q < s) (hsv : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q) {B : Block}
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq B K)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) B)
    (hB : B ∈ (storeAt p c E rho i x).base.blocks) (hne : B ≠ .genesis) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i s x B := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hsh : SA.gateTime p.toParams s ≤ rho.horizon := hsv.trans hphase.2.1
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hgst.trans (hu.trans ?_)
    have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  obtain ⟨C, hC, hBC⟩ := healing_support_gate_cover E rho hrec hgsts hsh hcov ht
    (by rw [clockPre_fg]; exact hFB)
  rw [clockPre_fg] at hC
  have hraw : (fgsaAC E rho).raw i s x = some C := by
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F) u s) hv
    have he' : (fgsaAC E rho).raw i s x = SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho i x).fg.F)
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s := he.symm
    exact he'.trans hC
  have hτ := opening_gate_support E rho hrec hgsts hsh hcov ht hFB
  have hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s B := by
    have he := congrArg (fun u => SA.Root.prefixSupport p.toParams u s B) hv
    exact he ▸ hτ
  have hb0 : B ∈ (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).base.blocks := by
    rw [(clockPre_fields p _ _).2.1]
    exact hB
  have hmem : B ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    refine (actView_blocks _ B).mpr ⟨hb0, ?_⟩
    rw [clockPre_fg]
    exact Bool.or_eq_true_iff.mpr (Or.inr hFB)
  have hmemw : B ∈ ((fgsaAC E rho).gateView i x s).blocks :=
    (congrArg GridCO.State.blocks hv) ▸ hmem
  exact fgsa_gate_of_coveringBatch E rho hS i s x B ht ⟨C, hraw, hBC⟩
    (opening_gate_guard E rho hrec mono crossing writes hgst hphase hQ hexact hu hqs hsv hx ht
      hFQ) hne hmemw hsupport (opening_gate_level E rho i x s B hsupport)

end AvailableChain.FGSA.Run
end
