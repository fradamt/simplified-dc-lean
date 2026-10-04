module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6S

public section

/-! H-REPAIR (plan steps 1, 7, 10–13; blueprint 21 H.6:910–986, H.6-S:988–1052). The two
repair branches and `healing_tRepair : TRepair`. Recovery₂ is a standing hypothesis (plan
Gap 1); the other hypotheses are RMono, RXing, RQCOrigin and the inline last-write premise
(ruling B27). TRepair quantifies its own gap G; only its ProposalGap is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Plan H-REPAIR step 11 (HonestSlot → HonestProposal); Run/Emission.lean:72.
DC: INTENTIONAL the honest proposer of a post-GST slot inside the horizon ticks at t_s
(tick totality), is awake (Recovery₂) and emits its proposal (s ≠ 0). -/
theorem repair_honest_proposal [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) {s : Slot}
    (hs : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hh : SA.proposalTime p.toParams s ≤ rho.horizon) :
    ∃ Q, HonestProposal E rho (fgsaInterface p c) s Q := by
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hs0, hx⟩ := hs
  have htime : ((4 * s : Nat) : Time) * p.Δ = SA.proposalTime p.toParams s := by
    change ((4 * s : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int)
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hS hrec.base.delta _ hx (4 * s) (htime ▸ hh)
  rw [htime] at hj
  have hawake := hrec.awake _ hx _ hgst hh
  have hne : s ≠ 0 := Nat.pos_iff_ne_zero.mp hs0
  obtain ⟨m, hm⟩ : ∃ m, (propose p (FGSA.clock p (rho.stateBefore E j
      (V2.D.proposerOf rho (fgsaInterface p c) s)).st (SA.proposalTime p.toParams s)) s).map
      (withApp p (c.app (rho.input (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)))) = some m := by
    unfold propose
    simp only [hne, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq']
  have hblock : ∃ Q, (fgsaInterface p c).block m = some Q := by
    unfold propose at hm
    simp only [hne, ↓reduceIte, Option.map_some, Option.some.injEq] at hm
    subst hm
    exact ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ := hblock
  have hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩ : Obj p) ∈ V2.D.Run.emitsAt E rho j := by
    rw [(V2.D.Run.step_tick_eq E rho hj).2]
    exact (fgsa_emits_proposal E rho _ _ _ s m).mpr ⟨hawake, rfl, rfl, hm⟩
  exact ⟨Q, ⟨hs0, hx⟩, ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩, ⟨j, hj, hem⟩, hQ⟩

/-- Plan H-REPAIR step 11. DC: INTENTIONAL GUP r2 uses the rounded-up gap. -/
theorem repair_grid_Γ {Gp : Time} {l s : Nat}
    (hs : SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams l + Gp) :
    SA.proposalTime p.toParams s ≤ SA.proposalTime p.toParams l + Γ p Gp := by
  linarith [(fgsa_gamma_bounds p Gp).1]

/-- Plan H-REPAIR step 11. DC: INTENTIONAL GUP r2 has G ≤ Γ. -/
theorem repair_lt_Γ (Gp : Time) : Gp < Γ p Gp + 4 * p.Δ := by
  have := (fgsa_gamma_bounds p Gp).1
  linarith [p.deltaPos]

/-- Blueprint 21 H.6:965–986; plan H-REPAIR steps 9–10. DC: INTENTIONAL exact gate service of
an honest proposal of slot r + 1 inside the phase, from the lease cover of its preceding
HEAD batch (u ≤ v_r) and the gate geometry. -/
theorem repair_exact_service [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {r : Nat} (hhead : u ≤ SA.voteTime p.toParams r)
    (hlease : RepairLeaseCover E rho (r + 1))
    (hgate : SA.gateTime p.toParams (r + 1) ≤ v) {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) (r + 1) Q) :
    ExactService p c E rho (r + 1) Q := by
  have hd := p.deltaPos
  have hvq : SA.voteTime p.toParams (r + 1) ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hus : u ≤ SA.voteTime p.toParams (r + 1) := by
    refine hhead.trans ?_
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hQs := repair_proposal_slot E rho hp
  have hheadQ := repair_head_exact E rho hrec mono crossing hgst hphase hhead hvq hlease hp
  have hne : Q ≠ .genesis := by
    rintro rfl
    exact Nat.succ_ne_zero r hQs.symm
  exact exactService_of_head_recovery E rho G hrec (r + 1) Q hne (hgst.trans hus)
    (fun _ => hheadQ) (fun _ _ hx ht => repair_gate_geometry E rho hrec mono crossing qc
      writes hgst hphase hus hgate hQs hheadQ hx ht)

/-- Blueprint 21 H.6:749–756 (RepairAfter); plan H-REPAIR step 10. DC: INTENTIONAL every
later honest proposal s with d_s ≤ v has exact service once the lease cover holds after
the threshold l and u ≤ v_l. -/
theorem repair_after_of_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {l : Nat} (hlu : u ≤ SA.voteTime p.toParams l)
    (hcover : ∀ s, SA.proposalTime p.toParams l < SA.proposalTime p.toParams s →
      SA.voteTime p.toParams s ≤ v → RepairLeaseCover E rho s) :
    RepairAfter p c E rho l v := by
  intro s Q hls hgate hp
  have hlt := repair_slot_lt_of_time hls
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt hlt)
  have hd := p.deltaPos
  have hlr : (l : Int) ≤ r := by omega
  have hhead : u ≤ SA.voteTime p.toParams r := by
    refine hlu.trans ?_
    change 4 * p.Δ * (l : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
    nlinarith
  have hvs : SA.voteTime p.toParams (r + 1) ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  exact repair_exact_service E rho hrec mono crossing qc writes hgst hphase hhead
    (hcover _ hls hvs) hgate hp

/-- Blueprint 21 H.6:910–986 (two leases); plan H-REPAIR steps 3, 4, 10–12 (R4).
DC: INTENTIONAL with β the first proposal after u: RepairAfter (β + 2k − 1) v, and inside
u + ρΓ an honest proposal after t_(β+2k−1) with exact service. The gap window is G (not Γ);
Γ bounds the slot found. -/
theorem repair_two_lease [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    {Gp : Time} (hgap : ProposalGap p c E rho Gp)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Nat} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b) :
    RepairAfter p c E rho (β + 2 * p.k - 1) v ∧
    (u + ρΓ p Gp ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s ≤ u + ρΓ p Gp ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q) := by
  have hd := p.deltaPos
  have hk := p.kLarge
  have hu0 : 0 ≤ u := E.t_GST_nonneg.trans hgst
  have hβ1 : 1 ≤ β := by
    by_contra h0
    have hb0 : β = 0 := by omega
    subst hb0
    change u < 4 * p.Δ * ((0 : Nat) : Int) at hβ
    simp only [Nat.cast_zero, mul_zero] at hβ
    linarith
  have hβu : SA.proposalTime p.toParams β ≤ u + 4 * p.Δ := by
    by_contra hc
    have hc' : u < SA.proposalTime p.toParams (β - 1) := by
      change ¬ (4 * p.Δ * (β : Int) ≤ u + 4 * p.Δ) at hc
      change u < 4 * p.Δ * ((β - 1 : Nat) : Int)
      have e : ((β - 1 : Nat) : Int) = (β : Int) - 1 := by omega
      rw [e]
      linarith
    have := hmin (β - 1) hc'
    omega
  have hcl : ((β + 2 * p.k - 1 : Nat) : Int) = (β : Int) + 2 * p.k - 1 := by omega
  have htl : SA.proposalTime p.toParams (β + 2 * p.k - 1) ≤ u + 8 * p.k * p.Δ := by
    change 4 * p.Δ * (β : Int) ≤ u + 4 * p.Δ at hβu
    change 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int) ≤ u + 8 * p.k * p.Δ
    rw [hcl]
    linarith
  have hlu : u ≤ SA.voteTime p.toParams (β + 2 * p.k - 1) := by
    refine hβ.le.trans ?_
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int) + p.Δ
    rw [hcl]
    have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
    nlinarith
  have hafter : RepairAfter p c E rho (β + 2 * p.k - 1) v :=
    repair_after_of_cover E rho hrec mono crossing qc writes hgst hphase hlu
      (fun _ hls hvs => repair_lease_cover_two E rho hrec mono crossing writes hgst hphase hβ
        hls hvs)
  refine ⟨hafter, fun hbud => ?_⟩
  have hβl : SA.proposalTime p.toParams β ≤ SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int)
    rw [hcl]
    have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
    nlinarith
  have hGl : E.t_GST ≤ SA.proposalTime p.toParams (β + 2 * p.k - 1) :=
    hgst.trans (hβ.le.trans hβl)
  have hlt := repair_lt_Γ (p := p) Gp
  have hhor : SA.proposalTime p.toParams (β + 2 * p.k - 1) + Gp ≤ rho.horizon := by
    refine le_trans ?_ (hbud.trans hphase.2.1)
    change _ ≤ u + (2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p Gp + 8 * p.Δ)
    linarith
  obtain ⟨s, hs1, hs2, hslot⟩ := hgap _ hGl hhor
  rw [proposalTime_fgsa] at hs1 hs2
  have hsΓ := repair_grid_Γ (p := p) hs2
  have hds : SA.gateTime p.toParams s ≤ u + ρΓ p Gp := by
    change 4 * p.Δ * (s : Int) ≤ _ at hsΓ
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
      u + (2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p Gp + 8 * p.Δ)
    linarith
  have hts : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  obtain ⟨Q, hp⟩ := repair_honest_proposal E rho hrec hslot (hGl.trans hs1.le)
    ((hts.trans (hds.trans hbud)).trans hphase.2.1)
  exact ⟨s, Q, hs1, hds, hp, hafter s Q hs1 (hds.trans hbud) hp⟩

/-- Blueprint 21 H.6-S:988–1052 (one lease); plan H-REPAIR steps 3, 5, 10–12 (R4).
DC: INTENTIONAL with b the first HEAD label at or after u and the synchronous window
GST ≤ v_(b+1−k): RepairAfter (b + k) v, and strictly inside u + ρ₁ an honest proposal after
t_(b+k) with exact service. The budget keeps the strict bound for b. -/
theorem repair_synchronous [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    {Gp : Time} (hgap : ProposalGap p c E rho Gp)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Nat} (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) :
    RepairAfter p c E rho (b + p.k) v ∧
    (u + ρ₁ p Gp ≤ v → ∃ s Q,
      SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s ∧
      SA.gateTime p.toParams s < u + ρ₁ p Gp ∧
      HonestProposal E rho (fgsaInterface p c) s Q ∧ ExactService p c E rho s Q) := by
  have hd := p.deltaPos
  have hk := p.kLarge
  have hk' : (2 : Int) ≤ p.k := by exact_mod_cast hk
  have hu0 : 0 ≤ u := E.t_GST_nonneg.trans hgst
  have htb : SA.proposalTime p.toParams b < u + 3 * p.Δ := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      change 4 * p.Δ * ((0 : Nat) : Int) < u + 3 * p.Δ
      simp only [Nat.cast_zero, mul_zero]
      linarith
    · by_contra hc
      have hc' : u ≤ SA.voteTime p.toParams (b - 1) := by
        change ¬ (4 * p.Δ * (b : Int) < u + 3 * p.Δ) at hc
        change u ≤ 4 * p.Δ * ((b - 1 : Nat) : Int) + p.Δ
        have e : ((b - 1 : Nat) : Int) = (b : Int) - 1 := by omega
        rw [e]
        linarith
      have := hmin (b - 1) hc'
      omega
  have hlu : u ≤ SA.voteTime p.toParams (b + p.k) := by
    refine hb.trans ?_
    change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * ((b + p.k : Nat) : Int) + p.Δ
    push_cast
    nlinarith
  have hafter : RepairAfter p c E rho (b + p.k) v :=
    repair_after_of_cover E rho hrec mono crossing qc writes hgst hphase hlu
      (fun _ hls hvs => repair_lease_cover_one E rho hrec mono crossing writes hgst hphase hb
        hwindow hls hvs)
  refine ⟨hafter, fun hbud => ?_⟩
  have htl : SA.proposalTime p.toParams (b + p.k) < u + 4 * p.k * p.Δ + 3 * p.Δ := by
    change 4 * p.Δ * (b : Int) < u + 3 * p.Δ at htb
    change 4 * p.Δ * ((b + p.k : Nat) : Int) < u + 4 * p.k * p.Δ + 3 * p.Δ
    push_cast
    linarith
  have hGl : E.t_GST ≤ SA.proposalTime p.toParams (b + p.k) := by
    refine hgst.trans (hb.trans ?_)
    change 4 * p.Δ * (b : Int) + p.Δ ≤ 4 * p.Δ * ((b + p.k : Nat) : Int)
    push_cast
    nlinarith
  have hlt := repair_lt_Γ (p := p) Gp
  have hhor : SA.proposalTime p.toParams (b + p.k) + Gp ≤ rho.horizon := by
    refine le_trans ?_ (hbud.trans hphase.2.1)
    change _ ≤ u + ((4 * (p.k : Time) - 1) * p.Δ + Γ p Gp + 10 * p.Δ)
    linarith
  obtain ⟨s, hs1, hs2, hslot⟩ := hgap _ hGl hhor
  rw [proposalTime_fgsa] at hs1 hs2
  have hsΓ := repair_grid_Γ (p := p) hs2
  have hds : SA.gateTime p.toParams s < u + ρ₁ p Gp := by
    change 4 * p.Δ * (s : Int) ≤ _ at hsΓ
    change 4 * p.Δ * (s : Int) + 6 * p.Δ < u + ((4 * (p.k : Time) - 1) * p.Δ + Γ p Gp + 10 * p.Δ)
    linarith
  have hts : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  obtain ⟨Q, hp⟩ := repair_honest_proposal E rho hrec hslot (hGl.trans hs1.le)
    ((hts.trans (hds.le.trans hbud)).trans hphase.2.1)
  exact ⟨s, Q, hs1, hds, hp, hafter s Q hs1 (hds.le.trans hbud) hp⟩

/-- T-REPAIR (ChannelProps.lean:917; blueprint 21 H.6:749–756, 910–986, H.6-S:988–1052);
plan H-REPAIR steps 1, 13 (R5). DC: INTENTIONAL the exact frozen TRepair under the standing
Recovery₂ (plan Gap 1: unconditional TRepair is false on arbitrary runs). The other
hypotheses are RMono, RXing, RQCOrigin (FGFoundation fields with producers on main) and the
inline last-write premise (ruling B27), as in healing_tPerm. -/
theorem healing_tRepair [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C) :
    TRepair p c E rho := by
  intro Gp u v m J contested hgap _ hgst hphase
  exact ⟨fun _ hβ hmin => repair_two_lease E rho hrec mono crossing qc writes hgap hgst
      hphase hβ hmin,
    fun _ hb hmin _ hwindow => repair_synchronous E rho hrec mono crossing qc writes hgap
      hgst hphase hb hmin hwindow⟩

end AvailableChain.FGSA.Run
end
