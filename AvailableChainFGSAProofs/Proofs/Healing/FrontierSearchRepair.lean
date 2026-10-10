module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.Frame
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle

public section

/-! Blueprint 21 HG.3; run 2 R2-b.
Settlement uses healing_settle_start, including the inclusive cut.
The TRepair input has producer healing_tRepair. It retains both first labels.
No weak served witness is used to construct a seed. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME inclusive-prefix monotonicity. -/
theorem frontierSearch_timeIdx_mono (rho : V2.D.Run V (fgsa p c))
    {u v : Time} (h : u ≤ v) : timeIdx rho u ≤ timeIdx rho v := by
  change (rho.events.filter (fun e => decide (e.time ≤ u))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ v))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    ((of_decide_eq_true he).trans h))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME a shorter phase keeps the lower read cut. -/
theorem frontierSearch_phase_cut (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {u v w : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hp : PhaseInterval p c E rho u v m J contested) (huw : u ≤ w) (hwv : w ≤ v) :
    PhaseInterval p c E rho u w m J contested := by
  refine ⟨huw, hwv.trans hp.2.1, hp.2.2.1, ?_⟩
  intro i x hui hiw hx
  exact hp.2.2.2 i x hui (hiw.trans (frontierSearch_timeIdx_mono rho hwv)) hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 H.6/H.6-S and HG.3. DC: SAME full frozen seed adapters. -/
theorem frontierSearch_repair_seed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (repair : TRepair p c E rho)
    {G u v ρbar : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G)
    (hgst : E.t_GST ≤ u) (hp : PhaseInterval p c E rho u v m J contested)
    (mode : FrontierRepairStart p E G u ρbar) (hbudget : u + ρbar ≤ v) :
    ∃ q Q, FrontierSeedQualification p E u q ∧
      SA.gateTime p.toParams q ≤ u + ρbar ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q := by
  cases mode with
  | two β after least =>
    exact tfSeed_two_from_tRepair p c E rho repair hgap hG hgst hp after least hbudget
  | one b after least window sync =>
    obtain ⟨q, Q, hs, hg, hQ, he⟩ :=
      tfSeed_one_from_tRepair p c E rho repair hgap hG hgst hp after least window sync hbudget
    exact ⟨q, Q, hs, hg.le, hQ, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME a seed follows its phase start in both arms. -/
theorem frontierSearch_seed_after {V : Type} (E : Generic.Env V)
    {u : Time} {q : Slot} (hseed : FrontierSeedQualification p E u q) :
    u ≤ SA.proposalTime p.toParams q := by
  have hd := p.deltaPos
  rcases (frontierSeedQualification_iff p E u q).mp hseed with
    ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
  · have hl : β ≤ β + 2 * p.k - 1 := by
      have hk : 1 ≤ 2 * p.k := by have := p.kLarge; omega
      exact Nat.le_sub_of_add_le (Nat.add_le_add_left hk β)
    have hli : (β : Time) ≤ ((β + 2 * p.k - 1 : Nat) : Time) := by exact_mod_cast hl
    have ht : SA.proposalTime p.toParams β ≤
        SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
      change 4 * p.Δ * (β : Time) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Time)
      nlinarith
    exact hβ.le.trans (ht.trans hlt.le)
  · change u ≤ 4 * p.Δ * (b : Time) + p.Δ at hb
    change 4 * p.Δ * ((b + p.k : Nat) : Time) < 4 * p.Δ * (q : Time) at hlt
    change u ≤ 4 * p.Δ * (q : Time)
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    push_cast at hlt
    nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3. DC: SAME the proposer floor and exact-gate cap. -/
theorem frontierSearch_proposal_heights [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u)
    (hp : PhaseInterval p c E rho u D m J contested)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams q ≤ D)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (heq : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q) :
    (if contested then m else m - 1) ≤ (heightView p Qfg).h ∧
      (heightView p Qfg).h ≤ m := by
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _hem, hst, _hslot, _hb, _hrows⟩ :=
    healing_promotion_proposal_read p c E rho hS hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
    (SA.proposalTime p.toParams q)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hui := healing_support_idxBefore_le p c E rho hS hj hu
  have hjD := (healing_phase_lt_timeIdx p c E rho hS hj (hqg.trans hgate)).le
  obtain ⟨hH, hc, _hr⟩ := hp.2.2.2 j x hui hjD hx
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, _hB, heB, hlo⟩ := healing_proposer_floor p c E rho hS q Q st hQ hst hne
  have he : B = Qfg.parent := eraseFG_injective (heB.trans
    (by rw [← eraseFG_parent, heq]))
  have hH' : st.fg.h_max = m := by rw [hfg]; exact hH
  have hc' : (FGSA.controls p st).contest = contested := by
    change (KitFG.treeStoreControlsView (heightView p) st.fg).contest = contested
    rw [hfg]
    exact hc
  change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _ at hlo
  rw [hH', hc', he] at hlo
  have hparent : FGBlock.Preceq Qfg.parent Qfg := by
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
  refine ⟨hlo.trans ((fgCertificateLaws p).height.h_mono hparent), ?_⟩
  obtain ⟨i, K, hi, hK, heK⟩ := healing_rise_one_gate_copy p c E rho hS hexact
    (hgate.trans hp.2.1) hx
    (healing_recovery_gate_reader hrec hx (hgst.trans hu) (hgate.trans hp.2.1))
  have hKe : K = Qfg := eraseFG_injective (heK.trans heq.symm)
  subst K
  have hui' := healing_support_idxBefore_le p c E rho hS hi (hu.trans hqg)
  have hiD := (healing_phase_lt_timeIdx p c E rho hS hi hgate).le
  have hcap := (hp.2.2.2 i x hui' hiD hx).1
  exact hcap ▸ healing_phase_height_le p c E rho hK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME the saved seed keeps its repair threshold. -/
theorem frontierSearch_seed_repair (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (repair : TRepair p c E rho)
    {G u : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G) (hgst : E.t_GST ≤ u)
    (hseed : FrontierSeedQualification p E u q) :
    ∃ l, SA.proposalTime p.toParams l < SA.proposalTime p.toParams q ∧
      ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v := by
  rcases (frontierSeedQualification_iff p E u q).mp hseed with
    ⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, hkb, hsync, hlt⟩
  · exact ⟨_, hlt, fun v hp =>
      ((repair G u v m J contested hgap hG hgst hp).1 β hβ hmin).1⟩
  · exact ⟨_, hlt, fun v hp =>
      ((repair G u v m J contested hgap hG hgst hp).2 b hb hmin hkb hsync).1⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 Blueprint 21 HG.3. DC: SAME save a complete seed at its actual gate. -/
theorem frontierSearch_save_seed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    {u D : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hp : PhaseInterval p c E rho u D m J contested)
    (hseed : FrontierSeedQualification p E u q)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (he : eraseFG Qfg = Q)
    (hh : (heightView p Qfg).h = m) (hs : ExactService p c E rho q Q)
    (hg : SA.gateTime p.toParams q ≤ D) :
    StrongServed p c E rho m (SA.gateTime p.toParams q) := by
  have hu := frontierSearch_seed_after E hseed
  have huq : u ≤ SA.gateTime p.toParams q := by
    change u ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  apply (strongServed_iff p c E rho m (SA.gateTime p.toParams q)).mpr
  refine ⟨u, J, contested, q, Q, Qfg, hgst, hQ, he, hh, hs, hseed, hu,
    frontierSearch_phase_cut E rho hp huq hg, le_rfl, hg.trans hp.2.1, ?_⟩
  intro i x hui hiq hx
  exact (hp.2.2.2 i x
    ((healing_phase_idx_le_time p c rho le_rfl).trans hui)
    (hiq.trans (frontierSearch_timeIdx_mono rho hg)) hx).1.le

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
 ROOT-DIGEST W2b. Blueprint 21 HG.3 contest; plan R2-b.
DC: SAME stop at the finite first event, or save the repaired height-m seed.
The horizon is closed. TRepair has producer healing_tRepair. -/
theorem frontier_hg3_contest [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) (monoAll : RMonoAll p
      c E rho)
    (heldServices : ∀ i (ev : V2.Event V (Obj p)) x W y,
      rho.events[i]? = some ev → x ∈ rho.honest → y ∈ rho.honest →
      E.t_GST ≤ ev.time → W ∈ (storeAt p c E rho (i + 1) x).fg.TF →
      ev.time + p.Δ ≤ rho.horizon →
      TargetReceiptService E rho (eraseFG W) (ev.time + p.Δ) y)
    (repair : TRepair p c E rho)
    {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .contest)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + (ρbar + 3 * p.Δ) ≤ rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time (ev.time + (ρbar + 3 * p.Δ)) := by
  apply (frontierHG3Result_iff p c E rho i m ev.time _).mpr
  have hsched := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hi, hgst0, _, hfront, hm, hkind⟩ :=
    (frontierSearchStart_iff p c E rho i ev m .contest).mp hstart
  have hρ : 0 ≤ ρbar := by
    have hG := (fgsa_gamma_bounds p G).1
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    cases mode with
    | two =>
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos]
    | one =>
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos]
  rcases frontierSearch_first_effective_split p c E rho hsched i
      (ev.time + (ρbar + 3 * p.Δ)) with hstop | hquiet
  · rcases frontierSearch_classify_stop p c E rho monoAll hfront hstop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨J, hp, _⟩ := healing_settle_start_on (hroots := hrec.base.receiptIdealization)
    p c E rho crossing hrec.base.valid monoAll heldServices i ev _ m .contest hi hgst0
    (by change ev.time + 3 * p.Δ ≤ ev.time + (ρbar + 3 * p.Δ); linarith)
    hhor hm hfront hkind hquiet
  have hgst : E.t_GST ≤ ev.time + 3 * p.Δ := by linarith [p.deltaPos]
  obtain ⟨q, Q, hseed, hgate, hQ, he⟩ := frontierSearch_repair_seed E rho repair
    hrec.gap hrec.gapPos hgst hp mode (by linarith)
  have hgateD : SA.gateTime p.toParams q ≤ ev.time + (ρbar + 3 * p.Δ) := by linarith
  obtain ⟨j, Qfg, _, _, hErase⟩ := healing_rise_one_gate_copy p c E rho hsched he
    (hgateD.trans hhor) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 (hgst.trans (frontierSearch_seed_after E
      hseed)) (hgateD.trans hhor))
  obtain ⟨hlo, hhi⟩ := frontierSearch_proposal_heights E rho hrec crossing hgst hp
    (frontierSearch_seed_after E hseed) hgateD hQ hErase he
  have hh : (heightView p Qfg).h = m := Nat.le_antisymm hhi hlo
  have hu := frontierSearch_seed_after E hseed
  have ht : ev.time ≤ SA.gateTime p.toParams q := by
    change ev.time ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  exact Or.inr (Or.inr ⟨_, ht, hgateD,
    frontierSearch_save_seed E rho hgst hp hseed hQ hErase hh he hgateD⟩)

end AvailableChain.FGSA.Run
end
