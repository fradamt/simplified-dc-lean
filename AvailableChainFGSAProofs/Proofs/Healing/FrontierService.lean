module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSeed
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceCover
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceGate
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceSupport
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierOpenAll
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersQ

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! HG.1 exact service (blueprint 21:1500–1583; plan §3.1 steps 6–7).
The q+1 read uses the initial phase. Later reads use the closed capped endpoint.
Both routes use capped gate geometry. INLINE writes: `fgsa_leaseOrigins_lastWrite`. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Bounded retained objects and read epochs used by one frontier service interval. -/
structure FrontierServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q : Slot) (v : Time) : Prop where
  read : recoveryStart p E ≤ SA.proposalTime p.toParams q →
    SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierReadScope E rho q v
  permanence : ∀ u t m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u t m J contested → t ≤ v →
    SupportPermanenceServices E rho u t m J contested
  heads : ∀ s ip x N, q + 1 ≤ s → SA.voteTime p.toParams s ≤ v →
    E.t_GST ≤ slotStartZ p ((s : Int) - 2) →
    x ∈ rho.honest → rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
    RepairHeadServices E rho s ip x N

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1551–1574; plan §3.1 step 6.
DC: INTENTIONAL the exact HEAD clause and capped gate geometry give all service fields. -/
theorem frontier_exactService_of_heads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} {B : Block} (hqs : q < s) (hgate : SA.gateTime p.toParams s ≤ v)
    (hp : HonestProposal E rho (fgsaInterface p c) s B)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some B) :
    ExactService p c E rho s B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith)).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  have hBs := repair_proposal_slot E rho hp
  have hne : B ≠ .genesis := by
    rintro rfl
    exact hp.1.1.ne' hBs.symm
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hGST.trans (hu.trans ?_)
    have hqsI : (q : Int) < (s : Int) := by exact_mod_cast hqs
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hRead := services.read (hready.trans hu) hqv hvh
  have hScope := frontier_repair_gate_scope E rho hRead hready hu hqs hgate
  have hhor : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans ?_ (hgate.trans hvh)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hheadAll : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some B :=
    fun y hy => hhead y hy
      (healing_recovery_joined E rho hrec hy hScope.cut hgsts hhor)
  exact repair_exact_service_on E rho hrec s B hne hScope.cut hgsts (fun _ => hhead)
    (fun _ _ hx ht => frontier_gate_geometry E rho hrec mono crossing writes hRead
      hready hErase hHeight hService hu hPhase hqv hvh hcap hqs hgate hBs hheadAll hx ht)
    (fun i x hReader ht => hScope.gates i x hReader.1 ht) hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1570–1574; TF-SEED Q4 step 4.
DC: INTENTIONAL an honest q+1 proposal has full service after d_q, under the cap.
The gate proof uses no phase through d_(q+1). -/
theorem frontier_seed_qSucc_exactService [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hseed : FrontierSeedQualification p E u q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  exact frontier_exactService_of_heads E rho hrec mono crossing writes services hready hErase
    hHeight
    hService hu hPhase hqv hvh hCap (Nat.lt_succ_self q) hgate hp
    (frontier_seed_qSucc_head E rho hrec mono crossing writes
      hready hPhase
      (services.permanence u (SA.gateTime p.toParams q) m J contested hready hPhase hqv)
      hseed
      (fun ip x N hx hip hem => services.heads (q + 1) ip x N le_rfl (by
        apply le_trans ?_ hgate
        change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤
          4 * p.Δ * ((q + 1 : Nat) : Int) + 6 * p.Δ
        linarith [p.deltaPos]) (by
        have he : ((q + 1 : Nat) : Int) - 2 = (q : Int) - 1 := by push_cast; omega
        simpa only [he] using frontier_seed_prior_cut hready hseed)
        hx hip hem) hp)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1500–1574; plan §3.1 step 6.
DC: INTENTIONAL the HG.1 retained-read chain gives exact HEADs for s ≥ q+2.
The strict consumer uses v+1 only as an integer bound; every read and gate is within v. -/
theorem frontier_later_head [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) s B) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hE := hrec.base.valid
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  subst B
  have hgsts : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ := by
    refine hGST.trans (hu.trans ?_)
    have htime := hafter
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at htime
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) - p.Δ
    linarith
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hqs : q + 1 ≤ s := by
    have ht := hafter
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at ht
    have hlt : q < s := by exact_mod_cast (show (q : Int) < (s : Int) by
      nlinarith [p.deltaPos])
    exact Nat.succ_le_of_lt hlt
  have hPriorCut : E.t_GST ≤ slotStartZ p ((s : Int) - 2) := by
    have hqsI : (q : Int) + 2 ≤ (s : Int) := by
      change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at hafter
      by_contra hn
      have hle : (s : Int) ≤ (q : Int) + 1 := by omega
      nlinarith [p.deltaPos]
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 2)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hRead := services.read (hready.trans hu) hqv hvh
  have hHeads := services.heads s ip x N hqs hvs hPriorCut hx hip hem
  have hinput := retainedHG1Input_through E rho hrec mono crossing writes hready hQ hErase
    hHeight hService hRead hu hPhase hqv hvh hCap hx hip hseat N hem hafter hgate
  have hreads := fgsa_retainedReads_HG1_joined (hroots := hrec.base.receiptIdealization)
    E rho hE s hx hip hseat N hem Qfg q (v + 1) hafter
    (lt_of_le_of_lt hgate (lt_add_of_pos_right v (show (0 : Int) < 1 by decide)))
    (fun y hy ih hih _ _ => hinput y hy ih hih)
    (hHeads.targets ip x N hx hip hem)
  have hgeom : RetainedExactHeadRunGeometryOn E rho ip x s Qfg N.erase :=
    fgsa_retainedExactHead_geometry_on_run_on E rho hE s hx hip hseat N hem Qfg hreads
      (hHeads.scopes ip x N hx hip hem) hrec.base.receiptIdealization
  exact exactService_head_of_retained_proposal_on E rho hE hDelta s hip N hem
    Qfg hgeom (hvs.trans hvh)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1500–1574; plan §3.1 step 6.
DC: INTENTIONAL full service for a later honest proposal whose gate is in the capped interval. -/
theorem frontier_later_exactService [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) s B) :
    ExactService p c E rho s B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hqs : q < s := by
    apply repair_slot_lt_of_time
    refine lt_of_lt_of_le ?_ hafter
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact frontier_exactService_of_heads E rho hrec mono crossing writes services hready hErase
    hHeight
    hService hu hPhase hqv hvh hCap hqs hgate hp
    (frontier_later_head E rho hrec mono crossing writes services hready hQ hErase hHeight hService
      hu hPhase hqv hvh hCap hafter hgate hp)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1333–1350, 1500–1574; plan §2.4 and §3.1.
DC: INTENTIONAL the first two frozen TFrontier conjuncts, under its seed hypotheses.
INLINE writes: `fgsa_leaseOrigins_lastWrite` (Foundations/Leases:392), supplied at Assembly.
The full opening conjunction is assembled by `frontier_service` below. -/
theorem frontier_service_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    : ∀ u v m J contested q Q Qfg,
  recoveryStart p E ≤ u → HonestProposal E rho (fgsaInterface p c) q Q → eraseFG Qfg = Q →
  (heightView p Qfg).h = m → ExactService p c E rho q Q →
  ((∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)) →
  u ≤ SA.proposalTime p.toParams q →
  PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested →
  SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
  (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
    (storeAt p c E rho i x).fg.h_max ≤ m) →
  Transfers p c E rho q Q v ∧ RepairAfter p c E rho q v := by
  intro u v m J contested q Q Qfg hgst hQ hErase hHeight hService hseed hu hPhase hqv hvh hCap
  have hSync : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hseed := (frontierSeedQualification_iff p E u q).mpr hseed
  have services := scopeProducer q v (hgst.trans hu) hqv hvh
  have hRead := services.read (hgst.trans hu) hqv hvh
  have hd := p.deltaPos
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith)).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x i H hx hi hiv hH
      exact frontier_Q_heads E rho hrec mono crossing writes hSync hErase hHeight hService
        (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hRead.seed hu hPhase hqv
          hvh hcap i hi hiv x hx H hH
    · intro i B hi hiv hp
      exact frontier_proposals_cover E rho hrec mono crossing writes hRead hgst
        hErase hHeight
        hService hu hPhase hqv hvh hcap hi hiv hp
    · intro i x hx hguard hai hiv
      exact frontier_output_cover E rho hrec mono crossing writes hRead
        (fun s hs ht => frontier_repair_gate_scope E rho hRead hgst hu
          (Nat.lt_of_succ_le hs) ht) hgst hErase hHeight
        hService hu hPhase hqv hvh hcap hguard hx hai hiv
  · intro s B htime hgate hp
    have hqs := repair_slot_lt_of_time htime
    by_cases heq : s = q + 1
    · subst s
      exact frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase
        hHeight hService hu hPhase hqv hvh hCap hseed hgate hp
    · have hqs2 : q + 2 ≤ s :=
        Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hqs) (Ne.symm heq))
      have hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s := by
        have hqsI : (q : Int) + 2 ≤ (s : Int) := by exact_mod_cast hqs2
        change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int)
        nlinarith
      exact frontier_later_exactService E rho hrec mono crossing writes services hgst hQ hErase
        hHeight hService hu hPhase hqv hvh hCap hafter hgate hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1333–1350, 1500–1583; plan §2.4 and §3.1 step 8.
DC: INTENTIONAL the seeded TFrontier, in its frozen order, through the closed cap.
INLINE writes: `fgsa_leaseOrigins_lastWrite`; INLINE rowCoverage:
`rowPermission_covered E rho hrec.base hrec.fault`, both supplied at Assembly.
Later opening service follows from the covering gate, without an honest proposal
at that label or a phase through that gate. -/
theorem frontier_service [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root)) :
    TFrontier p c E rho := by
  intro u v m J contested q Q Qfg hgst hQ hErase hHeight hService hseed hu hPhase hqv hvh hCap
  have hseedQ := (frontierSeedQualification_iff p E u q).mpr hseed
  have services := scopeProducer q v (hgst.trans hu) hqv hvh
  have hRead := services.read (hgst.trans hu) hqv hvh
  have hcore := frontier_service_core E rho hrec mono crossing scopeProducer writes u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService hseed hu hPhase hqv hvh hCap
  refine ⟨hcore.1, hcore.2, frontier_openings E rho hrec crossing rowCoverage
    u v m J contested q Q Qfg hgst hQ hErase hHeight hService hu hPhase hqv hvh hCap ?_⟩
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos])).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  intro r hqr hav
  apply frontierOpeningServed_intro E rho
  intro i x hx ht
  exact frontier_opening_gateService_of_cover E rho hrec mono crossing writes hRead hgst hQ
    hErase hHeight hService hu hPhase hqv hvh hcap hqr hav hx ht

end AvailableChain.FGSA.Run
end
